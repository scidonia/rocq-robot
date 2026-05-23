#!/usr/bin/env node

/**
 * MCP server for Coq/Rocq integration via coq-lsp/rocq-lsp
 */

import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
} from '@modelcontextprotocol/sdk/types.js';

import { RocqLspClient } from './lsp-client.js';
import { DocumentManager } from './document-manager.js';
import { detectProjectConfig, mergeProjectArgs, findProjectRoot } from './project-config.js';
import type {
  Position,
  Range,
  GoalAnswer,
  ProofInfo,
  RunResult,
  GoalConfig,
  RunOpts,
} from './types.js';
import * as fs from 'fs';
import { resolve as resolvePath } from 'path';

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function retryDocumentNotReady<T>(
  action: () => Promise<T>,
  opts?: { timeoutMs?: number; initialDelayMs?: number; maxDelayMs?: number }
): Promise<T> {
  const timeoutMs = opts?.timeoutMs ?? 30_000;
  let delayMs = opts?.initialDelayMs ?? 50;
  const maxDelayMs = opts?.maxDelayMs ?? 500;
  const start = Date.now();

  for (;;) {
    try {
      return await action();
    } catch (err) {
      const message = err instanceof Error ? err.message : String(err);
      const isNotReady = message.includes('Document is not ready');

      if (!isNotReady || Date.now() - start > timeoutMs) {
        throw err;
      }

      await sleep(delayMs);
      delayMs = Math.min(Math.floor(delayMs * 1.5), maxDelayMs);
    }
  }
}

// Parse command-line arguments for configuration
function parseArgs() {
  const args = process.argv.slice(2);
  const config: {
    rocqLspPath?: string;
    rocqLspArgs?: string[];
    workspaceRoot?: string;
  } = {};

  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--coq-lsp-path' && i + 1 < args.length) {
      config.rocqLspPath = args[++i];
    } else if (args[i] === '--workspace-root' && i + 1 < args.length) {
      config.workspaceRoot = args[++i];
    } else if (args[i] === '--coq-lsp-args' && i + 1 < args.length) {
      config.rocqLspArgs = args[++i].split(' ');
    }
  }

  if (config.workspaceRoot) {
    config.workspaceRoot = resolvePath(config.workspaceRoot);
  }

  return config;
}

async function main() {
  const config = parseArgs();

  // Determine workspace root
  const workspaceRoot = config.workspaceRoot || process.cwd();

  // Auto-detect project configuration (for logging/debugging purposes)
  // Note: coq-lsp will auto-detect _CoqProject/_RocqProject itself, but we log what we find
  // to help diagnose any issues with project configuration
  const projectConfig = detectProjectConfig(workspaceRoot);

  console.error('[mcp-coq-lsp] Workspace root:', workspaceRoot);
  console.error('[mcp-coq-lsp] Detected load paths:', projectConfig.loadPaths);
  
  if (projectConfig.loadPaths.length === 0) {
    console.error('[mcp-coq-lsp] WARNING: No _CoqProject/_RocqProject/dune config found!');
    console.error('[mcp-coq-lsp] coq-lsp may not be able to resolve imports correctly.');
  }

  // Base user-provided args
  const baseRocqLspArgs = config.rocqLspArgs || [];
  let finalRocqLspArgs = [...baseRocqLspArgs];

  console.error('[mcp-coq-lsp] coq-lsp args:', finalRocqLspArgs);

  /**
   * Compute coq-lsp CLI args for a given workspace root.
   * Maps the coq/ source directory (if it exists) to the root logical path
   * so that bare imports like `Require Import Wp` resolve correctly.
   */
  function computeRocqLspArgs(root: string): string[] {
    const args = [...baseRocqLspArgs];
    try {
      const srcDir = resolvePath(root, 'coq');
      if (fs.existsSync(srcDir)) {
        args.push('-R', `${srcDir},Imp`);
      }
    } catch {}
    return args;
  }

  // Initialize with initial workspace root
  finalRocqLspArgs = computeRocqLspArgs(workspaceRoot);

  // Track the active project root for dynamic workspace switching
  let activeWorkspaceRoot = workspaceRoot;

  // Speculative imports per file URI — persisted across tool calls
  const speculativeImports = new Map<string, string[]>();

  // File history per file path — used by coq_undo to restore previous versions
  const fileHistory = new Map<string, string[]>();
  const MAX_HISTORY = 50;

  function isSkipLine(line: string): boolean {
    const trimmed = line.trim();
    if (trimmed === '') return true;
    if (trimmed.startsWith('(*')) return true;
    if (trimmed === 'Proof.' || trimmed.startsWith('Proof. ')) {
      const after = trimmed.substring('Proof.'.length).trim();
      // Don't skip "Proof. Admitted." — that's the entire proof body
      if (after === 'Admitted.' || after === 'Qed.' || after === 'Defined.') return false;
      return true;
    }
    return false;
  }

  function autoAdvancePosition(text: string, pos: Position): Position {
    const lines = text.split('\n');
    let line = pos.line;
    // Phase 1: skip keyword/comment lines
    for (let i = 0; i < 20; i++) {
      if (line >= lines.length) break;
      if (!isSkipLine(lines[line])) break;
      line = line + 1;
    }
    if (line > lines.length) line = lines.length;
    return { line, character: 0 };
  }

  function isProofEndLine(line: string): boolean {
    const t = line.trim();
    return t === 'Qed.' || t === 'Admitted.' || t === 'Defined.';
  }

  function findProofLine(lines: string[], searchName: string): number {
    const s = searchName.trim();
    for (let i = 0; i < lines.length; i++) {
      const l = lines[i].trim();
      const kw = l.split(/\s+/)[0];
      if ((kw === 'Lemma' || kw === 'Theorem' || kw === 'Corollary' || kw === 'Example') &&
          l.includes(s + ' :')) {
        for (let j = i + 1; j < lines.length; j++) {
          const t = (lines[j] || '').trim();
          if (t === 'Proof.' || t.startsWith('Proof. ')) return j;
          if (isTopLevelLine(lines[j] || '') || isProofEndLine(lines[j] || '')) break;
        }
      }
    }
    return -1;
  }

  function isTopLevelLine(line: string): boolean {
    const t = line.trim();
    const kw = t.split(/\s+/)[0];
    return            kw === 'Lemma' || kw === 'Theorem' || kw === 'Definition' ||
           kw === 'Fixpoint' || kw === 'Inductive' || kw === 'CoFixpoint' ||
           kw === 'Corollary' || kw === 'Example' || kw === 'Remark' ||
           kw === 'Fact' || kw === 'Goal' || kw === 'Require' ||
           kw === 'Import' || kw === 'Export' || kw === 'From' ||
           kw === 'Notation' || kw === 'Ltac' || kw === 'Module' ||
           kw === 'End' || kw === 'Axiom' || kw === 'Parameter' ||
           kw === 'CoInductive';
  }

  function insertPosition(text: string, pos: Position): Position {
    const lines = text.split('\n');
    let line = pos.line;
    // Skip keyword/comment lines
    for (let i = 0; i < 20; i++) {
      if (line >= lines.length) break;
      if (!isSkipLine(lines[line])) break;
      line = line + 1;
    }
    // Skip past non-blank content but stop at proof-ending or toplevel keywords
    for (let i = 0; i < 200; i++) {
      if (line >= lines.length) break;
      const l = (lines[line] || '').trim();
      if (l === '') break;
      if (isProofEndLine(lines[line] || '')) break;
      if (isTopLevelLine(lines[line] || '')) break;
      line = line + 1;
    }
    if (line > lines.length) line = lines.length;
    return { line, character: 0 };
  }

  /** Clamp a position to be within [0, lines.length-1] — never past EOF. */
  function safePos(pos: Position, text: string): Position {
    const maxLine = Math.max(0, text.split('\n').length - 1);
    return { line: Math.min(pos.line, maxLine), character: 0 };
  }

  function pushFileHistory(path: string, text: string) {
    if (!fileHistory.has(path)) fileHistory.set(path, []);
    const stack = fileHistory.get(path)!;
    stack.push(text);
    if (stack.length > MAX_HISTORY) stack.shift();
    fileHistory.set(path, stack);
  }

  /**
   * Open a document, first detecting and switching to its project root if needed.
   * This allows files from different Coq projects to be opened without restarting
   * the MCP server.
   */
  async function ensureDocumentOpened(path: string) {
    const absPath = resolvePath(path);
    const projectRoot = findProjectRoot(absPath);

    if (projectRoot && resolvePath(projectRoot) !== resolvePath(activeWorkspaceRoot)) {
      console.error('[mcp-coq-lsp] Switching workspace root:',
        activeWorkspaceRoot, '->', projectRoot);

      activeWorkspaceRoot = projectRoot;
      docManager.clear();
      speculativeImports.clear();
      fileHistory.clear();

      // Do NOT await the full restart — fire it and let the caller retry.
      // The MCP client has a tighter timeout than the LSP cold-start needs.
      lspClient.restart({
        workspaceRoot: projectRoot,
        rocqLspArgs: computeRocqLspArgs(projectRoot),
      }).then(() => {
        console.error('[mcp-coq-lsp] Workspace switch complete');
      }).catch(err => {
        console.error('[mcp-coq-lsp] Workspace switch failed:', err);
      });

      const e = new Error('Switching workspace to ' + projectRoot + ' — please retry');
      (e as any).retryAfter = 5000;
      throw e;
    }

    try {
      const doc = await docManager.openDocument(path);
      const freshText = await fs.promises.readFile(absPath, 'utf-8');
      if (freshText !== doc.text) {
        return await docManager.updateDocument(path, freshText);
      }
      return doc;
    } catch (err: any) {
      if (err?.message === 'LSP client not started') {
        // LSP isn't running — try to start it
        lspClient.restart({
          workspaceRoot: activeWorkspaceRoot,
          rocqLspArgs: computeRocqLspArgs(activeWorkspaceRoot),
        }).then(() => {
          console.error('[mcp-coq-lsp] Auto-restart complete');
        }).catch(err => {
          console.error('[mcp-coq-lsp] Auto-restart failed:', err);
        });
        const e = new Error('LSP client not started — please retry');
        (e as any).retryAfter = 5000;
        throw e;
      }
      throw err;
    }
  }

  // Create LSP client and document manager
  const lspClient = new RocqLspClient({
    rocqLspPath: config.rocqLspPath,
    rocqLspArgs: finalRocqLspArgs,
    workspaceRoot: workspaceRoot,
    checkOnlyOnRequest: false,
    ppType: 0, // String output
    goalAfterTactic: true,
  });

  const docManager = new DocumentManager(
    lspClient,
    workspaceRoot
  );

  // Start LSP client
  await lspClient.start();

  // Create MCP server
  const server = new Server(
    {
      name: 'mcp-coq-lsp',
      version: '0.1.0',
    },
    {
      capabilities: {
        tools: {},
      },
    }
  );

  // Tool: coq_open_goals
  server.setRequestHandler(ListToolsRequestSchema, async () => {
    return {
      tools: [
        {
          name: 'coq_open_goals',
          description:
            'Get current open goals for a proof in a Coq/Rocq file. ' +
            'Uses Prev mode by default. Takes a proof name.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string', description: 'Path to the .v file' },
              name: { type: 'string', description: 'Proof name (e.g. "preservation")' },
              pp_format: { type: 'string', enum: ['Str', 'Pp'], description: 'Pretty-printing format (default: Str)' },
              compact: { type: 'boolean', description: 'Use compact hypothesis display' },
              mode: { type: 'string', enum: ['Prev', 'After'], description: 'Goal position mode (default: Prev)' },
            },
            required: ['file', 'name'],
          },
        },
        {
          name: 'coq_proof_state',
          description:
            'Get richer proof context including proof name and statements',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string' },
              position: {
                type: 'object',
                properties: {
                  line: { type: 'number' },
                  character: { type: 'number' },
                },
                required: ['line', 'character'],
              },
            },
            required: ['file', 'position'],
          },
        },
        {
          name: 'coq_get_state_at_pos',
          description:
            'Get an opaque state identifier from a file position (Pétanque)',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string' },
              position: {
                type: 'object',
                properties: {
                  line: { type: 'number' },
                  character: { type: 'number' },
                },
                required: ['line', 'character'],
              },
              memo: { type: 'boolean', description: 'Enable memoization' },
              hash: { type: 'boolean', description: 'Compute state hash' },
            },
            required: ['file', 'position'],
          },
        },
        {
          name: 'coq_run_tactic',
          description:
            'Run a tactic/command against a state (speculative execution)',
          inputSchema: {
            type: 'object',
            properties: {
              state_id: { type: 'number', description: 'State identifier' },
              tactic: { type: 'string', description: 'Tactic or command text' },
              memo: { type: 'boolean' },
              hash: { type: 'boolean' },
            },
            required: ['state_id', 'tactic'],
          },
        },
        {
          name: 'coq_goals_for_state',
          description: 'Get goals for a given state identifier',
          inputSchema: {
            type: 'object',
            properties: {
              state_id: { type: 'number' },
              compact: { type: 'boolean' },
            },
            required: ['state_id'],
          },
        },
        {
          name: 'coq_apply_edit',
          description: 'Apply text edits to a file and re-sync with rocq-lsp. Use "find"/"replace" for simple text search-and-replace instead of computing line numbers.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string' },
              find: { type: 'string', description: 'Text to search for (use instead of edits for simple replacements)' },
              replace: { type: 'string', description: 'Replacement text (use with find)' },
              edits: {
                type: 'array',
                items: {
                  type: 'object',
                  properties: {
                    range: {
                      type: 'object',
                      properties: {
                        start: {
                          type: 'object',
                          properties: {
                            line: { type: 'number' },
                            character: { type: 'number' },
                          },
                          required: ['line', 'character'],
                        },
                        end: {
                          type: 'object',
                          properties: {
                            line: { type: 'number' },
                            character: { type: 'number' },
                          },
                          required: ['line', 'character'],
                        },
                      },
                      required: ['start', 'end'],
                    },
                    newText: { type: 'string' },
                  },
                  required: ['range', 'newText'],
                },
              },
            },
            required: ['file'],
          },
        },
        {
          name: 'coq_insert_tactic',
          description:
            'Insert a tactic into a proof and return updated goals. ' +
            'Auto-prepends bullet prefix (-, +, *) when proof state requires it. ' +
            'Prefer explicit "as" clauses with induction/destruct for robust proofs.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string' },
              name: { type: 'string', description: 'Proof name (e.g. "preservation")' },
              tactic: { type: 'string' },
              follow_with_goals: {
                type: 'boolean',
                description: 'Query goals after inserting',
              },
            },
            required: ['file', 'name', 'tactic'],
          },
        },
        {
          name: 'coq_search',
          description:
            'Search the Coq environment for lemmas and theorems. Simple names auto-quote (e.g. "plus_n_O"). ' +
            'Use parentheses for patterns: "(_ + 0 = _)" or just "_ + 0 = _". ' +
            'Runs speculatively, no file changes.',
          inputSchema: {
            type: 'object',
            properties: {
              file: {
                type: 'string',
                description: 'Path to a .v file (used to obtain a proof state)',
              },
              pattern: {
                type: 'string',
                description: 'Search pattern for lemmas/theorems',
              },
            },
            required: ['file', 'pattern'],
          },
        },
        {
          name: 'coq_check_term',
          description:
            'Check the type of a term speculatively. Runs `Check <term>.` and returns the result.',
          inputSchema: {
            type: 'object',
            properties: {
              file: {
                type: 'string',
                description: 'Path to a .v file (used to obtain a proof state)',
              },
              term: {
                type: 'string',
                description: 'Term to check the type of',
              },
            },
            required: ['file', 'term'],
          },
        },
        {
          name: 'coq_about',
          description:
            'Get information about a term/definition speculatively. Runs `About <term>.` and returns the result.',
          inputSchema: {
            type: 'object',
            properties: {
              file: {
                type: 'string',
                description: 'Path to a .v file (used to obtain a proof state)',
              },
              term: {
                type: 'string',
                description: 'Term to get information about',
              },
            },
            required: ['file', 'term'],
          },
        },
        {
          name: 'coq_undo',
          description:
            'Restore the file to before the last N edit operations (coq_insert_tactic or coq_apply_edit). Uses operation history, not span counting.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string' },
              n: {
                type: 'number',
                description: 'Number of file versions to undo (default: 1)',
              },
            },
            required: ['file'],
          },
        },
        {
           name: 'coq_try_tactic',
          description:
            'Single-call speculative tactic execution: get state, run tactic, and return updated goals. ' +
            'Position is optional — uses "name" or cursor. Does not modify the file.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string' },
              name: { type: 'string', description: 'Proof name' },
              tactic: { type: 'string', description: 'Tactic to run speculatively' },
              compact: { type: 'boolean', description: 'Use compact hypothesis display' },
            },
            required: ['file', 'name', 'tactic'],
          },
        },
        {
          name: 'coq_check',
          description: 'Force document checking and return completion status',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string' },
            },
            required: ['file'],
          },
        },
        {
          name: 'coq_check_range',
          description: 'Check a specific line range in a Coq file and return diagnostics',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string', description: 'Path to the .v file' },
              range: {
                type: 'object',
                properties: {
                  start: {
                    type: 'object',
                    properties: {
                      line: { type: 'number' },
                      character: { type: 'number' },
                    },
                    required: ['line'],
                  },
                  end: {
                    type: 'object',
                    properties: {
                      line: { type: 'number' },
                      character: { type: 'number' },
                    },
                    required: ['line'],
                  },
                },
                required: ['start', 'end'],
                description: 'Line range to check (0-based)',
              },
            },
            required: ['file', 'range'],
          },
        },
        {
          name: 'coq_require',
          description:
            'Require a library speculatively. Runs `Require Import <lib>.` against the file environment. ' +
            'Subsequent speculative queries on the same file will see the library. Does not modify the file.',
          inputSchema: {
            type: 'object',
            properties: {
              file: {
                type: 'string',
                description: 'Path to a .v file (provides the import environment)',
              },
              lib: {
                type: 'string',
                description: 'Library/module name to import (e.g. "Arith", "Coq.Lists.List")',
              },
            },
            required: ['file', 'lib'],
          },
        },
        {
          name: 'coq_locate',
          description:
            'Find where a library, module, or term is defined. Runs `Locate <thing>.` speculatively. ' +
            'Useful before Require to check if a module exists.',
          inputSchema: {
            type: 'object',
            properties: {
              file: {
                type: 'string',
                description: 'Path to a .v file (used to obtain a proof state)',
              },
              thing: {
                type: 'string',
                description: 'Name to locate (e.g. "Nat", "Coq.Lists.List", "plus_n_O")',
              },
            },
            required: ['file', 'thing'],
          },
        },
        {
          name: 'coq_focus',
          description:
            'Get full proof tree: current goals, bullet stack depth/levels, ' +
            'and the proof script up to the given position. ' +
            'Sets the file cursor — subsequent coq_insert_tactic/coq_try_tactic calls ' +
            'use this cursor automatically. Auto-removes empty Admitted stubs. ' +
            'Accepts proof name (e.g. "has_type_weaken") or explicit position.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string', description: 'Path to a .v file' },
              position: {
                type: 'object',
                properties: { line: { type: 'number' }, character: { type: 'number' } },
                required: ['line', 'character'],
              },
              name: { type: 'string', description: 'Proof name (alternative to position)' },
            },
            required: ['file'],
          },
        },
        {
          name: 'coq_reset_proof',
          description:
            'Wipe the proof body (from Proof. to Qed./Admitted.) and replace with fresh Admitted. ' +
            'Use this to start over on a broken proof.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string', description: 'Path to a .v file' },
              name: { type: 'string', description: 'Proof name (e.g. "has_type_weaken")' },
            },
            required: ['file', 'name'],
          },
        },
        {
          name: 'coq_add_lemma',
          description:
            'Insert a lemma stub (Lemma name : statement. Proof. Admitted.) ' +
            'above a specified proof. Use "before" to name which proof it goes above. ' +
            'Cursor moves to the new proof.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string', description: 'Path to a .v file' },
              name: { type: 'string', description: 'Lemma name (e.g. "my_helper")' },
              statement: { type: 'string', description: 'The lemma statement after the colon' },
              before: { type: 'string', description: 'Proof name to insert above (e.g. "preservation")' },
            },
            required: ['file', 'name', 'statement'],
          },
        },
      ],
    };
  });

  // Tool handler
  server.setRequestHandler(CallToolRequestSchema, async (request) => {
    const { name, arguments: args } = request.params;

    function formatSemi(data: unknown, indent = 0): string {
      const pad = '  '.repeat(indent);
      if (data === null || data === undefined) return pad + 'null';
      if (typeof data === 'string') return data;
      if (typeof data === 'number' || typeof data === 'boolean') return pad + String(data);
      if (Array.isArray(data)) {
        if (data.length === 0) return '[]';
        const allSimple = data.every(v => typeof v !== 'object' || v === null);
        if (allSimple) return data.map((v, i) => `[${i}]: ${formatSemi(v, 0)}`).join(', ');
        return data.map((v, i) => `[${i}]:\n${formatSemi(v, indent + 1)}`).join('\n');
      }
      if (typeof data === 'object') {
        const entries = Object.entries(data as Record<string, unknown>);
        if (entries.length === 0) return '{}';
        return entries.map(([k, v]) => {
          if (v === null || v === undefined) return pad + k + ': null';
          if (typeof v === 'object') return pad + k + ':\n' + formatSemi(v, indent + 1);
          return pad + `${k}: ${formatSemi(v, 0)}`;
        }).join('\n');
      }
      return pad + String(data);
    }

    function reply(summary: string, data: unknown) {
      const d = data as Record<string, unknown>;
      const parts: string[] = [summary];
      if (d?.goals) {
        const goalsWrapped = Array.isArray(d.goals) ? { goals: d.goals } : d.goals;
        const gl = (goalsWrapped as any)?.goals || [];
        if (gl.length > 0) {
          parts.push('');
          parts.push(formatGoals(goalsWrapped));
        }
      }
      if (Array.isArray(d?.feedback) && d.feedback.length > 0) parts.push(formatFeedback(d.feedback));
      const text = parts.join('\n');
      return {
        content: [
          { type: 'text' as const, text },
        ],
      };
    }

    function err(summary: string, detail?: string) {
      return {
        content: [
          { type: 'text' as const, text: detail ?? summary },
          { type: 'text' as const, text: summary },
        ],
        isError: true,
      };
    }

    /**
     * Run all pending speculative imports for a document URI on a given state.
     * Returns the final state after all imports.
     */
    async function runPendingImports(uri: string, stateId: number): Promise<number> {
      const pending = speculativeImports.get(uri);
      if (!pending || pending.length === 0) return stateId;
      let st = stateId;
      for (const lib of pending) {
        const r = await lspClient.sendRequest<RunResult<number>>(
          'petanque/run',
          { st, tac: `Require Import ${lib}.`, opts: { memo: true, hash: true } }
        );
        st = r.st;
      }
      return st;
    }

    function formatGoals(goals: any): string {
      const gl = goals?.goals || [];
      if (gl.length === 0) {
        const prog = goals?.program?.length || 0;
        const msgs = (goals?.messages || []).filter((m: any) => m.level === 1).map((m: any) => m.text).join('; ');
        return 'no goals' + (prog ? ` (${prog} program items)` : '') + (msgs ? '\n  messages: ' + msgs : '');
      }
      return gl.map((g: any, i: number) => {
        const total = gl.length;
        const idx = `Goal [${i + 1} of ${total}]: `;
        const hyps = (g.hyps || []).map((h: any) => {
          const name = h.names ? h.names.join(', ') : (h.name || '?');
          return `  ${name}: ${h.ty || h.type}`;
        }).join('\n');
        const ty = (g.ty || '').replace(/\s+/g, ' ');
        return (idx ? idx.trim() + '\n' : '') + (hyps ? hyps + '\n' : '') + '  ════════════════════════════════════\n  ' + ty;
      }).join('\n\n');
    }

    function compactGoalSummary(goals: any): string {
      const gl = goals?.goals || [];
      if (gl.length === 0) return '';
      if (gl.length === 1 && gl[0]) {
        const g = gl[0];
        const hnames = (g.hyps || []).map((h: any) => h.names ? h.names.join(',') : (h.name || '?')).join('; ');
        const parts: string[] = [];
        if (hnames) parts.push(`hyps: ${hnames}`);
        const oneline = (g.ty || '').replace(/\s+/g, ' ');
        const short = oneline.length > 70 ? oneline.slice(0, 67) + '…' : oneline;
        if (short) parts.push(`⊢ ${short}`);
        return parts.join(' | ');
      }
      return `${gl.length} goals`;
    }

    function nextHint(gc: any): string {
      const goals = gc?.goals || [];
      const stack = gc?.stack || [];
      const bullet = gc?.bullet;

      const bgGoals = stack.reduce(
        (s: number, [b, a]: any[]) => s + (b?.length || 0) + (a?.length || 0), 0
      );
      const total = goals.length + bgGoals;

      if (total === 0) {
        return 'Proof complete. You may close with Qed. or leave as Admitted.';
      }
      if (goals.length === 0 && bgGoals > 0) return `Bullet closed. ${bgGoals} goal(s) in background. Insert next bullet.`;
      if (goals.length === 1) {
        if (bgGoals > 0) return `Bullet open [${bullet || '-'}]. 1 goal at focus, ${bgGoals} in background.`;
        return '1 goal. Insert a tactic.';
      }
      const summary = compactGoalSummary(gc);
      if (bgGoals > 0) return `Bullet open [${bullet || '-'}]. ${goals.length} goals at focus, ${bgGoals} in background. ${summary}`;
      return `${goals.length} goals at focus. ${summary}${bullet ? ' [bullet ' + bullet + ']' : ''}`;
    }

    function formatFeedback(fb: Array<[number, string]>): string {
      return fb.map(([lvl, msg]) => {
        const tag = lvl === 1 ? 'ERR' : lvl === 3 ? 'WARN' : lvl === 4 ? 'INFO' : 'DBG';
        return `  [${tag}] ${msg}`;
      }).join('\n');
    }

    function fileLine(file: string, line: number): string {
      const base = file.split('/').pop() || file;
      return `${base}:${line + 1}`;
    }

    try {
      switch (name) {
        case 'coq_open_goals': {
          const { file, name, pp_format, compact, mode } = args as {
            file: string;
            name: string;
            pp_format?: string;
            compact?: boolean;
            mode?: string;
          };

          let position: Position;
          if (name) {
            const doc = await ensureDocumentOpened(file);
            const docLines = doc.text.split('\n');
            const proofLine = findProofLine(docLines, name);
            if (proofLine < 0) throw new Error(`Proof not found: "${name}"`);
            position = autoAdvancePosition(doc.text, { line: proofLine, character: 0 });
          } else {
            throw new Error('name is required for coq_open_goals');
          }

          // Ensure document is open
          const doc = await ensureDocumentOpened(file);

          // Send proof/goals request
          const result = await retryDocumentNotReady(() =>
            lspClient.sendRequest<GoalAnswer<string>>('proof/goals', {
              textDocument: {
                uri: doc.uri,
                version: doc.version,
              },
              position,
              pp_format: pp_format || 'Str',
              compact: compact ?? true,
              mode: mode || 'Prev',
            })
          );

          if (result.error) {
            return reply(`${fileLine(file, position.line)} — error: ${result.error}`, result);
          }
          const ngoals = (result.goals?.goals || []).length;
          return reply(`${fileLine(file, position.line)} — ${ngoals} goal(s)`, result);
        }

        case 'coq_proof_state': {
          const { file, position } = args as {
            file: string;
            position: Position;
          };

          // Get goals
          const doc = await ensureDocumentOpened(file);
          const goalsResult = await retryDocumentNotReady(() =>
            lspClient.sendRequest<GoalAnswer<string>>('proof/goals', {
              textDocument: { uri: doc.uri, version: doc.version },
              position,
              pp_format: 'Str',
            })
          );

          // Get proof info
          let proofInfo: ProofInfo | null = null;
          try {
            proofInfo = await lspClient.sendRequest<ProofInfo>(
              'petanque/proof_info_at_pos',
              {
                uri: doc.uri,
                position,
              }
            );
          } catch {
            // Proof info may not be available
          }

          const pname = proofInfo?.name || 'unknown';
          const ngoals = goalsResult.goals?.goals?.length || 0;
          return reply(
            `${fileLine(file, position.line)} — proof ${pname}, ${ngoals} goal(s)`,
            { proof: proofInfo, goals: goalsResult.goals, messages: goalsResult.messages, error: goalsResult.error }
          );
        }

        case 'coq_focus': {
          const { file, name } = args as {
            file: string;
            name: string;
          };

          const doc = await ensureDocumentOpened(file);
          const docLines = doc.text.split('\n');

          const pLine = findProofLine(docLines, name);
          if (pLine < 0) throw new Error(`Proof not found: "${name}"`);
          const position = { line: pLine, character: 0 };

          const lastPoint = insertPosition(doc.text, position);
          const goalsResult = await retryDocumentNotReady(() =>
            lspClient.sendRequest<GoalAnswer<string>>('proof/goals', {
              textDocument: { uri: doc.uri, version: doc.version },
              position: lastPoint,
              pp_format: 'Str',
              mode: 'Prev',
            })
          );

          // Extract proof script from file content (no LSP query)
          let scriptLines: string[] = [];
          const allLines = doc.text.split('\n');
          const scriptEnd = insertPosition(doc.text, position);
          scriptLines = allLines.slice(position.line, scriptEnd.line);

          const gc = goalsResult.goals;
          const goals = gc?.goals || [];
          const stack = gc?.stack || [];
          const bullet = gc?.bullet;
          const shelf = gc?.shelf || [];
          const givenUp = gc?.given_up || [];

          // Format proof tree as text
          const parts: string[] = [];
          parts.push(`${fileLine(file, position.line)}`);

          // Bullet level
          if (bullet) parts.push(`  bullet: ${bullet}`);
          parts.push(`  goals: ${goals.length} at focus`);

          // Stack levels
          if (stack.length > 0) {
            parts.push(`  stack depth: ${stack.length}`);
            for (let i = 0; i < stack.length; i++) {
              const [before, after] = stack[i];
              parts.push(`    level ${i + 1}: ${before.length} before, ${after.length} after`);
            }
          }

          // Shelved / given-up
          if (shelf.length > 0) parts.push(`  shelved: ${shelf.length}`);
          if (givenUp.length > 0) parts.push(`  given-up: ${givenUp.length}`);

          // Formatted goals
          if (goals.length > 0) {
            const goalText = formatGoals(gc);
            parts.push('');
            parts.push(goalText);
          } else {
            parts.push('  (no goals at focus)');
          }

          // Proof script
          if (scriptLines.length > 0) {
            parts.push('');
            parts.push('-- proof script ----------');
            scriptLines.forEach(l => parts.push(`  ${l}`));
          }

          const hint = nextHint(gc);
          parts.push('');
          parts.push(`next: ${hint}`);

          return reply(parts.join('\n'), {
            bullet,
            goals_at_focus: goals.length,
            stack_depth: stack.length,
            stack: stack.map(([before, after]: any) => ({
              before: before.length,
              after: after.length,
            })),
            shelved: shelf.length,
            given_up: givenUp.length,
            script: scriptLines,
            auto_removed: false,
            next: hint,
            error: goalsResult.error || null,
          });
        }

        case 'coq_get_state_at_pos': {
          const { file, position, memo, hash } = args as {
            file: string;
            position: Position;
            memo?: boolean;
            hash?: boolean;
          };

          const doc = await ensureDocumentOpened(file);

          const result = await lspClient.sendRequest<RunResult<number>>(
            'petanque/get_state_at_pos',
            {
              uri: doc.uri,
              position,
              opts: {
                memo: memo ?? true,
                hash: hash ?? true,
              },
            }
          );

          return reply(
            `${fileLine(file, position.line)} — state_id=${result.st}`,
            result
          );
        }

        case 'coq_run_tactic': {
          const { state_id, tactic, memo, hash } = args as {
            state_id: number;
            tactic: string;
            memo?: boolean;
            hash?: boolean;
          };

          const result = await lspClient.sendRequest<RunResult<number>>(
            'petanque/run',
            {
              st: state_id,
              tac: tactic,
              opts: { memo: memo ?? true, hash: hash ?? true },
            }
          );

          const nFeedback = (result.feedback || []).length;
          return reply(
            `run state=${state_id} "${tactic}" → st=${result.st}, proof_finished=${!!result.proof_finished}, feedback=${nFeedback}`,
            { state_id: result.st, proof_finished: result.proof_finished, feedback: result.feedback }
          );
        }

        case 'coq_goals_for_state': {
          const { state_id, compact } = args as {
            state_id: number;
            compact?: boolean;
          };

          const result = await lspClient.sendRequest<GoalConfig<string>>(
            'petanque/goals',
            {
              st: state_id,
              opts: { compact: compact ?? true },
            }
          );

          return reply(
            `goals for state_id=${state_id}: ${result.goals?.length || 0} goal(s)`,
            result
          );
        }

        case 'coq_apply_edit': {
          const { file, edits, find, replace } = args as {
            file: string;
            edits?: Array<{ range: Range; newText: string }>;
            find?: string;
            replace?: string;
          };

          // Get current document
          let doc = docManager.getDocument(file);
          if (!doc) {
            doc = await ensureDocumentOpened(file);
          }

          // Resolve edits: either from explicit ranges or from text search
          let resolvedEdits: Array<{ range: Range; newText: string }>;
          if (find !== undefined) {
            const idx = doc.text.indexOf(find);
            if (idx === -1) {
              return reply(`text not found: "${find.substring(0, 80)}"`, { found: false });
            }
            const before = doc.text.substring(0, idx);
            const beforeLines = before.split('\n');
            const findLines = find.split('\n');
            const startLine = beforeLines.length - 1;
            const startChar = beforeLines[beforeLines.length - 1].length;
            const endLine = startLine + (findLines.length - 1);
            const endChar = findLines.length === 1
              ? startChar + find.length
              : findLines[findLines.length - 1].length;
            resolvedEdits = [{
              range: {
                start: { line: startLine, character: startChar },
                end: { line: endLine, character: endChar },
              },
              newText: replace ?? '',
            }];
          } else {
            resolvedEdits = edits || [];
          }

          // Apply edits
          pushFileHistory(file, doc.text);
          const newText = docManager.applyEdits(doc.text, resolvedEdits);

          // Update and save
          await docManager.updateDocument(file, newText);
          await docManager.saveDocument(file);

          const updatedDoc = docManager.getDocument(file)!;

          const summary = find !== undefined
            ? `replaced "${find.substring(0, 40)}${find.length > 40 ? '…' : ''}"`
            : `applied ${resolvedEdits.length} edit(s)`;
          return reply(
            `${fileLine(file, 0)} — ${summary}, v${updatedDoc.version}`,
            { file, new_version: updatedDoc.version, found: true }
          );
        }

        case 'coq_insert_tactic': {
          const rawPos = (args as any).position as Position | undefined;
          const { file, name, tactic: rawTactic, follow_with_goals } = args as {
            file: string;
            name: string;
            tactic: string;
            follow_with_goals?: boolean;
          };

          await ensureDocumentOpened(file);
          const doc = docManager.getDocument(file)!;

          // Resolve position from name
          const docLines = doc.text.split('\n');
          const proofLine = findProofLine(docLines, name);
          if (proofLine < 0) throw new Error(`Proof not found: "${name}"`);
          const position = { line: proofLine, character: 0 };

          // Advance past Proof. and blank lines to the actual insert point
          let insPos = insertPosition(doc.text, position);

          // Handle "Proof. Admitted." on one line: split so tactic goes between them
          // and Admitted. is preserved at the end
          let oneLineSplit = false;
          if (insPos.line > 0) {
            const prev = (docLines[insPos.line - 1] || '').trim();
            if (prev.startsWith('Proof.') && prev !== 'Proof.' &&
                (prev.includes('Admitted.') || prev.includes('Qed.') || prev.includes('Defined.'))) {
              oneLineSplit = true;
              insPos = { line: insPos.line - 1, character: 0 };
            }
          }

          // Auto-bullet: query proof state to determine if bullet prefix is needed
          let tactic = rawTactic.trim();
          try {
            const stateResult = await retryDocumentNotReady(() =>
              lspClient.sendRequest<GoalAnswer<string>>('proof/goals', {
                textDocument: { uri: doc.uri, version: doc.version },
                position: insPos,
                pp_format: 'Str',
                mode: 'Prev',
              })
            );
            const bgCount = (stateResult.goals?.stack || []).reduce(
              (s: number, [b, a]: any[]) => s + (b?.length || 0) + (a?.length || 0), 0
            );
            const totalRemaining = (stateResult.goals?.goals?.length || 0) + bgCount;
            const rawBullet = stateResult.goals?.bullet || (totalRemaining > 1 ? '-' : undefined);
            const bulletMatch = rawBullet?.match(/[-+*]+/);
            const bullet = bulletMatch ? bulletMatch[0] : (rawBullet === '-' || rawBullet === '+' || rawBullet === '*' ? rawBullet : undefined);
            const firstWord = tactic.split(/\s+/)[0];
            const hasBullet = /^[-+*]+$/.test(firstWord) || firstWord === '{';

            // Compute indent from stack depth (only for line-start insertions).
            // Use stackDepth directly — the bullet prefix itself adds one level of nesting.
            const atLineStart = insPos.character === 0;
            const hasActiveBullet = !!stateResult.goals?.bullet;
            const stackDepth = hasActiveBullet ? (stateResult.goals?.stack || []).length : 0;
            const indent = atLineStart ? '  '.repeat(stackDepth) : '';

            if (bullet && !hasBullet && tactic !== 'Qed.' && tactic !== 'Defined.' && tactic !== 'Admitted.') {
              tactic = `${indent}${bullet} ${tactic}`;
            } else if (atLineStart) {
              tactic = `${indent}${tactic}`;
            }
          } catch {
            // state query is best-effort for bullets
          }

          // Speculative check: run tactic via Pétanque before editing the file.
          // If it fails, report the Coq error without modifying the file.
          let speculativeError: string | null = null;
          try {
            const stateResult = await retryDocumentNotReady(() =>
              lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                uri: doc.uri,
                position: insPos,
                opts: { memo: true, hash: true },
              })
            );
            await lspClient.sendRequest<RunResult<number>>('petanque/run', {
              st: stateResult.st,
              tac: tactic,
              opts: { memo: true, hash: true },
            });
          } catch (e: any) {
            const msg = e?.message || String(e);
            if (msg.includes('illegal begin of vernac') ||
                msg.includes('No proof-editing in progress') ||
                msg.includes('proof-editing') ||
                (tactic === 'Qed.' || tactic === 'Defined.' || tactic === 'Admitted.')) {
              // allow this error (e.g., Qed. or other vernac-level proof closers)
              // fall through to normal insertion
            } else {
              speculativeError = msg;
            }
          }

          if (speculativeError) {
            return reply(
              `${fileLine(file, proofLine)} — error: "${tactic}" — ${speculativeError}`,
              { applied: false, error: speculativeError }
            );
          }

          // Insert tactic at insert point
          let insertText: string;
          let editEnd: Position;
          if (oneLineSplit) {
            insertText = `Proof.\n${tactic}\nAdmitted.\n`;
            editEnd = { line: insPos.line + 1, character: 0 };
          } else {
            insertText = tactic.endsWith('\n') ? `${tactic}\n` : `${tactic}\n`;
            const curLine = (docLines[insPos.line] || '').trim();
            editEnd = (tactic === 'Qed.' && (curLine === 'Admitted.' || curLine === 'Qed.' || curLine === 'Defined.'))
              ? { line: insPos.line, character: (docLines[insPos.line] || '').length }
              : insPos;
          }
          const insertLines = insertText.split('\n');
          const contentLines = insertLines.slice(0, -1); // exclude trailing empty from \n
          const lastIdx = contentLines.length - 1;
          const insertedLinesCount = contentLines.length;
          const insertedUntil: Position = {
            line: insPos.line + insertedLinesCount,
            character: 0,
          };
          const nextTacticPosition: Position = {
            line: insPos.line + lastIdx,
            character: lastIdx === 0
              ? (insPos.character || 0) + contentLines[0].length
              : contentLines[lastIdx].length,
          };
          pushFileHistory(file, doc.text);
          const preEditVersion = doc.version;
          const preEditText = doc.text;

          const newText = docManager.applyEdits(doc.text, [
            {
              range: {
                start: insPos,
                end: editEnd,
              },
              newText: insertText,
            },
          ]);

          await docManager.updateDocument(file, newText);
          await docManager.saveDocument(file);

          let goals = null;
          if (follow_with_goals ?? true) {
            try {
              const updatedDoc = docManager.getDocument(file)!;
              const goalsQueryPos = safePos(nextTacticPosition, updatedDoc.text);
              const goalsResult = await retryDocumentNotReady(() =>
                lspClient.sendRequest<GoalAnswer<string>>('proof/goals', {
                  textDocument: {
                    uri: updatedDoc.uri,
                    version: updatedDoc.version,
                  },
                  position: goalsQueryPos,
                  pp_format: 'Str',
                  mode: oneLineSplit ? 'Prev' : 'Prev',
                })
              );
              if (goalsResult.error) {
                console.error('Goals query error:', goalsResult.error);
              }
              goals = goalsResult;
            } catch (err) {
              console.error('Failed to get goals:', err);
            }
          }

          const gcAfter = goals?.goals;
          const nFocus = gcAfter?.goals?.length ?? 0;
          const nBg = (gcAfter?.stack || []).reduce(
            (s: number, [b, a]: any[]) => s + (b?.length || 0) + (a?.length || 0), 0
          );
          const hint = gcAfter ? nextHint(gcAfter) : '';

          const stateMsg = goals?.error
            ? `error: ${goals?.error}`
            : oneLineSplit ? 'inserted'
            : gcAfter === undefined || gcAfter === null
            ? 'goals query failed'
            : nFocus === 0 && nBg === 0 ? 'done — Qed applied'
            : nFocus === 0 ? `bullet closed, ${nBg} in background`
            : nBg > 0 ? `${nFocus} at focus, ${nBg} in background (bullet open)`
            : `${nFocus} goal(s)`;

          // Auto-close: when all goals are done, replace the Admitted. stub with Qed.
          const hasErrors = (goals?.messages || []).some((m: any) => m.level === 1);
          if (nFocus === 0 && nBg === 0 && gcAfter !== undefined && gcAfter !== null && !hasErrors) {
            const currentDoc = docManager.getDocument(file);
            if (currentDoc) {
              const lines = currentDoc.text.split('\n');
              // Find the Admitted. line starting from the insert position
              let admittedLine = -1;
              for (let i = insPos.line; i < lines.length; i++) {
                if (lines[i].trim() === 'Admitted.') {
                  admittedLine = i;
                  break;
                }
              }
              if (admittedLine >= 0) {
                pushFileHistory(file, currentDoc.text);
                const replaceEdit = {
                  range: {
                    start: { line: admittedLine, character: 0 },
                    end: { line: admittedLine, character: lines[admittedLine].length },
                  },
                  newText: 'Qed.\n',
                };
                const newText = docManager.applyEdits(currentDoc.text, [replaceEdit]);
                await docManager.updateDocument(file, newText);
                await docManager.saveDocument(file);
              }
            }
          }

          // Extract proof script for context
          const scriptLines: string[] = [];
          {
            const fLines = doc.text.split('\n');
            let pl = insertedUntil.line;
            for (; pl >= 0; pl--) {
              const t = (fLines[pl] || '').trim();
              if (t === 'Proof.' || t.startsWith('Proof. ')) break;
            }
            if (pl >= 0) {
              for (let i = pl + 1; i <= insertedUntil.line; i++) {
                const l = fLines[i];
                if (!l) continue;
                const t = l.trim();
                if (t === '' || t === 'Proof.') continue;
                if (isSkipLine(l)) continue;
                if (isTopLevelLine(l)) break;
                scriptLines.push(l);
              }
            }
          }
          const scriptBlock = scriptLines.length > 0
            ? '\n-- proof script ----------\n' + scriptLines.map(l => `  ${l}`).join('\n')
            : '';

          // Build a focused goals object for the reply — strip background (stack) goals
          // to avoid confusing the display with Admitted-continuation state.
          let focusedGoals = goals?.goals || null;
          if (focusedGoals && nBg > 0) {
            focusedGoals = { ...focusedGoals, stack: [] };
          }

          // Compact summary of the new focus state for the response text
          const focusSummary = gcAfter ? compactGoalSummary(gcAfter) : '';

          return reply(
            `${fileLine(file, position.line)} — inserted "${tactic.trim()}" → ${stateMsg}${focusSummary ? '\n  ' + focusSummary : ''}${scriptBlock}${hint ? '\n  next: ' + hint : ''}`,
            {
              applied: true,
              inserted_until: insertedUntil,
              next_tactic_position: nextTacticPosition,
              next: hint,
              goals: focusedGoals,
              script: scriptLines,
              messages: goals?.messages || [],
              error: goals?.error || null,
            }
          );
        }

        case 'coq_check': {
          const { file } = args as { file: string };

          try {
            const doc = await ensureDocumentOpened(file);

            const result = await retryDocumentNotReady(() =>
              lspClient.sendRequest<{
                spans: Array<{ range: Range }>;
                completed: { status: string; range: Range };
              }>('coq/getDocument', {
                textDocument: {
                  uri: doc.uri,
                  version: doc.version,
                },
                ast: false,
                goals: 'Str',
              })
            );

            const spanCount = result.spans?.length || 0;
            const range = result.completed?.range;
            const loc = range ? `L${range.start.line}-L${range.end.line}` : '?';

            // Count Admitted. occurrences and locate them
            const docLines = doc.text.split('\n');
            let admittedCount = 0;
            const admittedAt: number[] = [];
            const admittedGoals: string[] = [];
            for (let i = 0; i < docLines.length; i++) {
              if (docLines[i].trim() === 'Admitted.') { admittedCount++; admittedAt.push(i); }
            }
            // For each admitted position, query the proof goals to report what remains.
            for (const line of admittedAt) {
              try {
                const gResult = await retryDocumentNotReady(() =>
                  lspClient.sendRequest<GoalAnswer<string>>('proof/goals', {
                    textDocument: { uri: doc.uri, version: doc.version },
                    position: { line, character: 0 },
                    pp_format: 'Str',
                    mode: 'Prev',
                  })
                );
                const nG = gResult.goals?.goals?.length || 0;
                if (nG > 0) {
                  admittedGoals.push(`L${line + 1}: ${nG} goal(s)`);
                }
              } catch {}
            }

            const admittedInfo = admittedCount > 0
              ? `, ${admittedCount} admitted (${admittedAt.map(l => l + 1).join(', ')})` +
                (admittedGoals.length > 0 ? ` — ${admittedGoals.join(', ')}` : '')
              : '';

            // Summary: scan file for toplevel names and their status
            const items: string[] = [];
            for (let i = 0; i < docLines.length; i++) {
              const l = docLines[i].trim();
              const kw = l.split(/\s+/)[0];
              if (kw === 'Lemma' || kw === 'Theorem' || kw === 'Corollary' ||
                  kw === 'Definition' || kw === 'Fixpoint' || kw === 'Inductive' ||
                  kw === 'Example') {
                const namePart = l.split(':')[0].replace(kw, '').trim();
                // Extract type/statement (everything after first colon)
                const colonIdx = l.indexOf(':');
                let typeStr = '';
                if (colonIdx >= 0) {
                  typeStr = l.slice(colonIdx + 1).trim().replace(/\.$/, '');
                  if (typeStr.length > 80) typeStr = typeStr.slice(0, 77) + '...';
                }
                let status = '?';
                for (let j = i + 1; j < docLines.length; j++) {
                  const t = docLines[j].trim();
                  if (t === 'Qed.') { status = 'Qed'; break; }
                  if (t === 'Admitted.') { status = 'Admitted'; break; }
                  if (isTopLevelLine(docLines[j] || '')) { status = 'open'; break; }
                }
                const typePart = typeStr ? ` : ${typeStr}` : '';
                items.push(`${kw} ${namePart}${typePart}: ${status} (L${i + 1})`);
              }
            }
            const summary = items.length > 0 ? '\n' + items.join('\n') : '';

            return reply(
              `${fileLine(file, 0)} — ${result.completed?.status || 'unknown'}, ${spanCount} spans (${loc})` + admittedInfo + summary,
              { file, completed: result.completed?.status, span_count: spanCount, completed_range: loc, admitted: admittedCount, admitted_lines: admittedAt, success: true }
            );
          } catch (error) {
            return err(
              `${fileLine(file, 0)} — check failed: ${error instanceof Error ? error.message : String(error)}`,
              error instanceof Error ? error.message : String(error)
            );
          }
        }

        case 'coq_check_range': {
          const { file, range } = args as { 
            file: string; 
            range: { start: { line: number; character?: number }; end: { line: number; character?: number } };
          };

          try {
            const doc = await ensureDocumentOpened(file);

            // Get the full document info first
            const result = await retryDocumentNotReady(() =>
              lspClient.sendRequest<{
                spans: Array<{ range: Range }>;
                completed: { status: string; range: Range };
              }>('coq/getDocument', {
                textDocument: {
                  uri: doc.uri,
                  version: doc.version,
                },
                ast: false,
                goals: 'Str',
              })
            );

            // Filter spans to those within the requested range
            const targetSpans = result.spans?.filter(span => {
              const spanLine = span.range.start.line;
              return spanLine >= range.start.line && spanLine <= range.end.line;
            }) || [];

            // Check if any spans in the range have errors (we'll need to get diagnostics)
            // For now, just return span information
            const spanCount = targetSpans.length;
            return reply(
              `${fileLine(file, range.start.line)}-${fileLine(file, range.end.line)} — ${spanCount} span(s), overall: ${result.completed?.status || 'unknown'}`,
              { file, range: `L${range.start.line}-L${range.end.line}`, span_count: spanCount, overall_completed: result.completed?.status, success: true }
            );
          } catch (error) {
            return err(
              `${fileLine(file, range.start.line)}-${fileLine(file, range.end.line)} — check failed: ${error instanceof Error ? error.message : String(error)}`,
              error instanceof Error ? error.message : String(error)
            );
          }
        }

        case 'coq_search': {
          const { file, pattern } = args as {
            file: string;
            pattern: string;
          };

          const doc = await ensureDocumentOpened(file);

          const docInfo = await retryDocumentNotReady(() =>
            lspClient.sendRequest<{
              spans: Array<{ range: Range }>;
            }>('coq/getDocument', {
              textDocument: { uri: doc.uri, version: doc.version },
              ast: false,
            })
          );

          const targetPos: Position =
            (docInfo.spans && docInfo.spans.length > 0)
              ? docInfo.spans[0].range.start
              : { line: 0, character: 0 };

          const stateResult = await retryDocumentNotReady(() =>
            lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
              uri: doc.uri,
              position: targetPos,
              opts: { memo: true, hash: true },
            })
          );

          // Run pending speculative imports, then the query
          const searchSt = await runPendingImports(doc.uri, stateResult.st);

          // Pass pattern to Coq's Search command.
          // Simple identifiers get quoted string search: Search "plus_n_O".
          // Patterns like "_ + 0 = _" need to be wrapped in parens: Search (_ + 0 = _).
          // Other forms like "leb" or "leb_le : ..." pass through as-is.
          const searchText = (() => {
            if (/^[a-zA-Z_][a-zA-Z0-9_']*$/.test(pattern))
              return `Search "${pattern}".`;
            if (/^_ [^:]+ _/.test(pattern) && !pattern.startsWith('('))
              return `Search (${pattern}).`;
            return `Search ${pattern}.`;
          })();

          let runResult: RunResult<number>;
          let errorMsg: string | null = null;
          try {
            runResult = await lspClient.sendRequest<RunResult<number>>(
              'petanque/run',
              { st: searchSt, tac: searchText, opts: { memo: false, hash: false } }
            );
          } catch (e: any) {
            // Try fallback: if the literal form failed and pattern has quotes, try without
            errorMsg = e?.message || String(e);
            runResult = { st: stateResult.st, proof_finished: false, feedback: [] };
          }

          const msgs = (runResult.feedback || []).map(([level, msg]: [number, string]) => ({ level, message: msg }));
          const results = msgs.length > 0
            ? msgs.map(m => m.message).join('\n')
            : errorMsg || '(no results)';
          return reply(
            `Search "${pattern}" → ${msgs.length} result(s)\n${results}`,
            { messages: msgs, error: errorMsg }
          );
        }

        case 'coq_check_term': {
          const { file, term } = args as {
            file: string;
            term: string;
          };

          const doc3 = await ensureDocumentOpened(file);

          const docInfo3 = await retryDocumentNotReady(() =>
            lspClient.sendRequest<{
              spans: Array<{ range: Range }>;
            }>('coq/getDocument', {
              textDocument: { uri: doc3.uri, version: doc3.version },
              ast: false,
            })
          );

          const targetPos3: Position =
            (docInfo3.spans && docInfo3.spans.length > 0)
              ? docInfo3.spans[0].range.start
              : { line: 0, character: 0 };

          const stateResult3 = await retryDocumentNotReady(() =>
            lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
              uri: doc3.uri,
              position: targetPos3,
              opts: { memo: true, hash: true },
            })
          );

          const checkSt = await runPendingImports(doc3.uri, stateResult3.st);

          const runResult3 = await lspClient.sendRequest<RunResult<number>>('petanque/run', {
            st: checkSt,
            tac: `Check ${term}.`,
            opts: { memo: false, hash: false },
          });

          const msgs3 = runResult3.feedback.map(([level, msg]) => ({ level, message: msg }));
          return reply(
            `Check ${term} → ${msgs3.length} message(s): ${msgs3.map(m => m.message).join('; ')}`,
            { messages: msgs3 }
          );
        }

        case 'coq_about': {
          const { file, term } = args as {
            file: string;
            term: string;
          };

          const doc4 = await ensureDocumentOpened(file);

          const docInfo4 = await retryDocumentNotReady(() =>
            lspClient.sendRequest<{
              spans: Array<{ range: Range }>;
            }>('coq/getDocument', {
              textDocument: { uri: doc4.uri, version: doc4.version },
              ast: false,
            })
          );

          const targetPos4: Position =
            (docInfo4.spans && docInfo4.spans.length > 0)
              ? docInfo4.spans[0].range.start
              : { line: 0, character: 0 };

          const stateResult4 = await retryDocumentNotReady(() =>
            lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
              uri: doc4.uri,
              position: targetPos4,
              opts: { memo: true, hash: true },
            })
          );

          const aboutSt = await runPendingImports(doc4.uri, stateResult4.st);

          const runResult4 = await lspClient.sendRequest<RunResult<number>>('petanque/run', {
            st: aboutSt,
            tac: `About ${term}.`,
            opts: { memo: false, hash: false },
          });

          const msgs4 = runResult4.feedback.map(([level, msg]) => ({ level, message: msg }));
          return reply(
            `About ${term} → ${msgs4.length} message(s): ${msgs4.map(m => m.message).join('; ')}`,
            { messages: msgs4 }
          );
        }

        case 'coq_undo': {
          const { file, n } = args as {
            file: string;
            n?: number;
          };

          const count = n ?? 1;
          const stack = fileHistory.get(file) || [];

          if (stack.length === 0) {
            throw new Error(`Nothing to undo for ${file}`);
          }
          if (stack.length < count) {
            throw new Error(`Can only undo ${stack.length} operation(s), requested ${count}`);
          }

          const restoreIdx = stack.length - count;
          const restoreText = stack[restoreIdx];
          fileHistory.set(file, stack.slice(0, restoreIdx));

          await docManager.updateDocument(file, restoreText);
          await docManager.saveDocument(file);

          return reply(
            `${fileLine(file, 0)} — undone ${count} operation(s), ${restoreIdx} remaining in history`,
            { applied: true, undone: count, remaining_history: restoreIdx }
          );
        }

        case 'coq_try_tactic': {
          const { file, name, tactic, compact } = args as {
            file: string;
            name: string;
            tactic: string;
            compact?: boolean;
          };

          const doc = await ensureDocumentOpened(file);
          const docLines = doc.text.split('\n');
          const proofLine = findProofLine(docLines, name);
          if (proofLine < 0) throw new Error(`Proof not found: "${name}"`);
          // Use insertPosition (same as coq_insert_tactic) to find the current
          // proof cursor — this is the Admitted./Qed. line. Passing that position
          // to get_state_at_pos in Prev mode gives the state after all preceding
          // tactics, i.e. the current proof state.
          const position = insertPosition(doc.text, { line: proofLine, character: 0 });
          const uri = doc.uri;

          async function getStateAt(pos: Position) {
            return retryDocumentNotReady(() =>
              lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
                uri, position: pos, opts: { memo: true, hash: true },
              })
            );
          }

          async function tryRunTactic(st: number) {
            const r = await lspClient.sendRequest<RunResult<number>>('petanque/run', {
              st, tac: tactic, opts: { memo: true, hash: true },
            });
            const g = await lspClient.sendRequest<GoalConfig<string>>('petanque/goals', {
              st: r.st, opts: { compact: compact ?? true },
            });
            return { runResult: r, goalsResult: g };
          }

          // Try at user's position (Prev mode)
          const stateResult = await getStateAt(position);
          let result: { runResult: RunResult<number>; goalsResult: GoalConfig<string> };
          try {
            result = await tryRunTactic(stateResult.st);
          } catch (e: any) {
            if (e?.message?.includes('illegal begin of vernac') ||
                e?.message?.includes('No proof-editing in progress')) {
              // Position is outside proof mode — either before or after the proof body.
              // Find the last span that ends before our position and retry from there.
              const docInfo = await retryDocumentNotReady(() =>
                lspClient.sendRequest<{ spans: Array<{ range: Range }> }>('coq/getDocument', {
                  textDocument: { uri, version: doc.version }, ast: false,
                })
              );
              const allSpans = docInfo.spans || [];
              // First try: span just before position (we landed after proof end)
              const spansBefore = allSpans.filter(
                s => s.range.end.line < position.line ||
                     (s.range.end.line === position.line && s.range.end.character <= position.character)
              ).sort((a, b) => b.range.end.line - a.range.end.line || b.range.end.character - a.range.end.character);
              if (spansBefore.length > 0) {
                const prevSpan = spansBefore[0];
                const prevPos: Position = { line: prevSpan.range.end.line, character: prevSpan.range.end.character };
                try {
                  const prevState = await getStateAt(prevPos);
                  result = await tryRunTactic(prevState.st);
                } catch {
                  throw e;
                }
              } else {
                // Fall back: try span just after position (we landed before proof start)
                const spansAfter = allSpans.filter(
                  s => s.range.start.line > position.line || (s.range.start.line === position.line && s.range.start.character > position.character)
                ).sort((a, b) => a.range.start.line - b.range.start.line || a.range.start.character - b.range.start.character);
                if (spansAfter.length === 0) throw e;
                const innerState = await getStateAt(spansAfter[0].range.start);
                result = await tryRunTactic(innerState.st);
              }
            } else {
              throw e;
            }
          }

          const { runResult, goalsResult } = result;
          const finished = runResult.proof_finished ? ' (proof finished!)' : '';
          const nGoals = goalsResult.goals?.length || 0;

          // Format goals for display
          let goalText = '';
          if (goalsResult.goals && goalsResult.goals.length > 0) {
            goalText = '\n' + formatGoals(goalsResult);
          }

          return reply(
            `"${tactic}" at ${fileLine(file, position.line)} → ${nGoals} goal(s)${finished}${goalText}`,
            { state_id: runResult.st, proof_finished: runResult.proof_finished, goals: goalsResult, feedback: runResult.feedback }
          );
        }

        case 'coq_require': {
          const { file, lib } = args as {
            file: string;
            lib: string;
          };

          const doc = await ensureDocumentOpened(file);

          const docInfo = await retryDocumentNotReady(() =>
            lspClient.sendRequest<{
              spans: Array<{ range: Range }>;
            }>('coq/getDocument', {
              textDocument: { uri: doc.uri, version: doc.version },
              ast: false,
            })
          );

          const targetPos: Position =
            (docInfo.spans && docInfo.spans.length > 0)
              ? docInfo.spans[0].range.start
              : { line: 0, character: 0 };

          const stateResult = await retryDocumentNotReady(() =>
            lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
              uri: doc.uri,
              position: targetPos,
              opts: { memo: true, hash: true },
            })
          );

          const runResult = await lspClient.sendRequest<RunResult<number>>(
            'petanque/run',
            { st: stateResult.st, tac: `Require Import ${lib}.`, opts: { memo: false, hash: false } }
          );

          const msgs = (runResult.feedback || []).map(([level, msg]: [number, string]) => ({ level, message: msg }));
          const ok = !msgs.some(m => m.level === 1);
          if (ok) {
            // Register persistent speculative import
            const uri = docManager.pathToUri(file);
            const existing = speculativeImports.get(uri) || [];
            if (!existing.includes(lib)) {
              existing.push(lib);
              speculativeImports.set(uri, existing);
            }
          }
          return reply(
            ok
              ? `Imported ${lib} — available for subsequent queries on ${file}`
              : `Error importing ${lib}: ${msgs.map(m => m.message).join('; ')}`,
            { ok, messages: msgs }
          );
        }

        case 'coq_locate': {
          const { file, thing } = args as {
            file: string;
            thing: string;
          };

          const doc = await ensureDocumentOpened(file);

          const docInfo = await retryDocumentNotReady(() =>
            lspClient.sendRequest<{
              spans: Array<{ range: Range }>;
            }>('coq/getDocument', {
              textDocument: { uri: doc.uri, version: doc.version },
              ast: false,
            })
          );

          const targetPos: Position =
            (docInfo.spans && docInfo.spans.length > 0)
              ? docInfo.spans[0].range.start
              : { line: 0, character: 0 };

          const stateResult = await retryDocumentNotReady(() =>
            lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
              uri: doc.uri,
              position: targetPos,
              opts: { memo: true, hash: true },
            })
          );

          const locateSt = await runPendingImports(doc.uri, stateResult.st);

          const runResult = await lspClient.sendRequest<RunResult<number>>(
            'petanque/run',
            { st: locateSt, tac: `Locate ${thing}.`, opts: { memo: false, hash: false } }
          );

          const msgs = (runResult.feedback || []).map(([level, msg]: [number, string]) => ({ level, message: msg }));
          const results = msgs.length > 0
            ? msgs.map(m => m.message).join('\n')
            : '(not found)';
          return reply(
            `Locate "${thing}" → ${msgs.length} result(s)\n${results}`,
            { messages: msgs }
          );
        }

        case 'coq_reset_proof': {
          const { file, name } = args as {
            file: string;
            name: string;
          };

          const doc = await ensureDocumentOpened(file);
          const docLines = doc.text.split('\n');
          const proofLine = findProofLine(docLines, name);
          if (proofLine < 0) throw new Error(`Proof not found: "${name}"`);

          let foundClosing = false;
          let endLine = proofLine + 1;
          while (endLine < docLines.length) {
            const l = (docLines[endLine] || '').trim();
            if (l === 'Qed.' || l === 'Admitted.' || l === 'Defined.') { foundClosing = true; break; }
            if (isTopLevelLine(docLines[endLine] || '')) break;
            endLine++;
          }

          const end = foundClosing
            ? { line: endLine + 1, character: 0 }
            : (endLine < docLines.length
                ? { line: endLine, character: 0 }
                : { line: endLine, character: (docLines[endLine - 1] || '').length });

          const newText = docManager.applyEdits(doc.text, [{
            range: {
              start: { line: proofLine + 1, character: 0 },
              end,
            },
            newText: 'Admitted.\n',
          }]);

          await docManager.updateDocument(file, newText);
          await docManager.saveDocument(file);

          // Find the proof name
          let nameLine = proofLine - 1;
          let proofName = 'unknown';
          while (nameLine >= 0) {
            const nl = (docLines[nameLine] || '').trim();
            if (isTopLevelLine(docLines[nameLine] || '')) {
              proofName = nl.split(':')[0].trim();
              break;
            }
            nameLine--;
          }

          return reply(
            `${fileLine(file, proofLine)} — reset "${proofName}" to Admitted.`,
            { applied: true, proof: proofName }
          );
        }

        case 'coq_add_lemma': {
          const { file, name, statement, before } = args as {
            file: string;
            name: string;
            statement: string;
            before?: string;
          };

          const doc = await ensureDocumentOpened(file);
          const docLines = doc.text.split('\n');

          // Check if lemma already exists
          for (let i = 0; i < docLines.length; i++) {
            const l = docLines[i].trim();
            const kw = l.split(/\s+/)[0];
            if ((kw === 'Lemma' || kw === 'Theorem' || kw === 'Corollary' || kw === 'Example') &&
                l.includes(name + ' :') && (l.includes(name + ' :') || l.includes(name + ':'))) {
              const existingStmt = l.split(':').slice(1).join(':').trim().replace(/\.$/, '');
              if (existingStmt === statement.trim()) {
                return reply(
                  `${fileLine(file, i)} — Lemma ${name} already exists with same statement (no-op)`,
                  { exists: true, identical: true, line: i, proof: name, statement: existingStmt }
                );
              }
              return reply(
                `${fileLine(file, i)} — Lemma ${name} already exists with different statement`,
                { exists: true, identical: false, line: i, proof: name, existing_statement: existingStmt, requested_statement: statement }
              );
            }
          }

          // Resolve insertion line via before parameter
          let targetLine: number;
          if (before) {
            const pLine = findProofLine(docLines, before);
            if (pLine < 0) throw new Error(`"${before}" not found`);
            for (let i = pLine - 1; i >= 0; i--) {
              const kw = (docLines[i] || '').trim().split(/\s+/)[0];
              if (kw === 'Lemma' || kw === 'Theorem' || kw === 'Corollary' ||
                  kw === 'Definition' || kw === 'Fixpoint' || kw === 'Inductive' ||
                  kw === 'Example' || kw === 'Axiom') {
                targetLine = i;
                break;
              }
            }
            targetLine = targetLine!;
          } else {
            throw new Error('"before" parameter is required — specify which proof to insert above');
          }

          const block = `\nLemma ${name} : ${statement}.\nProof.\nAdmitted.\n\n`;
          const newText = docManager.applyEdits(doc.text, [{
            range: { start: { line: targetLine, character: 0 }, end: { line: targetLine, character: 0 } },
            newText: block,
          }]);

          await docManager.updateDocument(file, newText);
          await docManager.saveDocument(file);

          // Lint: check the inserted range for errors
          try {
            const checkResult = await lspClient.sendRequest<{
              diagnostics: Array<{ range: Range; severity: number; message: string }>;
            }>('coq/check', { textDocument: { uri: doc.uri, version: docManager.getDocument(file)!.version } });
            const diags = (checkResult.diagnostics || []).filter((d: any) => d.range.start.line >= targetLine && d.range.start.line < targetLine + 6 && d.severity === 1);
            if (diags.length > 0) {
              const old = docManager.applyEdits(newText, [{
                range: { start: { line: targetLine, character: 0 }, end: { line: targetLine + block.split('\n').length, character: 0 } },
                newText: '',
              }]);
              await docManager.updateDocument(file, old);
              await docManager.saveDocument(file);
              throw new Error(`Lemma type error: ${diags[0].message}`);
            }
          } catch (e: any) {
            if (e.message && e.message.startsWith('Lemma type error')) throw e;
          }

          return reply(
            `${fileLine(file, targetLine)} — added Lemma ${name}`,
            { applied: true }
          );
        }

        default:
          throw new Error(`Unknown tool: ${name}`);
      }
    } catch (error) {
      const e = error as Error & { data?: unknown };
      return err(
        `${name}: ${e.message}`,
        String(e.data ?? e.message)
      );
    }
  });

  // Connect stdio transport
  const transport = new StdioServerTransport();
  await server.connect(transport);

  // Handle shutdown
  process.on('SIGINT', async () => {
    await lspClient.shutdown();
    process.exit(0);
  });

  process.on('SIGTERM', async () => {
    await lspClient.shutdown();
    process.exit(0);
  });
}

main().catch((error) => {
  console.error('Fatal error:', error);
  process.exit(1);
});
