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
        args.push('-R', `${srcDir},`);
      }
      const buildDir = resolvePath(root, '_build', 'default', 'coq');
      if (fs.existsSync(buildDir)) {
        args.push('-R', `${buildDir},`);
      }
    } catch {}
    return args;
  }

  // Initialize with initial workspace root
  finalRocqLspArgs = computeRocqLspArgs(workspaceRoot);

  // Track the active project root for dynamic workspace switching
  let activeWorkspaceRoot = workspaceRoot;

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
      return await docManager.openDocument(path);
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
            'Get current open goals at a given position in a Coq/Rocq file',
          inputSchema: {
            type: 'object',
            properties: {
              file: {
                type: 'string',
                description: 'Path to the .v file',
              },
              position: {
                type: 'object',
                properties: {
                  line: { type: 'number' },
                  character: { type: 'number' },
                },
                required: ['line', 'character'],
                description: 'Position in the file (0-based)',
              },
              pp_format: {
                type: 'string',
                enum: ['Str', 'Pp'],
                description: 'Pretty-printing format (default: Str)',
              },
              compact: {
                type: 'boolean',
                description: 'Use compact hypothesis display',
              },
              mode: {
                type: 'string',
                enum: ['Prev', 'After'],
                description: 'Goal position mode (default: After)',
              },
            },
            required: ['file', 'position'],
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
          description: 'Apply text edits to a file and re-sync with rocq-lsp',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string' },
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
            required: ['file', 'edits'],
          },
        },
        {
          name: 'coq_insert_tactic',
          description:
            'High-level helper: insert a tactic and return updated goals',
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
              tactic: { type: 'string' },
              follow_with_goals: {
                type: 'boolean',
                description: 'Query goals after inserting',
              },
            },
            required: ['file', 'position', 'tactic'],
          },
        },
        {
          name: 'coq_search',
          description:
            'Search for lemmas/theorems without polluting the source file. Runs `Search <pattern>.` speculatively and returns results.',
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
            'Remove the last N tactics from the file and re-sync with rocq-lsp.',
          inputSchema: {
            type: 'object',
            properties: {
              file: { type: 'string' },
              n: {
                type: 'number',
                description: 'Number of tactics to undo (default: 1)',
              },
            },
            required: ['file'],
          },
        },
        {
          name: 'coq_try_tactic',
          description:
            'Single-call speculative tactic execution: get state, run tactic, and return updated goals.',
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
              tactic: { type: 'string', description: 'Tactic to run speculatively' },
              compact: { type: 'boolean', description: 'Use compact hypothesis display' },
            },
            required: ['file', 'position', 'tactic'],
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
      const detailParts: string[] = [];
      if (d?.goals) {
        const goalsWrapped = Array.isArray(d.goals) ? { goals: d.goals } : d.goals;
        detailParts.push(formatGoals(goalsWrapped));
      }
      if (Array.isArray(d?.feedback)) detailParts.push(formatFeedback(d.feedback));
      detailParts.push(formatSemi(data, 0));
      const detail = detailParts.join('\n');
      const goalsObj = d?.goals ? (Array.isArray(d.goals) ? { goals: d.goals } : d.goals) : null;
      const extra = goalsObj ? compactGoalSummary(goalsObj) : '';
      const compact = extra || summary;
      return {
        content: [
          { type: 'text' as const, text: compact },
          { type: 'text' as const, text: detail },
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

    function formatGoals(goals: any): string {
      const gl = goals?.goals || [];
      if (gl.length === 0) {
        const prog = goals?.program?.length || 0;
        const msgs = (goals?.messages || []).filter((m: any) => m.level === 1).map((m: any) => m.text).join('; ');
        return 'no goals' + (prog ? ` (${prog} program items)` : '') + (msgs ? '\n  messages: ' + msgs : '');
      }
      return gl.map((g: any, i: number) => {
        const idx = gl.length > 1 ? `Goal ${i + 1}: ` : '';
        const hyps = (g.hyps || []).map((h: any) => {
          const name = h.names ? h.names.join(', ') : (h.name || '?');
          return `  ${name}: ${h.ty || h.type}`;
        }).join('\n');
        return (hyps ? hyps + '\n' : '') + idx + '⊢ ' + g.ty;
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
          const { file, position, pp_format, compact, mode } = args as {
            file: string;
            position: Position;
            pp_format?: string;
            compact?: boolean;
            mode?: string;
          };

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
              mode: mode || 'After',
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
          const { file, edits } = args as {
            file: string;
            edits: Array<{ range: Range; newText: string }>;
          };

          // Get current document
          let doc = docManager.getDocument(file);
          if (!doc) {
            doc = await ensureDocumentOpened(file);
          }

          // Apply edits
          const newText = docManager.applyEdits(doc.text, edits);

          // Update and save
          await docManager.updateDocument(file, newText);
          await docManager.saveDocument(file);

          const updatedDoc = docManager.getDocument(file)!;

          return reply(
            `${fileLine(file, 0)} — applied ${edits.length} edit(s), v${updatedDoc.version}`,
            { file, new_version: updatedDoc.version }
          );
        }

        case 'coq_insert_tactic': {
          const { file, position, tactic, follow_with_goals } = args as {
            file: string;
            position: Position;
            tactic: string;
            follow_with_goals?: boolean;
          };

          // Insert tactic at position
          const insertText = tactic.endsWith('\n') ? tactic : `${tactic}\n`;

          await ensureDocumentOpened(file);

          // Apply edit
          const doc = docManager.getDocument(file)!;
          const newText = docManager.applyEdits(doc.text, [
            {
              range: {
                start: position,
                end: position,
              },
              newText: insertText,
            },
          ]);

          await docManager.updateDocument(file, newText);
          await docManager.saveDocument(file);

          let goals = null;
          if (follow_with_goals ?? true) {
            const updatedDoc = docManager.getDocument(file)!;
            try {
              const insertLines = insertText.split('\n');
              let lastLineIdx = insertLines.length - 1;
              if (insertLines[lastLineIdx] === '' && lastLineIdx > 0) lastLineIdx--;
              const afterPosition: Position = {
                line: position.line + lastLineIdx,
                character: insertLines[lastLineIdx].length,
              };
              const goalsResult = await lspClient.sendRequest<
                GoalAnswer<string>
              >('proof/goals', {
                textDocument: {
                  uri: updatedDoc.uri,
                  version: updatedDoc.version,
                },
                position: afterPosition,
                pp_format: 'Str',
              });
              goals = goalsResult;
            } catch (err) {
              console.error('Failed to get goals:', err);
            }
          }

          const ngls = goals?.goals?.goals?.length ?? 0;
          return reply(
            `${fileLine(file, position.line)} — inserted "${tactic.trim()}" → ${ngls} goal(s)`,
            { applied: true, goals: goals?.goals, messages: goals?.messages || [], error: goals?.error || null }
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
            return reply(
              `${fileLine(file, 0)} — ${result.completed?.status || 'unknown'}, ${spanCount} spans (${loc})`,
              { file, completed: result.completed?.status, span_count: spanCount, completed_range: loc, success: true }
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

          const runResult = await lspClient.sendRequest<RunResult<number>>('petanque/run', {
            st: stateResult.st,
            tac: `Search ${pattern}.`,
            opts: { memo: false, hash: false },
          });

          const msgs = runResult.feedback.map(([level, msg]) => ({ level, message: msg }));
          return reply(
            `Search "${pattern}" → ${msgs.length} result(s)`,
            { messages: msgs }
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

          const runResult3 = await lspClient.sendRequest<RunResult<number>>('petanque/run', {
            st: stateResult3.st,
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

          const runResult4 = await lspClient.sendRequest<RunResult<number>>('petanque/run', {
            st: stateResult4.st,
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
            })
          );

          const spans = result.spans || [];
          if (spans.length < count) {
            throw new Error(
              `Cannot undo ${count}: only ${spans.length} span(s) available`
            );
          }

          const sortedSpans = [...spans].sort((a, b) => {
            if (a.range.start.line !== b.range.start.line) {
              return a.range.start.line - b.range.start.line;
            }
            return a.range.start.character - b.range.start.character;
          });

          const firstUndone = sortedSpans[sortedSpans.length - count];
          const lastUndone = sortedSpans[sortedSpans.length - 1];

          const newText = docManager.applyEdits(doc.text, [
            {
              range: {
                start: firstUndone.range.start,
                end: lastUndone.range.end,
              },
              newText: '',
            },
          ]);

          await docManager.updateDocument(file, newText);
          await docManager.saveDocument(file);

          return reply(
            `${fileLine(file, 0)} — undone ${count} span(s), ${spans.length - count} remaining`,
            { applied: true, removed_spans: count }
          );
        }

        case 'coq_try_tactic': {
          const { file, position, tactic, compact } = args as {
            file: string;
            position: Position;
            tactic: string;
            compact?: boolean;
          };

          const doc = await ensureDocumentOpened(file);

          const stateResult = await retryDocumentNotReady(() =>
            lspClient.sendRequest<RunResult<number>>('petanque/get_state_at_pos', {
              uri: doc.uri,
              position,
              opts: { memo: true, hash: true },
            })
          );

          const runResult = await lspClient.sendRequest<RunResult<number>>('petanque/run', {
            st: stateResult.st,
            tac: tactic,
            opts: { memo: true, hash: true },
          });

          const goalsResult = await lspClient.sendRequest<GoalConfig<string>>(
            'petanque/goals',
            {
              st: runResult.st,
              opts: { compact: compact ?? true },
            }
          );

          const finished = runResult.proof_finished ? ' (proof finished!)' : '';
          const nGoals = goalsResult.goals?.length || 0;
          return reply(
            `"${tactic}" at ${fileLine(file, position.line)} → ${nGoals} goal(s)${finished}`,
            { state_id: runResult.st, proof_finished: runResult.proof_finished, goals: goalsResult, feedback: runResult.feedback }
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
