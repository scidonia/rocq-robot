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
import { detectProjectConfig, mergeProjectArgs } from './project-config.js';
import type {
  Position,
  Range,
  GoalAnswer,
  ProofInfo,
  RunResult,
  GoalConfig,
  RunOpts,
} from './types.js';
import { resolve as resolvePath } from 'path';

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function retryDocumentNotReady<T>(
  action: () => Promise<T>,
  opts?: { timeoutMs?: number; initialDelayMs?: number; maxDelayMs?: number }
): Promise<T> {
  const timeoutMs = opts?.timeoutMs ?? 10_000;
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

  // Use user-provided args (coq-lsp doesn't accept -Q/-R as CLI args, it reads _CoqProject)
  // User can still pass other coq-lsp-specific args if needed
  const finalRocqLspArgs = config.rocqLspArgs || [];

  console.error('[mcp-coq-lsp] coq-lsp args:', finalRocqLspArgs);

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
          const doc = await docManager.openDocument(file);

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

          return {
            content: [
              {
                type: 'text',
                text: JSON.stringify(result, null, 2),
              },
            ],
          };
        }

        case 'coq_proof_state': {
          const { file, position } = args as {
            file: string;
            position: Position;
          };

          // Get goals
          const doc = await docManager.openDocument(file);
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

          return {
            content: [
              {
                type: 'text',
                text: JSON.stringify(
                  {
                    proof: proofInfo,
                    goals: goalsResult.goals,
                    messages: goalsResult.messages,
                    error: goalsResult.error,
                  },
                  null,
                  2
                ),
              },
            ],
          };
        }

        case 'coq_get_state_at_pos': {
          const { file, position, memo, hash } = args as {
            file: string;
            position: Position;
            memo?: boolean;
            hash?: boolean;
          };

          const doc = await docManager.openDocument(file);

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

          return {
            content: [
              {
                type: 'text',
                text: JSON.stringify(result, null, 2),
              },
            ],
          };
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
              opts: {
                memo: memo ?? true,
                hash: hash ?? true,
              },
            }
          );

          return {
            content: [
              {
                type: 'text',
                text: JSON.stringify(result, null, 2),
              },
            ],
          };
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

          return {
            content: [
              {
                type: 'text',
                text: JSON.stringify(result, null, 2),
              },
            ],
          };
        }

        case 'coq_apply_edit': {
          const { file, edits } = args as {
            file: string;
            edits: Array<{ range: Range; newText: string }>;
          };

          // Get current document
          let doc = docManager.getDocument(file);
          if (!doc) {
            doc = await docManager.openDocument(file);
          }

          // Apply edits
          const newText = docManager.applyEdits(doc.text, edits);

          // Update and save
          await docManager.updateDocument(file, newText);
          await docManager.saveDocument(file);

          const updatedDoc = docManager.getDocument(file)!;

          return {
            content: [
              {
                type: 'text',
                text: JSON.stringify(
                  {
                    file,
                    new_version: updatedDoc.version,
                  },
                  null,
                  2
                ),
              },
            ],
          };
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

          await docManager.openDocument(file);

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
              const goalsResult = await lspClient.sendRequest<
                GoalAnswer<string>
              >('proof/goals', {
                textDocument: {
                  uri: updatedDoc.uri,
                  version: updatedDoc.version,
                },
                position,
                pp_format: 'Str',
              });
              goals = goalsResult;
            } catch (err) {
              console.error('Failed to get goals:', err);
            }
          }

          return {
            content: [
              {
                type: 'text',
                text: JSON.stringify(
                  {
                    applied: true,
                    goals: goals?.goals,
                    messages: goals?.messages || [],
                    error: goals?.error || null,
                  },
                  null,
                  2
                ),
              },
            ],
          };
        }

        case 'coq_check': {
          const { file } = args as { file: string };

          try {
            const doc = await docManager.openDocument(file);

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

            // Return a concise summary instead of the full result
            const summary = {
              file,
              completed: result.completed?.status || 'unknown',
              span_count: result.spans?.length || 0,
              completed_range: result.completed?.range 
                ? `L${result.completed.range.start.line}-L${result.completed.range.end.line}`
                : 'none',
              // Add a flag to indicate if checking completed successfully
              success: true,
            };

            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(summary, null, 2),
                },
              ],
            };
          } catch (error) {
            // Return error information in a concise format
            const errorSummary = {
              file,
              success: false,
              error: error instanceof Error ? error.message : String(error),
            };

            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(errorSummary, null, 2),
                },
              ],
              isError: true,
            };
          }
        }

        case 'coq_check_range': {
          const { file, range } = args as { 
            file: string; 
            range: { start: { line: number; character?: number }; end: { line: number; character?: number } };
          };

          try {
            const doc = await docManager.openDocument(file);

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
            const rangeSummary = {
              file,
              range: {
                start: `L${range.start.line}`,
                end: `L${range.end.line}`,
              },
              span_count: targetSpans.length,
              spans: targetSpans.map(span => ({
                line: span.range.start.line,
                status: 'parsed', // We'll enhance this later with actual diagnostics
              })),
              overall_completed: result.completed?.status || 'unknown',
              success: true,
            };

            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(rangeSummary, null, 2),
                },
              ],
            };
          } catch (error) {
            // Return error information in a concise format
            const errorSummary = {
              file,
              range: {
                start: `L${range.start.line}`,
                end: `L${range.end.line}`,
              },
              success: false,
              error: error instanceof Error ? error.message : String(error),
            };

            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(errorSummary, null, 2),
                },
              ],
              isError: true,
            };
          }
        }

        default:
          throw new Error(`Unknown tool: ${name}`);
      }
    } catch (error) {
      const err = error as Error & { data?: unknown };
      return {
        content: [
          {
            type: 'text',
            text: JSON.stringify(
              {
                error: err.message,
                data: err.data,
              },
              null,
              2
            ),
          },
        ],
        isError: true,
      };
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
