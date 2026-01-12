/**
 * LSP client for communicating with rocq-lsp subprocess
 */

import { spawn, ChildProcessWithoutNullStreams } from 'child_process';
import { resolve as resolvePath } from 'path';
import { pathToFileURL } from 'url';
import {
  createMessageConnection,
  MessageConnection,
  StreamMessageReader,
  StreamMessageWriter,
} from 'vscode-jsonrpc/node.js';
import type {
  InitializeParams,
  InitializeResult,
} from 'vscode-languageserver-protocol';
import type { ServerConfig } from './types.js';

export class RocqLspClient {
  private process: ChildProcessWithoutNullStreams | null = null;
  private connection: MessageConnection | null = null;
  private config: Required<ServerConfig>;
  private nextRequestId = 1;

  constructor(config: ServerConfig) {
    this.config = {
      rocqLspPath: config.rocqLspPath || 'coq-lsp',
      rocqLspArgs: config.rocqLspArgs || [],
      workspaceRoot: resolvePath(config.workspaceRoot || process.cwd()),
      checkOnlyOnRequest: config.checkOnlyOnRequest ?? true,
      ppType: config.ppType ?? 0,
      goalAfterTactic: config.goalAfterTactic ?? true,
    };
  }

  async start(): Promise<void> {
    if (this.process) {
      throw new Error('LSP client already started');
    }

    // Log the command being executed for debugging
    console.error('[lsp-client] Starting LSP process:');
    console.error('[lsp-client]   Command:', this.config.rocqLspPath);
    console.error('[lsp-client]   Args:', this.config.rocqLspArgs);
    console.error('[lsp-client]   CWD:', this.config.workspaceRoot);

    // Spawn rocq-lsp process
    this.process = spawn(this.config.rocqLspPath, this.config.rocqLspArgs, {
      stdio: ['pipe', 'pipe', 'pipe'],
      cwd: this.config.workspaceRoot,
      env: process.env,
    });

    // Setup message connection
    const reader = new StreamMessageReader(this.process.stdout);
    const writer = new StreamMessageWriter(this.process.stdin);
    this.connection = createMessageConnection(reader, writer);

    // Handle errors
    this.process.stderr.on('data', (data) => {
      console.error('[rocq-lsp stderr]:', data.toString());
    });

    this.process.on('error', (err) => {
      console.error('[rocq-lsp process error]:', err);
    });

    this.process.on('exit', (code) => {
      console.error(`[rocq-lsp exited with code ${code}]`);
      this.connection = null;
      this.process = null;
    });

    // Start listening
    this.connection.listen();

    // Initialize LSP
    await this.initialize();
  }

  private async initialize(): Promise<void> {
    if (!this.connection) {
      throw new Error('Connection not established');
    }

    const rootUri = pathToFileURL(this.config.workspaceRoot).toString();

    const initParams: InitializeParams = {
      processId: process.pid,
      rootUri,
      capabilities: {
        textDocument: {
          synchronization: {
            dynamicRegistration: false,
            willSave: false,
            willSaveWaitUntil: false,
            didSave: true,
          },
        },
      },
      workspaceFolders: [
        {
          uri: rootUri,
          name: 'workspace',
        },
      ],
      initializationOptions: {
        check_only_on_request: this.config.checkOnlyOnRequest,
        pp_type: this.config.ppType,
        goal_after_tactic: this.config.goalAfterTactic,
      },
    };

    const result = await this.connection.sendRequest<InitializeResult>(
      'initialize',
      initParams
    );

    console.error('[LSP initialized]:', result.serverInfo);

    // Send initialized notification
    await this.connection.sendNotification('initialized', {});
  }

  async shutdown(): Promise<void> {
    if (this.connection) {
      await this.connection.sendRequest('shutdown', null);
      await this.connection.sendNotification('exit', null);
      this.connection.dispose();
      this.connection = null;
    }

    if (this.process) {
      this.process.kill();
      this.process = null;
    }
  }

  /**
   * Send a JSON-RPC request to rocq-lsp
   */
  async sendRequest<T>(method: string, params: unknown): Promise<T> {
    if (!this.connection) {
      throw new Error('LSP client not started');
    }

    return this.connection.sendRequest<T>(method, params);
  }

  /**
   * Send a JSON-RPC notification to rocq-lsp
   */
  async sendNotification(method: string, params: unknown): Promise<void> {
    if (!this.connection) {
      throw new Error('LSP client not started');
    }

    await this.connection.sendNotification(method, params);
  }

  isRunning(): boolean {
    return this.connection !== null && this.process !== null;
  }
}
