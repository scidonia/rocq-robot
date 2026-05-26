/**
 * LSP client for communicating with rocq-lsp subprocess
 */

import { spawn, ChildProcessWithoutNullStreams } from 'child_process';
import { resolve as resolvePath } from 'path';
import { pathToFileURL } from 'url';
import { appendFileSync } from 'fs';
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

const DBG = '/tmp/mcp-coq-lsp-debug.log';
function dbg(msg: string) {
  appendFileSync(DBG, `[${new Date().toISOString()}] ${msg}\n`);
}

export class RocqLspClient {
  private process: ChildProcessWithoutNullStreams | null = null;
  private connection: MessageConnection | null = null;
  private ready = false;
  private restarting = false;
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

    dbg('start() begin  pid=' + (this.process && (this.process as any).pid) + ' ready=' + this.ready + ' restarting=' + this.restarting);
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
    dbg('start() spawned pid=' + this.process.pid);

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

    const proc = this.process; // capture ref to prevent stale handler
    proc.on('exit', (code) => {
      dbg('exit handler: pid=' + proc.pid + ' code=' + code + ' currentPid=' + (this.process?.pid ?? 0));
      if (this.process !== proc) {
        dbg('exit handler: IGNORING stale exit for pid=' + proc.pid);
        return;
      }
      console.error(`[rocq-lsp exited with code ${code}]`);
      this.ready = false;
      if (this.connection) {
        this.connection.dispose();
        this.connection = null;
      }
      this.process = null;
    });

    // Start listening
    this.connection.listen();
    dbg('start() connection listening');

    // Initialize LSP
    dbg('start() calling initialize()');
    await this.initialize();
    this.ready = true;
    dbg('start() DONE ready=true');
    console.error('[lsp-client] LSP client ready');
  }

  private async initialize(): Promise<void> {
    if (!this.connection) {
      dbg('initialize() FAIL connection is null');
      throw new Error('Connection not established');
    }

    const rootUri = pathToFileURL(this.config.workspaceRoot).toString();
    dbg('initialize() sending initialize request to ' + rootUri);

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

    dbg('initialize() request sent, awaiting response');
    const result = await this.connection.sendRequest<InitializeResult>(
      'initialize',
      initParams
    );

    dbg('initialize() got response: ' + JSON.stringify(result.serverInfo));

    console.error('[LSP initialized]:', result.serverInfo);

    // Send initialized notification
    await this.connection.sendNotification('initialized', {});
    dbg('initialize() DONE');
  }

  async shutdown(): Promise<void> {
    await this.stop();
  }

  /**
   * Stop the LSP client without cleaning up config (for restart)
   */
  async stop(): Promise<void> {
    dbg('stop() begin  pid=' + (this.process?.pid ?? 0) + ' ready=' + this.ready + ' restarting=' + this.restarting);
    this.ready = false;
    if (this.connection) {
      this.connection.dispose();
      this.connection = null;
    }

    if (this.process) {
      this.process.kill('SIGKILL');
      this.process = null;
    }
    dbg('stop() DONE');
  }

  /**
   * Restart the LSP process, optionally with new config overrides
   */
  async restart(config?: Partial<ServerConfig>): Promise<void> {
    dbg('restart() ENTER  pid=' + (this.process?.pid ?? 0) + ' ready=' + this.ready + ' restarting=' + this.restarting + ' root=' + (config?.workspaceRoot ?? 'none'));
    if (this.restarting) {
      dbg('restart() already in progress, waiting for ready');
      console.error('[lsp-client] Restart already in progress, waiting...');
      await this.waitUntilReady(30000);
      dbg('restart() DONE after wait');
      return;
    }
    this.restarting = true;
    try {
      try {
        await this.stop();
      } catch (e) {
        // Ignore stop errors
      }

      // Clear nextRequestId to avoid large request IDs accumulating
      this.nextRequestId = 1;

      if (config) {
        if (config.workspaceRoot !== undefined) {
          this.config.workspaceRoot = resolvePath(config.workspaceRoot);
        }
        if (config.rocqLspPath !== undefined) {
          this.config.rocqLspPath = config.rocqLspPath;
        }
        if (config.rocqLspArgs !== undefined) {
          this.config.rocqLspArgs = config.rocqLspArgs;
        }
        if (config.checkOnlyOnRequest !== undefined) {
          this.config.checkOnlyOnRequest = config.checkOnlyOnRequest;
        }
        if (config.ppType !== undefined) {
          this.config.ppType = config.ppType;
        }
        if (config.goalAfterTactic !== undefined) {
          this.config.goalAfterTactic = config.goalAfterTactic;
        }
      }

      await this.start();
    } finally {
      this.restarting = false;
      dbg('restart() DONE FINALLY  ready=' + this.ready + ' pid=' + (this.process?.pid ?? 0));
    }
  }

  /**
   * Wait until the LSP connection is ready (connection established)
   */
  async waitUntilReady(timeoutMs: number = 30000): Promise<void> {
    const deadline = Date.now() + timeoutMs;
    let logged = false;
    while (!this.ready) {
      if (!logged) {
        dbg('waitUntilReady() waiting  restarting=' + this.restarting + ' pid=' + (this.process?.pid ?? 0));
        logged = true;
      }
      await new Promise(r => setTimeout(r, 200));
      if (Date.now() >= deadline) {
        dbg('waitUntilReady() TIMEOUT  ready=' + this.ready + ' restarting=' + this.restarting + ' pid=' + (this.process?.pid ?? 0));
        throw new Error('LSP client not started');
      }
    }
    dbg('waitUntilReady() OK  ready=true  pid=' + (this.process?.pid ?? 0));
  }

  /**
   * Send a JSON-RPC request to rocq-lsp
   */
  async sendRequest<T>(method: string, params: unknown, timeoutMs = 15000): Promise<T> {
    if (!this.ready || !this.connection) {
      throw new Error('LSP client not started');
    }

    const result = await Promise.race([
      this.connection.sendRequest<T>(method, params),
      new Promise<never>((_, reject) =>
        setTimeout(() => reject(new Error(`LSP request timeout: ${method}`)), timeoutMs)
      ),
    ]);
    return result;
  }

  /**
   * Send a JSON-RPC notification to rocq-lsp
   */
  async sendNotification(method: string, params: unknown): Promise<void> {
    if (!this.ready || !this.connection) {
      throw new Error('LSP client not started');
    }

    await this.connection.sendNotification(method, params);
  }

  isRunning(): boolean {
    return this.connection !== null && this.process !== null;
  }
}
