/**
 * Integration test harness for rocq-piler MCP tools.
 *
 * Uses the official MCP SDK client (StdioClientTransport) to spawn and
 * communicate with the real dist/index.js server process.
 */

import * as path from 'path';
import * as fs from 'fs';
import { fileURLToPath } from 'url';
import { Client } from '@modelcontextprotocol/sdk/client/index.js';
import { StdioClientTransport } from '@modelcontextprotocol/sdk/client/stdio.js';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

export const SERVER_PATH = path.resolve(__dirname, '../../dist/index.js');
export const COQ_LSP_PATH = process.env.COQ_LSP_PATH ?? '/home/gavin/.opam/rocq-9/bin/coq-lsp';
export const FIXTURES_DIR = path.resolve(__dirname, 'fixtures');

export function fixture(name: string): string {
  return path.join(FIXTURES_DIR, name);
}

/** Create a temp copy of a fixture inside the fixtures dir (so coq-lsp indexes it).
 *  Optional srcDir overrides the source directory (defaults to FIXTURES_DIR). */
export function tempFixture(name: string, suffix: string, srcDir?: string): string {
  const src = path.join(srcDir ?? FIXTURES_DIR, name);
  const dst = path.join(FIXTURES_DIR, `_tmp_${suffix}_${process.pid}.v`);
  fs.copyFileSync(src, dst);
  return dst;
}

export function removeTempFixture(p: string): void {
  try { fs.unlinkSync(p); } catch {}
}

export interface ToolResult {
  text: string;
  allText: string[];
  isError: boolean;
}

export class McpHarness {
  private client: Client;
  private transport: StdioClientTransport;

  constructor() {
    this.transport = new StdioClientTransport({
      command: 'node',
      args: [SERVER_PATH, '--coq-lsp-path', COQ_LSP_PATH],
    });
    this.client = new Client(
      { name: 'test-harness', version: '0.0.1' },
      { capabilities: {} }
    );
  }

  async connect(): Promise<void> {
    await this.client.connect(this.transport);
  }

  async callTool(name: string, args: Record<string, unknown>, timeoutMs = 90_000): Promise<ToolResult> {
    const signal = AbortSignal.timeout(timeoutMs);
    const result = await this.client.callTool({ name, arguments: args }, undefined, { signal }) as {
      content: Array<{ type: string; text: string }>;
      isError?: boolean;
    };
    const texts = (result.content ?? []).filter(c => c.type === 'text').map(c => c.text);
    return {
      text: texts[0] ?? '',
      allText: texts,
      isError: result.isError ?? false,
    };
  }

  async teardown(): Promise<void> {
    await this.client.close();
  }
}

export async function createHarness(): Promise<McpHarness> {
  const h = new McpHarness();
  await h.connect();
  return h;
}
