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

/**
 * Extract admit hashes from a focus_proof or insert_tactic response.
 * The admits section now looks like:
 *   -- admits (N) ----------
 *     abc12345  L7:
 *       hyps: n : nat; IHn : n + 0 = n
 *       goal: True /\ True
 *
 * Also handles the old single-line format for backward compat:
 *     abc12345  L7: True /\ True
 */
export function extractAdmitHashes(focusText: string): Array<{ hash: string; line: number; goal: string; hyps: string }> {
  const result: Array<{ hash: string; line: number; goal: string; hyps: string }> = [];
  const section = focusText.includes('-- admits')
    ? focusText.split('-- admits')[1] ?? ''
    : focusText.includes('admit(s) remaining:')
    ? focusText.split('admit(s) remaining:')[1] ?? ''
    : '';
  if (!section) return result;

  const lines = section.split('\n');
  let i = 0;
  while (i < lines.length) {
    const line = lines[i];
    // Match "  abc12345  L7:" (new format) or "  abc12345  L7: goal text" (old format)
    const m = line.match(/([0-9a-f]{8})\s+L(\d+):(.*)$/);
    if (m) {
      const hash = m[1];
      const lineNum = parseInt(m[2]);
      const rest = m[3].trim();
      let goal = rest;
      let hyps = '';
      if (!rest) {
        // New multi-line format — look ahead for hyps/goal lines
        i++;
        while (i < lines.length) {
          const inner = lines[i].trim();
          if (inner.startsWith('hyps:')) {
            hyps = inner.slice('hyps:'.length).trim();
            i++;
          } else if (inner.startsWith('goal:')) {
            goal = inner.slice('goal:'.length).trim();
            i++;
          } else if (inner.startsWith('^')) {
            i++; // hint line, skip
          } else {
            break; // next admit entry — don't increment, outer loop will process it
          }
        }
        // i now points at next hash line or end — do NOT increment below
        result.push({ hash, line: lineNum, goal, hyps });
        continue;
      }
      result.push({ hash, line: lineNum, goal, hyps });
    }
    i++;
  }
  return result;
}
