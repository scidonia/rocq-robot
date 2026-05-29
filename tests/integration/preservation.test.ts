/**
 * Integration tests for list_admitted on the PCF+Ref preservation proof.
 *
 * Verifies that list_admitted correctly queries goal states at admit. lines
 * (the character-position fix works), and that insert_tactic admit_hash
 * can replace matching admits.
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness, removeTempFixture, tempFixture, fixture, extractAdmitHashes } from './harness.js';

const TIMEOUT = 90_000;

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

describe('focus_proof on preservation', () => {
  const FIXTURE = fixture('preservation_stubs.v');

  // Warm up the file
  beforeAll(async () => {
    await h.callTool('check_file', { file: FIXTURE });
  }, TIMEOUT);

  it('finds 21 admits', async () => {
    const r = await h.callTool('focus_proof', { file: FIXTURE, name: 'preservation' });
    expect(r.isError).toBe(false);
    expect(extractAdmitHashes(r.text)).toHaveLength(21);
  });

  it('returns real hashes for bullet admits, not error', async () => {
    const r = await h.callTool('focus_proof', { file: FIXTURE, name: 'preservation' });
    const admits = extractAdmitHashes(r.text);
    expect(admits).toHaveLength(21);
    expect(admits.filter(a => a.hash === 'error')).toHaveLength(0);
  });

  it('at least one admit shows a goal text', async () => {
    const r = await h.callTool('focus_proof', { file: FIXTURE, name: 'preservation' });
    const admits = extractAdmitHashes(r.text);
    expect(admits.some(a => a.goal.length > 0 && a.goal !== '(no goals)')).toBe(true);
  });
});

describe('insert_tactic admit_hash on preservation', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('preservation_stubs.v', 'preserv');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('replaces first admit line via admit_hash', async () => {
    const list = await h.callTool('focus_proof', { file: tmpFile, name: 'preservation' });
    const hash = extractAdmitHashes(list.text)[0]?.hash;
    expect(hash).toBeTruthy();

    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'preservation',
      tactic: 'exact I.',
      admit_hash: hash,
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/replaced/);
  });
});
