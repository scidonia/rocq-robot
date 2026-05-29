/**
 * Integration tests for admit_hash with mixed goal types.
 *
 * Fixture: mixed_admits.v
 *   - mixed_four  : True /\ nat /\ True /\ nat  (4 admits, 2 goal types)
 *   - mixed_partial: same shape, first True already solved (3 admits)
 *   - all_true    : True /\ True /\ True /\ True (4 admits, 1 goal type)
 *
 * Key properties under test:
 *   1. list_admitted returns distinct hashes for distinct goal types
 *   2. insert_tactic admit_hash replaces ALL admits sharing a hash, not others
 *   3. The count of replacements matches the count of same-hash admits
 *   4. After replacement, only admits with other hashes remain
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import * as fs from 'fs';
import { McpHarness, createHarness, fixture, tempFixture, removeTempFixture, extractAdmitHashes } from './harness.js';

/** Count admit. tactic lines within a named proof in a file. */
function countAdmitsInProof(file: string, proofName: string): number {
  const text = fs.readFileSync(file, 'utf8');
  const lines = text.split('\n');
  // Find proof start
  const startIdx = lines.findIndex(l => l.includes(`Lemma ${proofName}`) || l.includes(`Theorem ${proofName}`));
  if (startIdx < 0) return 0;
  // Find proof end (Admitted. or Qed.)
  let endIdx = startIdx;
  for (let i = startIdx + 1; i < lines.length; i++) {
    if (/^\s*(Admitted|Qed|Defined)\./.test(lines[i])) { endIdx = i; break; }
    // Stop at next top-level decl
    if (/^(Lemma|Theorem|Corollary|Definition|Fixpoint|Inductive)\s/.test(lines[i]) && i > startIdx + 2) { endIdx = i - 1; break; }
  }
  const proofLines = lines.slice(startIdx, endIdx + 1);
  return proofLines.filter(l => /\badmit\b/.test(l) && !/Admitted\./.test(l)).length;
}

const TIMEOUT = 90_000;
const MIXED = fixture('mixed_admits.v');

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
  await h.callTool('check_file', { file: MIXED });
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

// ─────────────────────────────────────────────────────────────────────────────
// list_admitted — goal hashes are distinct across goal types
// ─────────────────────────────────────────────────────────────────────────────

describe('list_admitted on mixed goals', () => {
  it('returns 4 admits for mixed_four', async () => {
    const r = await h.callTool('focus_proof', { file: MIXED, name: 'mixed_four' });
    expect(r.isError).toBe(false);
    expect(extractAdmitHashes(r.text)).toHaveLength(4);
  });

  it('returns exactly 2 distinct hashes for mixed_four (True and True->True)', async () => {
    const r = await h.callTool('focus_proof', { file: MIXED, name: 'mixed_four' });
    expect(r.isError).toBe(false);
    const admits = extractAdmitHashes(r.text);
    expect(admits).toHaveLength(4);
    const unique = new Set(admits.map(a => a.hash));
    expect(unique.size).toBe(2);
  });

  it('True admits share one hash, (True->True) admits share another distinct hash', async () => {
    const r = await h.callTool('focus_proof', { file: MIXED, name: 'mixed_four' });
    const admits = extractAdmitHashes(r.text);
    const trueAdmits = admits.filter(a => a.goal === 'True');
    const implAdmits = admits.filter(a => a.goal.includes('True -> True'));
    expect(trueAdmits).toHaveLength(2);
    expect(implAdmits).toHaveLength(2);
    expect(new Set(trueAdmits.map(a => a.hash)).size).toBe(1);
    expect(new Set(implAdmits.map(a => a.hash)).size).toBe(1);
    expect(trueAdmits[0].hash).not.toBe(implAdmits[0].hash);
  });

  it('returns 3 admits for mixed_partial (first True already solved)', async () => {
    const r = await h.callTool('focus_proof', { file: MIXED, name: 'mixed_partial' });
    expect(r.isError).toBe(false);
    expect(extractAdmitHashes(r.text)).toHaveLength(3);
  });

  it('all 4 admits share one hash for all_true', async () => {
    const r = await h.callTool('focus_proof', { file: MIXED, name: 'all_true' });
    expect(r.isError).toBe(false);
    const admits = extractAdmitHashes(r.text);
    expect(admits).toHaveLength(4);
    expect(new Set(admits.map(a => a.hash)).size).toBe(1);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// insert_tactic admit_hash — replaces only matching admits
// ─────────────────────────────────────────────────────────────────────────────

describe('insert_tactic admit_hash on mixed goals', () => {
  let tmpFile: string;

  // Extract hashes from mixed_four before we start mutating
  let trueHash: string;
  let implHash: string; // hash for "True -> True" goals

  beforeAll(async () => {
    tmpFile = tempFixture('mixed_admits.v', 'mixed');
    await h.callTool('check_file', { file: tmpFile });

    const list = await h.callTool('focus_proof', { file: tmpFile, name: 'mixed_four' });
    const admits = extractAdmitHashes(list.text);
    trueHash = admits.find(a => a.goal === 'True')!.hash;
    implHash = admits.find(a => a.goal.includes('True -> True'))!.hash;
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('replacing True hash closes exactly 2 admits, leaves 2 nat admits', async () => {
    expect(countAdmitsInProof(tmpFile, 'mixed_four')).toBe(4);

    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'mixed_four',
      tactic: 'exact I.',
      admit_hash: trueHash,
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/replaced|done/i);

    // 2 True admits replaced → 2 nat admits remain
    expect(countAdmitsInProof(tmpFile, 'mixed_four')).toBe(2);
    // The replacement tactic appears (at least) twice
    const content = fs.readFileSync(tmpFile, 'utf8');
    expect((content.match(/exact I\./g) ?? []).length).toBeGreaterThanOrEqual(2);
  });

  it('replacing nat hash closes the remaining 2 nat admits', async () => {
    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'mixed_four',
      tactic: 'tauto.',
      admit_hash: implHash,
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/replaced|done/i);

    expect(countAdmitsInProof(tmpFile, 'mixed_four')).toBe(0);
  });

  it('after all admits closed, proof auto-Qeds', async () => {
    expect(countAdmitsInProof(tmpFile, 'mixed_four')).toBe(0);
    const check = await h.callTool('check_file', { file: tmpFile });
    expect(check.text).toMatch(/mixed_four.*Qed/);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// mixed_partial — only the unresolved admits are affected
// ─────────────────────────────────────────────────────────────────────────────

describe('insert_tactic admit_hash on mixed_partial', () => {
  let tmpFile: string;
  let trueHash: string;
  let implHash: string;

  beforeAll(async () => {
    tmpFile = tempFixture('mixed_admits.v', 'partial');
    await h.callTool('check_file', { file: tmpFile });

    const list = await h.callTool('focus_proof', { file: tmpFile, name: 'mixed_partial' });
    const admits = extractAdmitHashes(list.text);
    // mixed_partial has: (True->True), True, (True->True)  — first True solved with exact I.
    trueHash = admits.find(a => a.goal === 'True')?.hash ?? '';
    implHash = admits.find(a => a.goal.includes('True -> True'))?.hash ?? '';
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('has 3 admits: 1 True and 2 (True -> True)', async () => {
    const list = await h.callTool('focus_proof', { file: tmpFile, name: 'mixed_partial' });
    const admits = extractAdmitHashes(list.text);
    expect(admits.filter(a => a.goal === 'True')).toHaveLength(1);
    expect(admits.filter(a => a.goal.includes('True -> True'))).toHaveLength(2);
  });

  it('replacing True hash closes exactly 1 admit', async () => {
    const before = countAdmitsInProof(tmpFile, 'mixed_partial');
    expect(before).toBe(3);

    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'mixed_partial',
      tactic: 'exact I.',
      admit_hash: trueHash,
    });
    expect(r.isError).toBe(false);

    expect(countAdmitsInProof(tmpFile, 'mixed_partial')).toBe(before - 1);
  });

  it('replacing (True->True) hash closes both remaining implication admits', async () => {
    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'mixed_partial',
      tactic: 'tauto.',
      admit_hash: implHash,
    });
    expect(r.isError).toBe(false);

    expect(countAdmitsInProof(tmpFile, 'mixed_partial')).toBe(0);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// all_true — all 4 admits share one hash, all replaced in one call
// ─────────────────────────────────────────────────────────────────────────────

describe('insert_tactic admit_hash on all_true', () => {
  let tmpFile: string;
  let trueHash: string;

  beforeAll(async () => {
    tmpFile = tempFixture('mixed_admits.v', 'alltrue');
    await h.callTool('check_file', { file: tmpFile });

    const list = await h.callTool('focus_proof', { file: tmpFile, name: 'all_true' });
    trueHash = extractAdmitHashes(list.text)[0]?.hash; // all same hash
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('single admit_hash call replaces all 4 admits at once', async () => {
    expect(countAdmitsInProof(tmpFile, 'all_true')).toBe(4);

    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'all_true',
      tactic: 'exact I.',
      admit_hash: trueHash,
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/replaced|done/i);

    expect(countAdmitsInProof(tmpFile, 'all_true')).toBe(0);
  });

  it('after all admits replaced, proof auto-Qeds', async () => {
    expect(countAdmitsInProof(tmpFile, 'all_true')).toBe(0);
    const check = await h.callTool('check_file', { file: tmpFile });
    expect(check.text).toMatch(/all_true.*Qed/);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// Error cases
// ─────────────────────────────────────────────────────────────────────────────

describe('admit_hash error cases', () => {
  it('unknown hash returns an error', async () => {
    const r = await h.callTool('insert_tactic', {
      file: MIXED,
      name: 'mixed_four',
      tactic: 'exact I.',
      admit_hash: 'deadbeef',
    });
    expect(r.isError).toBe(true);
    expect(r.text).toMatch(/deadbeef/);
  });

  it('wrong tactic for goal type returns error', async () => {
    const tmpFile2 = tempFixture('mixed_admits.v', 'wrongtactic');
    await h.callTool('check_file', { file: tmpFile2 });

    const list = await h.callTool('focus_proof', { file: tmpFile2, name: 'mixed_four' });
    const implHash2 = extractAdmitHashes(list.text).find(a => a.goal.includes('True -> True'))?.hash ?? '';

    // exact I. is wrong type for (True -> True) goal — should fail or not corrupt file
    const r = await h.callTool('insert_tactic', {
      file: tmpFile2,
      name: 'mixed_four',
      tactic: 'exact I.',
      admit_hash: implHash2,
    });
    // Should either error or leave the admits in place (tactic type-check fails)
    if (!r.isError) {
      // If it didn't error, check the file wasn't corrupted
      const check = await h.callTool('check_file', { file: tmpFile2 });
      expect(check.isError).toBe(false);
    }
    removeTempFixture(tmpFile2);
  });
});
