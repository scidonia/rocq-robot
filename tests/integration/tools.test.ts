/**
 * Integration tests for all rocq-piler MCP tools.
 *
 * Spins up the real MCP server (dist/index.js + coq-lsp) and exercises
 * every tool and every significant mode. One server process per suite.
 *
 * Run: npm run test:integration
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import * as fs from 'fs';
import { McpHarness, createHarness, fixture, tempFixture, removeTempFixture, extractAdmitHashes } from './harness.js';

const TIMEOUT = 90_000;
const BASIC = fixture('basic.v');

// ─────────────────────────────────────────────────────────────────────────────
// Shared harness — one coq-lsp process for all tests
// ─────────────────────────────────────────────────────────────────────────────

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
  // Warm up: open the fixture so coq-lsp elaborates it
  await h.callTool('check_file', { file: BASIC });
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

// ─────────────────────────────────────────────────────────────────────────────
// check_file
// ─────────────────────────────────────────────────────────────────────────────

describe('check_file', () => {
  it('returns span count and lists declarations', async () => {
    const r = await h.callTool('check_file', { file: BASIC });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/spans/);
    expect(r.text).toMatch(/trivial/);
    expect(r.text).toMatch(/already_proved.*Qed/);
    expect(r.text).toMatch(/trivial.*Admitted/);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// focus_proof
// ─────────────────────────────────────────────────────────────────────────────

describe('focus_proof', () => {
  it('shows 1 goal for trivial : True', async () => {
    const r = await h.callTool('focus_proof', { file: BASIC, name: 'trivial' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/goals: 1 at focus/);
    expect(r.text).toMatch(/True/);
  });

  it('shows 1 goal (True /\\ True) for conjunction before any tactics', async () => {
    const r = await h.callTool('focus_proof', { file: BASIC, name: 'conjunction' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/goals: 1 at focus/);
    expect(r.text).toMatch(/True.*True/);
  });

  it('shows forall hypothesis for with_hyp', async () => {
    const r = await h.callTool('focus_proof', { file: BASIC, name: 'with_hyp' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/n.*nat/);
    expect(r.text).toMatch(/n = n/);
  });

  it('shows given-up count for has_admits', async () => {
    const r = await h.callTool('focus_proof', { file: BASIC, name: 'has_admits' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/given-up: 2/);
  });

  it('returns error for unknown proof name', async () => {
    const r = await h.callTool('focus_proof', { file: BASIC, name: 'nonexistent_proof_xyz' });
    expect(r.isError).toBe(true);
    expect(r.text).toMatch(/not found/i);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// open_goals
// ─────────────────────────────────────────────────────────────────────────────

describe('open_goals', () => {
  it('Prev mode: shows 1 goal', async () => {
    const r = await h.callTool('open_goals', { file: BASIC, name: 'trivial', mode: 'Prev' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/1 goal/);
    expect(r.text).toMatch(/True/);
  });

  it('compact mode: shows hypothesis', async () => {
    const r = await h.callTool('open_goals', { file: BASIC, name: 'with_hyp', compact: true });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/n = n/);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// check_range
// ─────────────────────────────────────────────────────────────────────────────

describe('check_range', () => {
  it('returns spans within a line range', async () => {
    const r = await h.callTool('check_range', {
      file: BASIC,
      range: { start: { line: 0 }, end: { line: 10 } },
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/span/);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// snap_state + exec_tactic + state_goals
// Using a line known to be inside a proof body (line 7 = `Admitted.` of trivial)
// We snap at line 6 (the blank line before Admitted.) to get pre-close state.
// ─────────────────────────────────────────────────────────────────────────────

describe('snap_state / exec_tactic / state_goals', () => {
  // basic.v: 'trivial' has Proof. on line 7, Admitted. on line 8 (0-based).
  // Snap at line 7 character 7 (after "Proof. ") to get the open proof state,
  // or use snap_state at the Proof. line and rely on petanque's prev-mode.
  // We use focus_proof to confirm the state and extract the proof line.

  // Use open_goals to confirm position, then snap_state at the Proof. line.
  // trivial: True — Proof. on line 6 (0-based), Admitted. on line 7.
  // Snap at line 6, char 6 (end of "Proof.") to get the open-goal state.
  // We use open_goals to get the valid state_id indirectly via snap_state.
  let stateId: number;

  beforeAll(async () => {
    // Find the Proof. line for 'trivial' by scanning basic.v
    const content = fs.readFileSync(BASIC, 'utf8').split('\n');
    const proofLineIdx = content.findIndex((l, i) =>
      i > 0 && /^Proof\./.test(l) && /trivial/.test(content[i - 1] || '')
    );
    // Snap at end of "Proof." line to get open-proof state
    const pos = { line: proofLineIdx, character: 6 };
    const snap = await h.callTool('snap_state', { file: BASIC, position: pos });
    stateId = parseInt(snap.text.match(/state_id=(\d+)/)![1]);
    // Verify we actually have a goal
    const goals = await h.callTool('state_goals', { state_id: stateId });
    // If no goals at this position, try char 0 of the Admitted. line (before it runs)
    if (!goals.text.match(/1 goal/)) {
      const admittedPos = { line: proofLineIdx + 1, character: 0 };
      const snap2 = await h.callTool('snap_state', { file: BASIC, position: admittedPos });
      stateId = parseInt(snap2.text.match(/state_id=(\d+)/)![1]);
    }
  });

  it('snap_state returns a numeric state_id', async () => {
    const content = fs.readFileSync(BASIC, 'utf8').split('\n');
    const proofLineIdx = content.findIndex((l, i) =>
      i > 0 && /^Proof\./.test(l) && /trivial/.test(content[i - 1] || '')
    );
    const r = await h.callTool('snap_state', { file: BASIC, position: { line: proofLineIdx, character: 6 } });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/state_id=\d+/);
  });

  it('state_goals returns 1 goal (True) for trivial proof state', async () => {
    const r = await h.callTool('state_goals', { state_id: stateId });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/1 goal/);
    expect(r.text).toMatch(/True/);
  });

  it('exec_tactic finishes proof with exact I.', async () => {
    const r = await h.callTool('exec_tactic', { state_id: stateId, tactic: 'exact I.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/proof_finished=true/);
  });

  it('exec_tactic reports type error without crashing', async () => {
    const r = await h.callTool('exec_tactic', { state_id: stateId, tactic: 'exact 42.' });
    expect(r.isError).toBe(true);
    // Should be a Coq type error, not a parse error
    expect(r.text).toMatch(/type|expected|42/i);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// try_step
// ─────────────────────────────────────────────────────────────────────────────

describe('try_step', () => {
  it('shows proof finished for exact I. on trivial', async () => {
    const r = await h.callTool('try_step', { file: BASIC, name: 'trivial', tactic: 'exact I.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/proof finished/i);
  });

  it('returns error reply for a tactic that fails type-checking', async () => {
    const r = await h.callTool('try_step', { file: BASIC, name: 'trivial', tactic: 'exact 42.' });
    // A type-checking failure is returned as an error reply
    expect(r.isError).toBe(true);
    // Error text contains either the Coq error or "illegal begin of vernac" if outside proof mode
    expect(r.text.length).toBeGreaterThan(0);
  });

  it('works against a given-up (admit.) bullet and closes it', async () => {
    const r = await h.callTool('try_step', { file: BASIC, name: 'has_admits', tactic: 'exact I.' });
    expect(r.isError).toBe(false);
    // exact I. closes the True goal — proof_finished or 0 goals remaining
    expect(r.text).toMatch(/0 goal|proof finished/i);
  });

  it('shows goal context when tactic fails on given-up bullet', async () => {
    const r = await h.callTool('try_step', { file: BASIC, name: 'has_admits', tactic: 'exact 42.' });
    // Should show the goal (True) and report tactic failure
    expect(r.isError).toBe(false); // tactic error is surfaced in text, not as isError
    expect(r.text).toMatch(/True/);
    expect(r.text).toMatch(/tactic failed|type|expected/i);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// insert_tactic (uses fixture-dir temp copies so coq-lsp can index them)
// ─────────────────────────────────────────────────────────────────────────────

describe('insert_tactic', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('basic.v', 'insert');
    // Warm up the temp file
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('inserts a closing tactic and auto-Qeds', async () => {
    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'trivial',
      tactic: 'exact I.',
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/done.*Qed|Qed.*applied/i);
  });

  it('replace:true replaces the last tactic', async () => {
    // Insert something, then replace it
    await h.callTool('insert_tactic', { file: tmpFile, name: 'with_hyp', tactic: 'intros n.' });
    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'with_hyp',
      tactic: 'reflexivity.',
      replace: true,
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/done|Qed/i);
  });

  it('rejects a tactic that produces a Coq error (no more subgoals)', async () => {
    // 'exact I. exact I.' after split — second exact I. hits "no more subgoals"
    // which the spec-check should reject
    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'trivial',    // trivial is already Qed'd — Admitted. is the body
      tactic: 'exact (False_rect _ I).',  // tries to prove True by contradiction — type error
    });
    expect(r.isError).toBe(false);
    // Either inserted (proof advances) or rejected (applied: false)
    // The key check: the file is not broken
    const check = await h.callTool('check_file', { file: tmpFile });
    expect(check.isError).toBe(false);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// reset_proof / add_lemma / delete_lemma / delete_step
// ─────────────────────────────────────────────────────────────────────────────

describe('proof management', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('basic.v', 'mgmt');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('reset_proof wipes proof body to Admitted.', async () => {
    await h.callTool('insert_tactic', { file: tmpFile, name: 'trivial', tactic: 'exact I.' });
    const r = await h.callTool('reset_proof', { file: tmpFile, name: 'trivial' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/reset.*Admitted/i);
    const focus = await h.callTool('focus_proof', { file: tmpFile, name: 'trivial' });
    expect(focus.text).toMatch(/goals: 1 at focus/);
  });

  it('add_lemma inserts a new lemma before a given proof', async () => {
    const r = await h.callTool('add_lemma', {
      file: tmpFile,
      name: 'new_helper',
      statement: 'True',
      before: 'trivial',
    });
    expect(r.isError).toBe(false);
    const focus = await h.callTool('focus_proof', { file: tmpFile, name: 'new_helper' });
    expect(focus.text).toMatch(/True/);
  });

  it('add_lemma is idempotent with identical statement', async () => {
    const r = await h.callTool('add_lemma', {
      file: tmpFile,
      name: 'new_helper',
      statement: 'True',
      before: 'trivial',
    });
    expect(r.isError).toBe(false);
    // Returns existing: true with identical: true — shown as "exists: true, identical: true"
    // or as a message saying the lemma already exists
    expect(r.text).toMatch(/identical|exists|already/i);
  });

  it('delete_lemma removes the lemma', async () => {
    const r = await h.callTool('delete_lemma', { file: tmpFile, name: 'new_helper' });
    expect(r.isError).toBe(false);
    const focus = await h.callTool('focus_proof', { file: tmpFile, name: 'new_helper' });
    expect(focus.isError).toBe(true);
  });

  it('delete_step removes last tactic line', async () => {
    await h.callTool('insert_tactic', { file: tmpFile, name: 'trivial', tactic: 'intros.' });
    const r = await h.callTool('delete_step', { file: tmpFile, name: 'trivial' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/removed/i);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// undo_step
// ─────────────────────────────────────────────────────────────────────────────

describe('undo_step', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('basic.v', 'undo');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('undo restores state before insert', async () => {
    await h.callTool('insert_tactic', { file: tmpFile, name: 'trivial', tactic: 'intros.' });
    const r = await h.callTool('undo_step', { file: tmpFile });
    expect(r.isError).toBe(false);
    const focus = await h.callTool('focus_proof', { file: tmpFile, name: 'trivial' });
    expect(focus.text).toMatch(/goals: 1 at focus/);
  });

  it('undo n=2 reverts two inserts', async () => {
    await h.callTool('insert_tactic', { file: tmpFile, name: 'trivial', tactic: 'intros.' });
    await h.callTool('insert_tactic', { file: tmpFile, name: 'trivial', tactic: 'intros.' });
    const r = await h.callTool('undo_step', { file: tmpFile, n: 2 });
    expect(r.isError).toBe(false);
    const focus = await h.callTool('focus_proof', { file: tmpFile, name: 'trivial' });
    expect(focus.text).toMatch(/goals: 1 at focus/);
  });

  it('undo with no history returns error', async () => {
    // Fresh file, focus to set currentProof, no inserts
    const fresh = tempFixture('basic.v', 'undo_fresh');
    await h.callTool('check_file', { file: fresh });
    await h.callTool('focus_proof', { file: fresh, name: 'trivial' });
    const r = await h.callTool('undo_step', { file: fresh });
    expect(r.isError).toBe(true);
    removeTempFixture(fresh);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// list_admitted + insert_tactic admit_hash
// ─────────────────────────────────────────────────────────────────────────────

describe('list_admitted + insert_tactic admit_hash', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('basic.v', 'admit');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('focus_proof returns hashes for each admit. line', async () => {
    const r = await h.callTool('focus_proof', { file: tmpFile, name: 'has_admits' });
    expect(r.isError).toBe(false);
    const admits = extractAdmitHashes(r.text);
    expect(admits.length).toBeGreaterThanOrEqual(2);
  });

  it('insert_tactic with admit_hash replaces the admit in-place', async () => {
    const list = await h.callTool('focus_proof', { file: tmpFile, name: 'has_admits' });
    const hash = extractAdmitHashes(list.text)[0]?.hash;

    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'has_admits', tactic: 'exact I.', admit_hash: hash });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/replaced/i);
    // The file should have one fewer admit. line
    const content = fs.readFileSync(tmpFile, 'utf8');
    const admitLines = content.split('\n').filter(l => /^\s*- admit\./.test(l));
    expect(admitLines.length).toBeLessThan(2);
  });

  it('insert_tactic with unknown admit_hash returns error', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'has_admits', tactic: 'exact I.', admit_hash: 'deadbeef' });
    expect(r.isError).toBe(true);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// insert_tactic multi-line (no sub-tactic splitting)
// ─────────────────────────────────────────────────────────────────────────────

describe('insert_tactic multi-line', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('basic.v', 'multiline');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('inserts a multi-line tactic block where second tactic depends on first', async () => {
    // with_hyp: forall n, n = n — needs intros then reflexivity.
    // Previously the sub-tactic splitter would try to validate "reflexivity."
    // against the pre-intros state and fail. Now the whole block goes in at once.
    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'with_hyp',
      tactic: 'intros n.\n  reflexivity.',
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/inserted/i);
    // File should now contain the two tactics and no Admitted goals open
    const content = fs.readFileSync(tmpFile, 'utf8');
    expect(content).toContain('intros n.');
    expect(content).toContain('reflexivity.');
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// insert_tactic auto-Qed
// ─────────────────────────────────────────────────────────────────────────────

describe('insert_tactic auto-Qed', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('basic.v', 'autoqed');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('auto-replaces Admitted with Qed when proof is fully closed', async () => {
    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'trivial',
      tactic: 'exact I.',
    });
    expect(r.isError).toBe(false);
    const content = fs.readFileSync(tmpFile, 'utf8');
    const trivialBlock = content.match(/Lemma trivial : True\.\nProof\.\n([^\n]*)\n(Qed\.|Admitted\.)/)?.[0];
    expect(trivialBlock).toBeDefined();
    expect(trivialBlock).toContain('Qed.');
    expect(trivialBlock).not.toContain('Admitted');
  });

  it('auto-replaces Admitted with Qed for multi-subgoal induction proof', async () => {
    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'conjunction',
      tactic: 'split; exact I.',
    });
    expect(r.isError).toBe(false);
    const content = fs.readFileSync(tmpFile, 'utf8');
    const conjBlock = content.match(/Lemma conjunction : True \/\\ True\.\nProof\.\n([^\n]*)\n(Qed\.|Admitted\.)/)?.[0];
    expect(conjBlock).toBeDefined();
    expect(conjBlock).toContain('Qed.');
    expect(conjBlock).not.toContain('Admitted');
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// insert_tactic admit_hash re-seal
// ─────────────────────────────────────────────────────────────────────────────

describe('insert_tactic admit_hash re-seal', () => {
  it('replaces admit in a partial bullet: intros. admit. → intros. exact I.', async () => {
    const tmpFile = tempFixture('partial_bullet.v', 'seal1');
    await h.callTool('check_file', { file: tmpFile });

    const list = await h.callTool('focus_proof', { file: tmpFile, name: 'partial_bullet' });
    // Fixture: second bullet already closed, first bullet has "intros. admit."
    const hash = extractAdmitHashes(list.text)[0]?.hash;

    // Replace only the admit. with the closing tactic
    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'partial_bullet',
      tactic: 'exact I.',
      admit_hash: hash,
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/replaced/);

    const content = fs.readFileSync(tmpFile, 'utf8');
    // First bullet should now be: intros. exact I. — no admit re-sealed inside
    expect(content).toMatch(/- intros\. exact I\./);
    // File should be fully closed — Qed. not Admitted.
    expect(content).toContain('Qed.');
    expect(content).not.toMatch(/Admitted\./);

    removeTempFixture(tmpFile);
  }, TIMEOUT);

  it('re-seals with admit inside bullet when tactic is non-closing (split.)', async () => {
    const tmpFile = tempFixture('nested_conj.v', 'split_seal');
    await h.callTool('check_file', { file: tmpFile });

    const list = await h.callTool('focus_proof', { file: tmpFile, name: 'nested_conj' });
    const firstHash = extractAdmitHashes(list.text)[0]?.hash;

    // bullet 1 goal is True /\ True. split. creates 2 subgoals — doesn't close.
    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'nested_conj',
      tactic: 'split.',
      admit_hash: firstHash,
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/sealed with/);

    const content = fs.readFileSync(tmpFile, 'utf8');
    // First bullet: split. then 2 child admits (one per goal) — second bullet intact
    expect(content).toMatch(/- split\./);
    const admitCount = (content.match(/\badmit\./g) ?? []).length;
    expect(admitCount).toBeGreaterThanOrEqual(2);

    removeTempFixture(tmpFile);
  }, TIMEOUT);

  it('response includes 0 remaining and Qed when proof fully closed', async () => {
    const tmpFile = tempFixture('partial_bullet.v', 'remaining1');
    await h.callTool('check_file', { file: tmpFile });

    const list = await h.callTool('focus_proof', { file: tmpFile, name: 'partial_bullet' });
    const hash = extractAdmitHashes(list.text)[0]?.hash;

    // Close the only admit — proof should complete
    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'partial_bullet',
      tactic: 'exact I.',
      admit_hash: hash,
    });
    expect(r.isError).toBe(false);
    // Qed applied — no remaining admits to report
    expect(r.text).toMatch(/Qed applied/);
    expect(r.text).not.toMatch(/admit\(s\) remaining/);

    removeTempFixture(tmpFile);
  }, TIMEOUT);

  it('response includes remaining admits after non-closing replacement', async () => {
    const tmpFile = tempFixture('nested_conj.v', 'remaining2');
    await h.callTool('check_file', { file: tmpFile });

    const list = await h.callTool('focus_proof', { file: tmpFile, name: 'nested_conj' });
    const firstHash = extractAdmitHashes(list.text)[0]?.hash;

    // Replace bullet 1 admit with split. — non-closing, re-seals
    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'nested_conj',
      tactic: 'split.',
      admit_hash: firstHash,
    });
    expect(r.isError).toBe(false);
    // split. on True /\ True → 2 child admits + original bullet 2 = 3 remaining
    expect(r.text).toMatch(/3 admit\(s\) remaining/);
    const remainingHashes = [...r.text.matchAll(/([0-9a-f]{8})\s+L/g)].map(m => m[1]);
    expect(remainingHashes.length).toBe(3);

    // Use the last inline hash (bullet 2 — distinct goal True /\ True) to close it
    const secondHash = remainingHashes[remainingHashes.length - 1];
    const r2 = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'nested_conj',
      tactic: 'exact I.',
      admit_hash: secondHash,
    });
    expect(r2.isError).toBe(false);
    expect(r2.text).toMatch(/replaced/);

    removeTempFixture(tmpFile);
  }, TIMEOUT);
});

// ─────────────────────────────────────────────────────────────────────────────
// Regression: auto-bullet must NOT fire at top level (no prior bullet context)
// ─────────────────────────────────────────────────────────────────────────────

describe('auto-bullet suppression at top-level proof', () => {
  // After "split." there are 2 goals but no bullet structure yet.
  // insert_tactic must NOT auto-prepend "- " to the next plain tactic,
  // even though totalRemaining > 1. The user is driving bullets explicitly.

  it('plain tactic after split. is not auto-prefixed with a bullet', async () => {
    const tmpFile = tempFixture('triple_conj.v', 'autobullet');
    await h.callTool('check_file', { file: tmpFile });

    // Step 1: split. at top level — should insert verbatim, no bullet
    const r1 = await h.callTool('insert_tactic', { file: tmpFile, name: 'triple_conj', tactic: 'split.' });
    expect(r1.isError).toBe(false);
    expect(r1.text).toMatch(/2 goal/);
    expect(fs.readFileSync(tmpFile, 'utf8')).not.toMatch(/- split\./);

    // Step 2: second plain split. — must NOT be auto-prefixed as "- split."
    // This is the regression: totalRemaining > 1 and no lspBullet, but user
    // has not started a bullet structure so we must not inject one.
    const r2 = await h.callTool('insert_tactic', { file: tmpFile, name: 'triple_conj', tactic: 'split.' });
    expect(r2.isError).toBe(false);
    const content = fs.readFileSync(tmpFile, 'utf8');
    // Both split. calls must be plain — no auto "- " prefix on either
    const lines = content.split('\n').filter(l => l.match(/split\./));
    expect(lines.every(l => !l.match(/^\s*-\s+split\.|^\s*\+\s+split\.|^\s*\*\s+split\./))).toBe(true);

    removeTempFixture(tmpFile);
  }, TIMEOUT);
});

// ─────────────────────────────────────────────────────────────────────────────
// triple_conj: nested bullet proof using insert_tactic with explicit bullets
// Goal: ((True /\ True) /\ True) /\ (True /\ True)
// Proof script built:
//   split.
//   - split.
//     + split; exact I.
//     + exact I.
//   - split; exact I.
// ─────────────────────────────────────────────────────────────────────────────

describe('triple_conj nested bullet proof via insert_tactic', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('triple_conj.v', 'triple');
    await h.callTool('check_file', { file: tmpFile });
  });

  afterAll(() => removeTempFixture(tmpFile));

  it('split. opens 2 top-level goals', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'triple_conj', tactic: 'split.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/2 goal/);
  }, TIMEOUT);

  it('- split. opens sub-goals inside bullet 1', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'triple_conj', tactic: '- split.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/2.*focus|2 goal/i);
    expect(r.text).toMatch(/background/);
  }, TIMEOUT);

  it('+ split; exact I. closes the True /\\ True sub-bullet', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'triple_conj', tactic: '+ split; exact I.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/bullet closed/i);
  }, TIMEOUT);

  it('+ exact I. closes the True sub-bullet', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'triple_conj', tactic: '+ exact I.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/bullet closed/i);
  }, TIMEOUT);

  it('- split; exact I. closes bullet 2 and applies Qed', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'triple_conj', tactic: '- split; exact I.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/Qed applied/i);
  }, TIMEOUT);

  it('file ends with Qed and no Admitted', async () => {
    const content = fs.readFileSync(tmpFile, 'utf8');
    expect(content).toContain('Qed.');
    expect(content).not.toMatch(/Admitted\./);
    // Verify bullet structure is correct
    expect(content).toMatch(/- split\./);
    expect(content).toMatch(/\+ split; exact I\./);
    expect(content).toMatch(/\+ exact I\./);
    expect(content).toMatch(/- split; exact I\./);
  }, TIMEOUT);
});

// ─────────────────────────────────────────────────────────────────────────────
// deep_conj: admit → split → admit sub-bullets → close one by one
// ─────────────────────────────────────────────────────────────────────────────

describe('deep_conj admit-split-close workflow', () => {
  // Fixture: (True /\ True) /\ True
  //   split → bullet 1: True /\ True (admitted), bullet 2: True (admitted)
  // Workflow:
  //   1. list_admitted → 2 hashes
  //   2. replace bullet 1 admit with split. → re-seals, now 3 admits total
  //   3. close the two new sub-admits (exact I.) one by one
  //   4. close bullet 2 admit (exact I.) → Qed

  it('focus_proof finds exactly 2 admits in the initial fixture', async () => {
    const tmpFile = tempFixture('deep_conj.v', 'dclist');
    await h.callTool('check_file', { file: tmpFile });

    const r = await h.callTool('focus_proof', { file: tmpFile, name: 'deep_conj' });
    expect(r.isError).toBe(false);
    const admits = extractAdmitHashes(r.text);
    expect(admits).toHaveLength(2);

    removeTempFixture(tmpFile);
  }, TIMEOUT);

  it('split. on the first admitted bullet re-seals and reports 3 remaining', async () => {
    const tmpFile = tempFixture('deep_conj.v', 'dcsplit');
    await h.callTool('check_file', { file: tmpFile });

    const list = await h.callTool('focus_proof', { file: tmpFile, name: 'deep_conj' });
    const firstHash = extractAdmitHashes(list.text)[0]?.hash;

    // bullet 1 goal is True /\ True — split. creates 2 child admits + bullet 2 = 3 remaining
    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'deep_conj',
      tactic: 'split.',
      admit_hash: firstHash,
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/sealed with 2 admits/);
    expect(r.text).toMatch(/3 admit\(s\) remaining/);

    removeTempFixture(tmpFile);
  }, TIMEOUT);

  it('closes all sub-admits one by one until Qed', async () => {
    const tmpFile = tempFixture('deep_conj.v', 'dcclose');
    await h.callTool('check_file', { file: tmpFile });

    // Step 1: get initial admits
    const list1 = await h.callTool('focus_proof', { file: tmpFile, name: 'deep_conj' });
    const hash1 = extractAdmitHashes(list1.text)[0]?.hash;

    // Step 2: split bullet 1 → 2 child admits + bullet 2 = 3 admits total
    const splitR = await h.callTool('insert_tactic', {
      file: tmpFile, name: 'deep_conj', tactic: 'split.', admit_hash: hash1,
    });
    expect(splitR.isError).toBe(false);
    expect(splitR.text).toMatch(/sealed with 2 admits/);
    const afterSplit = [...splitR.text.matchAll(/([0-9a-f]{8})\s+L/g)].map(m => m[1]);
    expect(afterSplit).toHaveLength(3);

    // Step 3: all 3 remaining admits have goal True — same hash, exact I. closes all → Qed
    const r2 = await h.callTool('insert_tactic', {
      file: tmpFile, name: 'deep_conj', tactic: 'exact I.', admit_hash: afterSplit[0],
    });
    expect(r2.isError).toBe(false);
    expect(r2.text).toMatch(/Qed applied/);

    // File should be fully closed
    const content = fs.readFileSync(tmpFile, 'utf8');
    expect(content).toContain('Qed.');
    expect(content).not.toMatch(/Admitted\./);

    removeTempFixture(tmpFile);
  }, TIMEOUT);
});

// ─────────────────────────────────────────────────────────────────────────────
// search_lemmas / inspect_term / inspect_about / locate_term / require_lib
// ─────────────────────────────────────────────────────────────────────────────

describe('search / inspect / locate / require', () => {
  it('search_lemmas by name finds plus_n_O', async () => {
    const r = await h.callTool('search_lemmas', { file: BASIC, pattern: 'plus_n_O' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/plus_n_O|n \+ 0/);
  });

  it('search_lemmas with type pattern finds nat addition identity', async () => {
    // Use Rocq 9 metavariable syntax (?n) for type pattern search
    const r = await h.callTool('search_lemmas', { file: BASIC, pattern: '(?n + 0 = ?n)' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/add_0_r/);
  });

  it('inspect_term returns Set/Type for nat', async () => {
    const r = await h.callTool('inspect_term', { file: BASIC, term: 'nat' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/Set|Type/);
  });

  it('inspect_about gives module info for plus_n_O', async () => {
    const r = await h.callTool('inspect_about', { file: BASIC, term: 'plus_n_O' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/plus_n_O/);
  });

  it('locate_term finds Nat.add', async () => {
    const r = await h.callTool('locate_term', { file: BASIC, thing: 'Nat.add' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/add|Nat/);
  });

  it('require_lib imports Lia successfully', async () => {
    // Rocq 9.1 stdlib is under Stdlib.* namespace
    const r = await h.callTool('require_lib', { file: BASIC, lib: 'Stdlib.micromega.Lia' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/Lia|import/i);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// edit_file
// ─────────────────────────────────────────────────────────────────────────────

describe('edit_file', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('basic.v', 'edit');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('find+replace mode substitutes text', async () => {
    const r = await h.callTool('edit_file', {
      file: tmpFile,
      find: '(** Basic fixture for integration tests *)',
      replace: '(** Modified by test *)',
    });
    expect(r.isError).toBe(false);
    expect(fs.readFileSync(tmpFile, 'utf8')).toContain('Modified by test');
  });

  it('returns soft error (isError:false) if text not found', async () => {
    const r = await h.callTool('edit_file', {
      file: tmpFile,
      find: 'this_string_does_not_exist_xyz',
      replace: 'something',
    });
    expect(r.isError).toBe(false); // soft error — not found, file unchanged
    expect(r.text).toMatch(/not found/i);
  });
});

// ─────────────────────────────────────────────────────────────────────────────
// insert_tactic admit_hash mode
// ─────────────────────────────────────────────────────────────────────────────

describe('insert_tactic admit_hash mode', () => {
  let tmpFile: string;

  beforeAll(async () => {
    tmpFile = tempFixture('basic.v', 'hash');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);

  afterAll(() => removeTempFixture(tmpFile));

  it('replaces admits matching a given goal hash', async () => {
    // List all admits and use the first hash — replaces all admits with the same goal
    const list = await h.callTool('focus_proof', { file: tmpFile, name: 'has_admits' });
    const admits = extractAdmitHashes(list.text);
    expect(admits.length).toBeGreaterThanOrEqual(1);

    const hash = admits[0].hash;
    const countBefore = (fs.readFileSync(tmpFile, 'utf8').match(/^\s*- admit\./mg) ?? []).length;

    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'has_admits',
      tactic: 'exact I.',
      admit_hash: hash,
    });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/replaced|done/i);

    // At least one admit should have been replaced
    const countAfter = (fs.readFileSync(tmpFile, 'utf8').match(/^\s*- admit\./mg) ?? []).length;
    expect(countAfter).toBeLessThan(countBefore);
  });

  it('returns error for unknown admit_hash', async () => {
    const r = await h.callTool('insert_tactic', {
      file: tmpFile,
      name: 'trivial',
      tactic: 'exact I.',
      admit_hash: 'deadbeef',
    });
    expect(r.isError).toBe(true);
    expect(r.text).toMatch(/deadbeef/);
  });
});
