/**
 * Integration tests for insert_tactic with goal-introducing tactics:
 * split, induction, inversion, and induction inside a bullet.
 *
 * These are the hardest cases for bullet management — the tool must:
 *   - Report new goals correctly (count, hypotheses)
 *   - Not auto-Qed when goals remain
 *   - Not corrupt bullet structure
 *   - Leave the file in a valid Coq state after every step
 */

import { describe, it, expect, beforeAll, afterAll, test } from 'vitest';
import * as fs from 'fs';
import { McpHarness, createHarness, tempFixture, removeTempFixture } from './harness.js';

const TIMEOUT = 90_000;

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

// ─────────────────────────────────────────────────────────────────────────────
// split introduces 2 goals — file stays valid, no auto-Qed
// ─────────────────────────────────────────────────────────────────────────────

describe('split introduces goals', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('induction_in_bullet.v', 'split');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('split. reports 2 goals and does not Qed', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'induction_in_bullet', tactic: 'split.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/2 goal/);
    expect(r.text).not.toMatch(/Qed applied/i);
  }, TIMEOUT);

  it('file is still valid Coq after split.', async () => {
    const r = await h.callTool('check_file', { file: tmpFile });
    expect(r.isError).toBe(false);
    // Admitted is still present (proof not closed)
    expect(fs.readFileSync(tmpFile, 'utf8')).toMatch(/Admitted\./);
    expect(fs.readFileSync(tmpFile, 'utf8')).not.toMatch(/Qed\./);
  }, TIMEOUT);

  it('split. is not auto-prefixed with a bullet', async () => {
    const content = fs.readFileSync(tmpFile, 'utf8');
    // Extract only the proof body (after Proof. up to Admitted./Qed.)
    const proofBody = content.replace(/^[\s\S]*?Proof\.\n/, '').replace(/\n(Admitted|Qed)\.$[\s\S]*/, '');
    // split. must be a plain tactic line, not "- split." / "+ split." / "* split."
    expect(proofBody).not.toMatch(/^\s*[-+*]\s+split\./m);
  }, TIMEOUT);
});

// ─────────────────────────────────────────────────────────────────────────────
// induction inside a bullet: - intro n. → induction n. → + cases → bullet 2
// ─────────────────────────────────────────────────────────────────────────────

describe('induction inside a bullet — full proof', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('induction_in_bullet.v', 'indbullet');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('split. opens 2 goals', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'induction_in_bullet', tactic: 'split.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/2 goal/);
  }, TIMEOUT);

  it('- intro n. opens bullet 1, reports 1 focused goal + 1 background', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'induction_in_bullet', tactic: '- intro n.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/1.*focus.*1.*background|bullet open/i);
    // hypothesis n should appear in goal summary
    expect(r.text).toMatch(/n/);
  }, TIMEOUT);

  it('induction n. inside bullet reports 2 focused goals + 1 background', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'induction_in_bullet', tactic: 'induction n.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/2.*focus.*1.*background|2 at focus/i);
    expect(r.text).not.toMatch(/Qed applied/i);
  }, TIMEOUT);

  it('file is valid after induction inside bullet', async () => {
    const r = await h.callTool('check_file', { file: tmpFile });
    expect(r.isError).toBe(false);
    expect(fs.readFileSync(tmpFile, 'utf8')).toMatch(/induction n\./);
  }, TIMEOUT);

  it('+ simpl. reflexivity. closes base case bullet', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'induction_in_bullet', tactic: '+ simpl. reflexivity.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/bullet closed/i);
    expect(r.text).not.toMatch(/Qed applied/i);
  }, TIMEOUT);

  it('+ simpl. rewrite IHn. reflexivity. closes step case bullet', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'induction_in_bullet', tactic: '+ simpl. rewrite IHn. reflexivity.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/bullet closed/i);
    expect(r.text).not.toMatch(/Qed applied/i);
  }, TIMEOUT);

  it('- intro n. reflexivity. closes bullet 2 and applies Qed', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'induction_in_bullet', tactic: '- intro n. reflexivity.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/Qed applied/i);
  }, TIMEOUT);

  it('final file has Qed, no Admitted, correct bullet structure', async () => {
    const content = fs.readFileSync(tmpFile, 'utf8');
    // Extract only the induction_in_bullet proof body
    const proofBody = content.match(/Lemma induction_in_bullet[\s\S]*?(?:Qed|Admitted)\./)?.[0] ?? '';
    expect(proofBody).toContain('Qed.');
    expect(proofBody).not.toMatch(/Admitted\./);
    // Bullet 1 opened with -
    expect(proofBody).toMatch(/- intro n\./);
    // induction sub-bullets use +
    expect(proofBody).toMatch(/\+ simpl\. reflexivity\./);
    expect(proofBody).toMatch(/\+ simpl\. rewrite IHn\. reflexivity\./);
    // Bullet 2 closed with -
    expect(proofBody).toMatch(/- intro n\. reflexivity\./);
  }, TIMEOUT);
});

// ─────────────────────────────────────────────────────────────────────────────
// induction at top level — 2 goals, no bullets, no auto-bullet injection
// ─────────────────────────────────────────────────────────────────────────────

describe('induction at top level — no auto-bullet injection', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('induction_in_bullet.v', 'indtoplevel');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('induction n. after intro n. reports 2 goals', async () => {
    await h.callTool('insert_tactic', { file: tmpFile, name: 'induction_in_bullet', tactic: 'split.' });
    await h.callTool('insert_tactic', { file: tmpFile, name: 'induction_in_bullet', tactic: '- intro n.' });
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'induction_in_bullet', tactic: 'induction n.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/2.*focus|2 goal/i);
  }, TIMEOUT);

  it('plain tactic after induction gets child bullet prefix, not parent-level prefix', async () => {
    // After induction n. inside a - bullet, there are 2 focused goals.
    // A plain tactic should get a child bullet (e.g. +), NOT a - (parent level).
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'induction_in_bullet', tactic: 'simpl.' });
    expect(r.isError).toBe(false);
    const content = fs.readFileSync(tmpFile, 'utf8');
    // Must NOT get the parent-level "-" prefix
    expect(content).not.toMatch(/^\s*-\s+simpl\.$/m);
  }, TIMEOUT);
});

// ─────────────────────────────────────────────────────────────────────────────
// inversion introduces hypotheses and a new goal — file stays valid
// ─────────────────────────────────────────────────────────────────────────────

describe('inversion inside a proof', () => {
  let tmpFile: string;
  beforeAll(async () => {
    // Fresh fixture: simple inversion target
    tmpFile = tempFixture('induction_in_bullet.v', 'inversion');
    // Overwrite with a simpler inversion lemma
    fs.writeFileSync(tmpFile, [
      'From Stdlib Require Import Arith.',
      '',
      'Lemma inversion_test : forall (n : nat), S n = S 5 -> n = 5.',
      'Proof.',
      'Admitted.',
      '',
    ].join('\n'));
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('intros introduces hypotheses, reports 1 goal', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'inversion_test', tactic: 'intros n H.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/1 goal/);
    expect(r.text).toMatch(/H/); // hypothesis visible in goal summary
  }, TIMEOUT);

  it('inversion H. reports 1 goal with new hypothesis H1', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'inversion_test', tactic: 'inversion H.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/1 goal/);
    expect(r.text).toMatch(/H1/); // inversion introduces H1: n = 5
    expect(r.text).not.toMatch(/Qed applied/i);
  }, TIMEOUT);

  it('file is valid Coq after inversion', async () => {
    const r = await h.callTool('check_file', { file: tmpFile });
    expect(r.isError).toBe(false);
    expect(fs.readFileSync(tmpFile, 'utf8')).toMatch(/inversion H\./);
  }, TIMEOUT);

  it('subst. closes the remaining goal and applies Qed', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'inversion_test', tactic: 'subst. reflexivity.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/Qed applied/i);
    expect(fs.readFileSync(tmpFile, 'utf8')).toContain('Qed.');
    expect(fs.readFileSync(tmpFile, 'utf8')).not.toMatch(/Admitted\./);
  }, TIMEOUT);
});

// ─────────────────────────────────────────────────────────────────────────────
// conj_induction: forall n, (n + 0 = n) /\ (0 + n = n)
// IH carries both conjuncts — induction then split inside each case.
// This is the key scenario: induction at top-level, split inside each bullet,
// with sub-bullets using + for both conjuncts.
// ─────────────────────────────────────────────────────────────────────────────

describe('conj_induction — induction with split inside each bullet', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('conj_induction.v', 'conjind');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('induction n. opens 2 goals (base and step)', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'conj_induction', tactic: 'induction n.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/2 goal/);
    expect(r.text).not.toMatch(/Qed applied/i);
  }, TIMEOUT);

  it('- split. opens 2 sub-goals inside base case bullet', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'conj_induction', tactic: '- split.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/2.*focus.*background|2 at focus/i);
  }, TIMEOUT);

  it('+ reflexivity. closes first base conjunct', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'conj_induction', tactic: '+ reflexivity.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/bullet closed/i);
    expect(r.text).not.toMatch(/Qed applied/i);
  }, TIMEOUT);

  it('+ reflexivity. closes second base conjunct, step case remains', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'conj_induction', tactic: '+ reflexivity.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/bullet closed/i);
    expect(r.text).not.toMatch(/Qed applied/i);
  }, TIMEOUT);

  it('- destruct IHn as [IH1 IH2]. opens step case with IH1 and IH2 in context', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'conj_induction', tactic: '- destruct IHn as [IH1 IH2].' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/IH1/);
    expect(r.text).toMatch(/IH2/);
    expect(r.text).toMatch(/1 goal/);
  }, TIMEOUT);

  it('split. inside step bullet opens 2 sub-goals', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'conj_induction', tactic: 'split.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/2 goal/);
    expect(r.text).not.toMatch(/Qed applied/i);
  }, TIMEOUT);

  it('+ simpl. rewrite IH1. reflexivity. closes first step conjunct', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'conj_induction', tactic: '+ simpl. rewrite IH1. reflexivity.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/bullet closed/i);
  }, TIMEOUT);

  it('+ simpl. reduces second step conjunct to S n = S n', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'conj_induction', tactic: '+ simpl.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/1 goal/);
    expect(r.text).not.toMatch(/Qed applied/i);
  }, TIMEOUT);

  it('reflexivity. closes final goal and applies Qed', async () => {
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'conj_induction', tactic: 'reflexivity.' });
    expect(r.isError).toBe(false);
    expect(r.text).toMatch(/Qed applied/i);
  }, TIMEOUT);

  it('final file has correct structure: induction, -, +, -, split., +', async () => {
    const content = fs.readFileSync(tmpFile, 'utf8');
    // This fixture has only conj_induction, so the whole file is in scope
    expect(content).toContain('Qed.');
    expect(content).not.toMatch(/Admitted\./);
    expect(content).toMatch(/induction n\./);
    // base case: - split. then + bullets
    expect(content).toMatch(/- split\./);
    expect(content).toMatch(/\+ reflexivity\./);
    // step case: - destruct, then split., then + bullets
    expect(content).toMatch(/- destruct IHn as \[IH1 IH2\]\./);
    expect(content).toMatch(/\+ simpl\. rewrite IH1\. reflexivity\./);
  }, TIMEOUT);
});

// ─────────────────────────────────────────────────────────────────────────────
// Negative: goal-introducing tactic inside a closed bullet is rejected
// ─────────────────────────────────────────────────────────────────────────────

describe('goal-introducing tactic errors', () => {
  let tmpFile: string;
  beforeAll(async () => {
    tmpFile = tempFixture('induction_in_bullet.v', 'goalerr');
    await h.callTool('check_file', { file: tmpFile });
  }, TIMEOUT);
  afterAll(() => removeTempFixture(tmpFile));

  it('induction on wrong variable fails gracefully without corrupting file', async () => {
    await h.callTool('insert_tactic', { file: tmpFile, name: 'induction_in_bullet', tactic: 'split.' });
    await h.callTool('insert_tactic', { file: tmpFile, name: 'induction_in_bullet', tactic: '- intro n.' });
    // induction on a non-inductive term should fail
    const r = await h.callTool('insert_tactic', { file: tmpFile, name: 'induction_in_bullet', tactic: 'induction 42.' });
    // Either rolled back with error in text, or isError — but file must still be valid
    const check = await h.callTool('check_file', { file: tmpFile });
    expect(check.isError).toBe(false);
    // File must not have broken syntax
    const content = fs.readFileSync(tmpFile, 'utf8');
    expect(content).toMatch(/Admitted\.|Qed\./);
  }, TIMEOUT);

  // BUG: speculative Pétanque check does not catch all type errors before
  // committing. coqc rejects "exact true." on "n = n" (bool vs Prop) but
  // insert_tactic accepts and commits it. This test.fails documents the
  // correct desired behaviour; it will start passing once the bug is fixed.
  test.fails('type-incorrect tactic is rejected and not committed to file', async () => {
    const tmpFile2 = tempFixture('induction_in_bullet.v', 'splitbad');
    fs.writeFileSync(tmpFile2, [
      'From Stdlib Require Import Arith.',
      '',
      'Lemma only_nat : forall n : nat, n = n.',
      'Proof.',
      'Admitted.',
      '',
    ].join('\n'));
    await h.callTool('check_file', { file: tmpFile2 });
    await h.callTool('insert_tactic', { file: tmpFile2, name: 'only_nat', tactic: 'intro n.' });
    await h.callTool('insert_tactic', { file: tmpFile2, name: 'only_nat', tactic: 'exact true.' });
    const content = fs.readFileSync(tmpFile2, 'utf8');
    expect(content).toMatch(/Admitted\./);
    expect(content).not.toMatch(/exact true\./);
    removeTempFixture(tmpFile2);
  }, TIMEOUT);
});
