import type { Position } from './types.js';

/** Skip lines that are blank, comments, Proof., or Proof. with trailing comment. */
export function isSkipLine(line: string): boolean {
  const trimmed = line.trim();
  if (trimmed === '') return true;
  if (trimmed.startsWith('(*')) return true;
  if (trimmed === 'Proof.' || trimmed.startsWith('Proof. ')) {
    const after = trimmed.substring('Proof.'.length).trim();
    if (after === 'Admitted.' || after === 'Qed.' || after === 'Defined.') return false;
    return true;
  }
  return false;
}

/** Check if a line is a proof-ending keyword. */
export function isProofEndLine(line: string): boolean {
  const t = line.trim();
  return t === 'Qed.' || t === 'Admitted.' || t === 'Defined.';
}

/** Check if a line starts a new toplevel Coq command. */
export function isTopLevelLine(line: string): boolean {
  const t = line.trim();
  const kw = t.split(/\s+/)[0];
  return            kw === 'Lemma' || kw === 'Theorem' || kw === 'Definition' ||
         kw === 'Fixpoint' || kw === 'Inductive' || kw === 'CoFixpoint' ||
         kw === 'Corollary' || kw === 'Example' || kw === 'Remark' ||
         kw === 'Fact' || kw === 'Goal' || kw === 'Require' ||
         kw === 'Import' || kw === 'Export' || kw === 'From' ||
         kw === 'Notation' || kw === 'Ltac' || kw === 'Module' ||
         kw === 'End' || kw === 'Axiom' || kw === 'Parameter' ||
         kw === 'CoInductive';
}

/**
 * Advance past Proof. and blank lines to find the view position.
 * Used for goal queries (not for insertion).
 */
export function autoAdvancePosition(text: string, pos: Position): Position {
  const lines = text.split('\n');
  let line = pos.line;
  for (let i = 0; i < 20; i++) {
    if (line >= lines.length) break;
    if (!isSkipLine(lines[line])) break;
    line = line + 1;
  }
  if (line > lines.length) line = lines.length;
  return { line, character: 0 };
}

/**
 * Compute the insert position: advance past Proof., blank, and content lines,
 * stopping at empty lines, proof-ending keywords, or toplevel commands.
 */
export function insertPosition(text: string, pos: Position): Position {
  const lines = text.split('\n');
  let line = pos.line;
  // Phase 1: skip keyword/comment lines
  for (let i = 0; i < 20; i++) {
    if (line >= lines.length) break;
    if (!isSkipLine(lines[line])) break;
    line = line + 1;
  }
  // Phase 2: skip past non-blank content but stop at proof-ending or toplevel keywords
  for (let i = 0; i < 200; i++) {
    if (line >= lines.length) break;
    const l = (lines[line] || '').trim();
    if (l === '') break;
    if (isProofEndLine(lines[line] || '')) break;
    if (isTopLevelLine(lines[line] || '')) break;
    line = line + 1;
  }
  if (line > lines.length) line = lines.length;
  return { line, character: 0 };
}

/**
 * Find the Proof. line for a named lemma/theorem.
 * Returns the 0-based line index of `Proof.` (including `Proof. Admitted.`), or -1.
 */
export function findProofLine(lines: string[], searchName: string): number {
  const s = searchName.trim();
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i].trim();
    const kw = l.split(/\s+/)[0];
    if ((kw === 'Lemma' || kw === 'Theorem' || kw === 'Corollary' || kw === 'Example') &&
        l.includes(s + ' :')) {
      for (let j = i + 1; j < lines.length; j++) {
        const t = (lines[j] || '').trim();
        if (t === 'Proof.' || t.startsWith('Proof. ')) return j;
        if (isTopLevelLine(lines[j] || '') || isProofEndLine(lines[j] || '')) break;
      }
    }
  }
  return -1;
}

/**
 * Compute the indent for a new bullet or tactic line by analyzing the proof
 * body text before `insPos`.  Scans backwards to find the last bullet or
 * tactic line and returns a space-prefix string that matches its indentation.
 */
export function computeBulletIndent(
  text: string,
  insPos: Position,
  proofLine: number,
): string {
  const lines = text.split('\n');
  if (insPos.character !== 0) return '';
  let lastBulletIndent = -1;
  let lastTacticIndent = -1;
  for (let i = insPos.line - 1; i > proofLine; i--) {
    const line = lines[i] || '';
    const trimmed = line.trimStart();
    if (trimmed === '' || trimmed.startsWith('Proof.')) continue;
    const lineIndent = line.length - trimmed.length;
    const bulletMatch = trimmed.match(/^([-+*]+)(?=\s|$)/);
    if (bulletMatch) {
      lastBulletIndent = lineIndent;
      break;
    }
    if (lastTacticIndent < 0) {
      lastTacticIndent = lineIndent;
    }
  }
  if (lastBulletIndent >= 0) return ' '.repeat(Math.max(0, lastBulletIndent));
  if (lastTacticIndent >= 0) return ' '.repeat(Math.max(0, lastTacticIndent));
  return '';
}
