import type { Position } from './types.js';
import { applyTextEdits } from './document-manager.js';

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

/**
 * Find the proof body bounds for a named proof.
 * Returns { proofLine, endLine } or null if not found.
 */
export function proofBounds(lines: string[], proofName: string): { proofLine: number; endLine: number } | null {
  const proofLine = findProofLine(lines, proofName);
  if (proofLine < 0) return null;

  let endLine = -1;
  for (let i = proofLine + 1; i < lines.length; i++) {
    const l = lines[i].trim();
    if (l === 'Admitted.' || l === 'Qed.' || l === 'Defined.') {
      endLine = i;
      break;
    }
    if (isTopLevelLine(lines[i] || '')) break;
  }
  if (endLine < 0) return null;
  return { proofLine, endLine };
}

/**
 * Find all admit. (lowercase, tactic-level) lines within a proof body.
 * Returns the 0-indexed line numbers of each admit.
 */
export function findAdmitLines(lines: string[], proofLine: number, endLine: number): number[] {
  const admitted: number[] = [];
  for (let i = proofLine + 1; i < endLine; i++) {
    const t = lines[i].trim();
    // Match standalone `admit.` bullets and also `admit` used as a tactic
    // inside bracket expressions (e.g. `[exact Hok | admit]`).
    // Exclude `Admitted.` (the proof-closing command).
    if (t === 'Admitted.' || t === 'Qed.' || t === 'Defined.') continue;
    if (t === 'admit.' || t.endsWith(' admit.') || /\badmit\b/.test(t)) {
      admitted.push(i);
    }
  }
  return admitted;
}

/**
 * Extract the bullet/tactic prefix from an admit line.
 * For "- admit." returns "- ". For "  + admit." returns "  + ".
 * For bare "admit." returns "".
 */
export function admitPrefix(line: string): string {
  const idx = line.indexOf('admit.');
  if (idx < 0) return '';
  return line.substring(0, idx);
}

/**
 * Compute the insert position after a bullet marker on a reopened admit line.
 * For "  + " returns { character: 4 }. For bare "" returns { character: 0 }.
 * Called by insert_tactic after replace_admit reopens a bullet.
 */
export function bulletInsertPos(line: string): number {
  const match = line.match(/^\s*[-+*]+(?:\s)/);
  return match ? match[0].length : 0;
}

/**
 * Replace an admit. line with a new tactic + re-seal admit.
 * Given text and the line number of an admit., replaces that line
 * with the bullet prefix, inserts the tactic at the right position,
 * and re-seals with admit. afterwards.
 *
 * Returns the new text, or the original if the line wasn't an admit.
 */
export function replaceAdmitLine(
  text: string,
  admitLine: number,
  tactic: string
): string {
  const lines = text.split('\n');
  const line = lines[admitLine] || '';
  const prefix = admitPrefix(line);
  if (!line.includes('admit.')) return text;

  return applyTextEdits(text, [{
    range: { start: { line: admitLine, character: 0 }, end: { line: admitLine + 1, character: 0 } },
    newText: prefix ? `${prefix}${tactic}\n` : `${tactic}\n`,
  }]);
}

/**
 * Apply a tactic to all admit lines whose goal text matches a given hash.
 * Re-queries after each replacement so line numbers stay fresh.
 *
 * getGoalText is injected — in production it calls the LSP, in tests it's mocked.
 * Returns the new text and the count of replacements made.
 */
export async function replaceAllMatchingAdmits(
  text: string,
  proofName: string,
  tactic: string,
  targetHash: string,
  getGoalText: (line: number, text: string) => Promise<string | null>
): Promise<{ text: string; count: number }> {
  const { createHash } = await import('crypto');
  let currentText = text;
  let count = 0;

  while (true) {
    const lines = currentText.split('\n');
    const bounds = proofBounds(lines, proofName);
    if (!bounds) break;
    const admitLines = findAdmitLines(lines, bounds.proofLine, bounds.endLine);

    let matched = -1;
    for (const line of admitLines) {
      const goalText = await getGoalText(line, currentText);
      if (goalText === null) continue;
      const h = createHash('md5').update(goalText).digest('hex').slice(0, 8);
      if (h === targetHash) { matched = line; break; }
    }
    if (matched < 0) break;

    currentText = replaceAdmitLine(currentText, matched, tactic);
    count++;
  }

  return { text: currentText, count };
}
