import { describe, it, expect } from 'vitest';
import {
  isSkipLine, isProofEndLine, isTopLevelLine,
  autoAdvancePosition, insertPosition, findProofLine,
  computeBulletIndent,
} from './coq-utils.js';
import { applyTextEdits } from './document-manager.js';

// ═══════════════════════════════════════════════════════════════════
// Helpers: simulate tool operations matching server logic
// ═══════════════════════════════════════════════════════════════════

function focusAutoRemove(text: string, proofName: string): { after: string; removed: boolean } {
  const lines = text.split('\n');
  const proofLine = findProofLine(lines, proofName);
  if (proofLine < 0) return { after: text, removed: false };

  const position = { line: proofLine, character: 0 };
  const insPos = insertPosition(text, position);
  const insLine = (lines[insPos.line] || '').trim();

  if (insLine === 'Admitted.' || insLine === 'Qed.' || insLine === 'Defined.') {
    let prev = insPos.line - 1;
    while (prev >= 0 && (lines[prev].trim() === '' || lines[prev].trim().startsWith('(*'))) prev--;
    if (prev >= 0 && (lines[prev] || '').trim() === 'Proof.') {
      const after = applyTextEdits(text, [{
        range: { start: { line: insPos.line, character: 0 }, end: { line: insPos.line + 1, character: 0 } },
        newText: '',
      }]);
      return { after, removed: true };
    }
  }

  for (let i = insPos.line - 1; i >= 0; i--) {
    const t = (lines[i] || '').trim();
    if (t.startsWith('Proof.') && t !== 'Proof.' &&
        (t.includes('Admitted.') || t.includes('Qed.') || t.includes('Defined.'))) {
      const after = applyTextEdits(text, [{
        range: { start: { line: i, character: 0 }, end: { line: i + 1, character: 0 } },
        newText: 'Proof.\n',
      }]);
      return { after, removed: true };
    }
    if (t !== '' && !t.startsWith('(*')) break;
  }
  return { after: text, removed: false };
}

function insertTactic(
  text: string, tactic: string, proofName: string,
  opts?: { bullet?: string | null; nested?: boolean },
): string {
  const lines = text.split('\n');
  const cursor = findProofLine(lines, proofName);
  if (cursor < 0) throw new Error(`Proof not found: ${proofName}`);
  const pos = { line: cursor, character: 0 };
  const insPos = insertPosition(text, pos);
  const atLineStart = insPos.character === 0;

  const baseIndent = atLineStart ? computeBulletIndent(text, insPos, cursor) : '';
  const b = opts?.bullet ?? undefined;
  // Nested bullet: auto-bullet + active bullet + focus goals (tactic created subgoals)
  const indent = (b && opts?.nested) ? baseIndent + '  ' : baseIndent;
  const prefix = b ? `${indent}${b} ` : indent;
  const fullTactic = `${prefix}${tactic}\n`;

  return applyTextEdits(text, [{
    range: { start: insPos, end: insPos },
    newText: fullTactic,
  }]);
}

function resetProof(text: string, proofName: string): string | null {
  const lines = text.split('\n');
  const proofLine = findProofLine(lines, proofName);
  if (proofLine < 0) return null;

  // Handle "Proof. Admitted." on one line: replace the whole line
  const proofLineContent = (lines[proofLine] || '').trim();
  if (proofLineContent.startsWith('Proof.') && proofLineContent !== 'Proof.' &&
      (proofLineContent.includes('Admitted.') || proofLineContent.includes('Qed.') || proofLineContent.includes('Defined.'))) {
    return applyTextEdits(text, [{
      range: { start: { line: proofLine, character: 0 }, end: { line: proofLine + 1, character: 0 } },
      newText: 'Proof.\nAdmitted.\n',
    }]);
  }

  let endLine = proofLine + 1;
  let foundClosing = false;
  while (endLine < lines.length) {
    const l = (lines[endLine] || '').trim();
    if (l === 'Qed.' || l === 'Admitted.' || l === 'Defined.') { foundClosing = true; break; }
    if (isTopLevelLine(lines[endLine] || '')) break;
    endLine++;
  }
  const end = foundClosing
    ? { line: endLine + 1, character: 0 }
    : (endLine < lines.length
        ? { line: endLine, character: 0 }
        : { line: endLine, character: (lines[endLine - 1] || '').length });

  return applyTextEdits(text, [{
    range: { start: { line: proofLine + 1, character: 0 }, end },
    newText: 'Admitted.\n',
  }]);
}

function addLemma(text: string, name: string, statement: string, beforeName: string): string | null {
  const lines = text.split('\n');
  const beforeLine = findProofLine(lines, beforeName);
  if (beforeLine < 0) return null;
  let kwLine = beforeLine - 1;
  while (kwLine >= 0) {
    if (isTopLevelLine(lines[kwLine] || '')) break;
    kwLine--;
  }
  if (kwLine < 0) return null;
  const block = `\nLemma ${name} : ${statement}.\nProof. Admitted.\n`;
  return applyTextEdits(text, [{
    range: { start: { line: kwLine, character: 0 }, end: { line: kwLine, character: 0 } },
    newText: block,
  }]);
}


// ═══════════════════════════════════════════════════════════════════
// PURE FUNCTIONS
// ═══════════════════════════════════════════════════════════════════

describe('isSkipLine', () => {
  it('skips blank and comment', () => {
    expect(isSkipLine('')).toBe(true);
    expect(isSkipLine('   ')).toBe(true);
    expect(isSkipLine('(* comment *)')).toBe(true);
  });
  it('skips Proof. on its own', () => {
    expect(isSkipLine('Proof.')).toBe(true);
    expect(isSkipLine('Proof.  ')).toBe(true);
  });
  it('does NOT skip "Proof. Admitted."', () => {
    expect(isSkipLine('Proof. Admitted.')).toBe(false);
  });
  it('does NOT skip "Proof. Qed."', () => {
    expect(isSkipLine('Proof. Qed.')).toBe(false);
  });
  it('does NOT skip "Proof. Defined."', () => {
    expect(isSkipLine('Proof. Defined.')).toBe(false);
  });
  it('does NOT skip "Defined."', () => {
    expect(isSkipLine('Defined.')).toBe(false);
  });
  it('does not skip tactic lines', () => {
    expect(isSkipLine('intros H.')).toBe(false);
  });
});

describe('isProofEndLine', () => {
  for (const kw of ['Qed.', 'Admitted.', 'Defined.']) {
    it(kw, () => {
      expect(isProofEndLine(kw)).toBe(true);
      expect(isProofEndLine(`  ${kw}  `)).toBe(true);
    });
  }
  it('not Proof.', () => expect(isProofEndLine('Proof.')).toBe(false));
  it('not Proof. Admitted.', () => expect(isProofEndLine('Proof. Admitted.')).toBe(false));
});

describe('isTopLevelLine', () => {
  for (const kw of ['Lemma','Theorem','Definition','Fixpoint','Inductive',
    'CoFixpoint','Corollary','Example','Remark','Fact','Goal',
    'Require','Import','Export','From','Notation','Ltac','Module',
    'End','Axiom','Parameter','CoInductive']) {
    it(kw, () => expect(isTopLevelLine(`${kw} foo : bar.`)).toBe(true));
  }
  it('not tactic', () => expect(isTopLevelLine('intros H.')).toBe(false));
  it('not Proof.', () => expect(isTopLevelLine('Proof.')).toBe(false));
});

describe('insertPosition', () => {
  it('advances past Proof. to blank, then stops at toplevel', () => {
    const text = `Lemma foo : 1.\nProof.\n\nLemma bar : 2.`;
    expect(insertPosition(text, { line: 1, character: 0 })).toEqual({ line: 3, character: 0 });
  });
  it('stops at Admitted.', () => {
    const text = `Lemma x : 1.\nProof.\n  admit.\nAdmitted.`;
    expect(insertPosition(text, { line: 1, character: 0 })).toEqual({ line: 3, character: 0 });
  });
  it('stops at Qed.', () => {
    const text = `Lemma x : 1.\nProof.\n  reflexivity.\nQed.`;
    expect(insertPosition(text, { line: 1, character: 0 })).toEqual({ line: 3, character: 0 });
  });
  it('stops at Defined.', () => {
    const text = `Lemma x : 1.\nProof.\n  exact I.\nDefined.`;
    expect(insertPosition(text, { line: 1, character: 0 })).toEqual({ line: 3, character: 0 });
  });
  it('stops at next toplevel', () => {
    const text = `Lemma x : 1.\nProof.\n  reflexivity.\nLemma y : 2.`;
    expect(insertPosition(text, { line: 1, character: 0 })).toEqual({ line: 3, character: 0 });
  });
  it('Proof. Admitted. on one line: does not skip, advances past', () => {
    const text = `Lemma foo : 1.\nProof. Admitted.\n\nLemma bar : 2.`;
    expect(insertPosition(text, { line: 1, character: 0 })).toEqual({ line: 2, character: 0 });
  });
  it('caps to file bounds', () => {
    expect(insertPosition('Proof.', { line: 0, character: 0 })).toEqual({ line: 1, character: 0 });
  });
});

describe('autoAdvancePosition', () => {
  it('advances past Proof. and blanks', () => {
    const text = `Lemma foo : 1.\nProof.\n\n  intro H.`;
    expect(autoAdvancePosition(text, { line: 1, character: 0 })).toEqual({ line: 3, character: 0 });
  });
  it('caps bounds', () => {
    expect(autoAdvancePosition('Proof.', { line: 0, character: 0 })).toEqual({ line: 1, character: 0 });
  });
});

describe('computeBulletIndent', () => {
  const proofStart = (name: string) => `Lemma ${name} : nat.\nProof.\n`;

  it('first bullet after induction: matches induction indent (2sp)', () => {
    const text = proofStart('foo') + `  induction n.\nAdmitted.`;
    const insPos = insertPosition(text, { line: 1, character: 0 });
    const proofLine = findProofLine(text.split('\n'), 'foo');
    expect(computeBulletIndent(text, insPos, proofLine)).toBe('  ');
  });

  it('second bullet continues at same indent as first (2sp)', () => {
    const text = proofStart('foo') + `  induction n.\n  - simpl. reflexivity.\nAdmitted.`;
    const insPos = insertPosition(text, { line: 1, character: 0 });
    const proofLine = findProofLine(text.split('\n'), 'foo');
    expect(computeBulletIndent(text, insPos, proofLine)).toBe('  ');
  });

  it('empty proof body: returns empty indent', () => {
    // Proof.\n\n  (* comment *)\nAdmitted. — nothing before Admitted
    const text = proofStart('foo') + `Admitted.`;
    const insPos = insertPosition(text, { line: 1, character: 0 });
    const proofLine = findProofLine(text.split('\n'), 'foo');
    expect(computeBulletIndent(text, insPos, proofLine)).toBe('');
  });

  it('nested bullet indents deeper than outer bullet (4sp)', () => {
    const text = proofStart('foo') + `  - destruct b.\nAdmitted.`;
    const insPos = insertPosition(text, { line: 1, character: 0 });
    const proofLine = findProofLine(text.split('\n'), 'foo');
    expect(computeBulletIndent(text, insPos, proofLine)).toBe('  ');
  });

  it('second nested bullet (continuing +) stays at same indent (4sp)', () => {
    const text = proofStart('foo') + `  - destruct b.\n    + reflexivity.\nAdmitted.`;
    const insPos = insertPosition(text, { line: 1, character: 0 });
    const proofLine = findProofLine(text.split('\n'), 'foo');
    expect(computeBulletIndent(text, insPos, proofLine)).toBe('    ');
  });

  it('back to outer bullet after nested closes: matches outer indent (2sp)', () => {
    const text = proofStart('foo') + `  - destruct b.\n    + reflexivity.\n    - reflexivity.\nAdmitted.`;
    const insPos = insertPosition(text, { line: 1, character: 0 });
    const proofLine = findProofLine(text.split('\n'), 'foo');
    expect(computeBulletIndent(text, insPos, proofLine)).toBe('    ');
  });

  it('no indent when insPos.character is not 0', () => {
    const text = proofStart('foo') + `  induction n.\nAdmitted.`;
    expect(computeBulletIndent(text, { line: 3, character: 4 }, 1)).toBe('');
  });

  it('skips blank lines when scanning backward', () => {
    const text = proofStart('foo') + `  induction n.\n  - reflexivity.\n\nAdmitted.`;
    const insPos = insertPosition(text, { line: 1, character: 0 });
    const proofLine = findProofLine(text.split('\n'), 'foo');
    expect(computeBulletIndent(text, insPos, proofLine)).toBe('  ');
  });
});

describe('insertTactic with text-based indent', () => {
  const lemma = 'Lemma foo : nat.\nProof.';

  it('first bullet after induction uses induction indent', () => {
    const text = lemma + `\n  induction n.\nAdmitted.`;
    const after = insertTactic(text, 'reflexivity.', 'foo', { bullet: '-' });
    expect(after).toContain('  - reflexivity.');
  });

  it('second bullet continues at same indent', () => {
    const text = lemma + `\n  induction n.\n  - reflexivity.\nAdmitted.`;
    const after = insertTactic(text, 'auto.', 'foo', { bullet: '-' });
    expect(after).toContain('  - auto.');
    // The second - line should NOT be indented deeper than the first
    const lines = after.split('\n');
    const firstDash = lines.find(l => l.includes('- reflexivity'));
    const secondDash = lines.find(l => l.includes('- auto'));
    expect(firstDash).toBe('  - reflexivity.');
    expect(secondDash).toBe('  - auto.');
  });

  it('nested bullet indents one level deeper (4sp) when inside active bullet', () => {
    // Inside an active `-` bullet, destruct creates subgoals → first nested `-`
    const text = lemma + `\n  - destruct n.\nAdmitted.`;
    const after = insertTactic(text, 'reflexivity.', 'foo', { bullet: '-', nested: true });
    expect(after).toContain('    - reflexivity.');
  });

  it('nested third level bullet (6sp) when first of a new group', () => {
    // Two levels deep, first subgoal of new group
    const text = lemma + `\n  - destruct n.\n    - destruct n'.\nAdmitted.`;
    const after = insertTactic(text, 'reflexivity.', 'foo', { bullet: '-', nested: true });
    expect(after).toContain('      - reflexivity.');
  });

  it('continuing nested bullet stays at same level (4sp, not deeper)', () => {
    // Second subgoal of an existing group — should match previous bullet indent
    const text = lemma + `\n  - destruct n.\n    - reflexivity.\nAdmitted.`;
    const after = insertTactic(text, 'auto.', 'foo', { bullet: '-' }); // nested: false
    expect(after).toContain('    - auto.');
    // NOT 6 spaces
    expect(after).not.toContain('      - auto.');
  });
});

describe('findProofLine', () => {
  const file = [
    '(* Header *)', '',
    'Lemma foo : forall n, n + 0 = n.',
    'Proof.', '  induction n.', '  - reflexivity.', 'Qed.', '',
    'Theorem bar : 1 = 1.',
    'Proof. Admitted.', '',
    'Lemma baz : 2 = 2.',
    'Proof.', 'Admitted.',
  ];
  it('finds Proof.', () => expect(findProofLine(file, 'foo')).toBe(3));
  it('finds Proof. Admitted.', () => expect(findProofLine(file, 'bar')).toBe(9));
  it('finds Proof. before Admitted', () => expect(findProofLine(file, 'baz')).toBe(12));
  it('returns -1 for missing', () => expect(findProofLine(file, 'nope')).toBe(-1));
});

describe('applyTextEdits', () => {
  it('replaces single line', () => {
    expect(applyTextEdits('a\nb\nc', [{
      range: { start: { line: 1, character: 0 }, end: { line: 2, character: 0 } },
      newText: 'B\n',
    }])).toBe('a\nB\nc');
  });
  it('replaces within a line', () => {
    expect(applyTextEdits('hello world\nfoo', [{
      range: { start: { line: 0, character: 6 }, end: { line: 0, character: 11 } },
      newText: 'there',
    }])).toBe('hello there\nfoo');
  });
  it('splits Proof. Admitted. → Proof.\\n', () => {
    expect(applyTextEdits('Lemma foo.\nProof. Admitted.\n\nLemma bar.', [{
      range: { start: { line: 1, character: 0 }, end: { line: 2, character: 0 } },
      newText: 'Proof.\n',
    }])).toBe('Lemma foo.\nProof.\n\nLemma bar.');
  });
  it('removes Admitted. cleanly', () => {
    expect(applyTextEdits('Lemma foo.\nProof.\nAdmitted.\n\nLemma bar.', [{
      range: { start: { line: 2, character: 0 }, end: { line: 3, character: 0 } },
      newText: '',
    }])).toBe('Lemma foo.\nProof.\n\nLemma bar.');
  });
  it('multi-range removal leaves no extras', () => {
    expect(applyTextEdits('a\nb\nc\nd', [{
      range: { start: { line: 1, character: 0 }, end: { line: 3, character: 0 } },
      newText: '',
    }])).toBe('a\nd');
  });
});

// ═══════════════════════════════════════════════════════════════════
// TOOL OPERATIONS — with rich surrounding context
// ═══════════════════════════════════════════════════════════════════

const surr = `Inductive ty : Type := TyNat | TyBool | TyRef : ty -> ty.
Inductive tm : Type :=
  | Num : nat -> tm
  | BOOL : bool -> tm
  | Succ : tm -> tm | Pred : tm -> tm
  | If : tm -> tm -> tm -> tm
  | Ref : tm -> tm | Deref : tm -> tm
  | Assign : tm -> tm -> tm.
Definition heap := list (nat * tm).

`;

describe('coq_focus: auto-remove (with surrounding defs)', () => {
  it('removes Admitted. on its own line', () => {
    const before = surr + `Lemma foo : 1 = 1.\nProof.\nAdmitted.\n\nLemma bar : 2 = 2.`;
    const { after, removed } = focusAutoRemove(before, 'foo');
    expect(removed).toBe(true);
    expect(after).toBe(surr + `Lemma foo : 1 = 1.\nProof.\n\nLemma bar : 2 = 2.`);
  });
  it('splits Proof. Admitted. on one line', () => {
    const before = surr + `Lemma foo : 1 = 1.\nProof. Admitted.\n\nLemma bar : 2 = 2.`;
    const { after, removed } = focusAutoRemove(before, 'foo');
    expect(removed).toBe(true);
    expect(after).toBe(surr + `Lemma foo : 1 = 1.\nProof.\n\nLemma bar : 2 = 2.`);
  });
  it('removes Qed. if body empty', () => {
    const before = surr + `Lemma foo : 1 = 1.\nProof.\nQed.\n\nLemma bar : 2 = 2.`;
    const { after, removed } = focusAutoRemove(before, 'foo');
    expect(removed).toBe(true);
    expect(after).toBe(surr + `Lemma foo : 1 = 1.\nProof.\n\nLemma bar : 2 = 2.`);
  });
  it('removes Defined. if body empty', () => {
    const before = surr + `Lemma foo : 1 = 1.\nProof.\nDefined.\n\nLemma bar : 2 = 2.`;
    const { after, removed } = focusAutoRemove(before, 'foo');
    expect(removed).toBe(true);
    expect(after).toBe(surr + `Lemma foo : 1 = 1.\nProof.\n\nLemma bar : 2 = 2.`);
  });
  it('does NOT remove if tactics exist between', () => {
    const before = surr + `Lemma foo : 1 = 1.\nProof.\n  reflexivity.\nAdmitted.\n\nLemma bar : 2 = 2.`;
    const { after, removed } = focusAutoRemove(before, 'foo');
    expect(removed).toBe(false);
  });
});

describe('coq_insert_tactic (with surrounding defs)', () => {
  const afterFocus = surr + `Lemma foo : 1 = 1.\nProof.\n\nLemma bar : 2 = 2.`;

  it('inserts tactic with indent', () => {
    const after = insertTactic(afterFocus, 'reflexivity.', 'foo');
    expect(after).toContain('reflexivity');
  });
  it('inserts with bullet', () => {
    const after = insertTactic(afterFocus, 'reflexivity.', 'foo', { bullet: '-' });
    expect(after).toContain('- reflexivity');
  });
});

describe('coq_reset_proof (with surrounding defs)', () => {
  it('wipes Qed. proof', () => {
    const before = surr + `Lemma foo : 1 = 1.\nProof.\n  reflexivity.\nQed.\n\nLemma bar : 2 = 2.`;
    expect(resetProof(before, 'foo')).toBe(surr + `Lemma foo : 1 = 1.\nProof.\nAdmitted.\n\nLemma bar : 2 = 2.`);
  });
  it('wipes Admitted. proof', () => {
    const before = surr + `Lemma foo : 1 = 1.\nProof.\n  admit.\nAdmitted.\n\nLemma bar : 2 = 2.`;
    expect(resetProof(before, 'foo')).toBe(surr + `Lemma foo : 1 = 1.\nProof.\nAdmitted.\n\nLemma bar : 2 = 2.`);
  });
  it('wipes open proof — stops before next lemma', () => {
    const before = surr + `Lemma foo : 1 = 1.\nProof.\n  intros H.\n  reflexivity.\nLemma bar : 2 = 2.`;
    expect(resetProof(before, 'foo')).toBe(surr + `Lemma foo : 1 = 1.\nProof.\nAdmitted.\nLemma bar : 2 = 2.`);
  });
  it('wipes proof at end of file', () => {
    const before = surr + `Lemma foo : 1 = 1.\nProof.\n  intros H.\n  reflexivity.`;
    expect(resetProof(before, 'foo')).toBe(surr + `Lemma foo : 1 = 1.\nProof.\nAdmitted.\n`);
  });
  it('wipes Proof. Admitted. on one line — does not eat next lemma', () => {
    const before = surr + `Lemma foo : 1 = 1.\nProof. Admitted.\n\nLemma bar : 2 = 2.`;
    expect(resetProof(before, 'foo')).toBe(surr + `Lemma foo : 1 = 1.\nProof.\nAdmitted.\n\nLemma bar : 2 = 2.`);
  });
});

describe('coq_add_lemma', () => {
  it('inserts stub before existing proof', () => {
    const before = surr + `Lemma bar : 2 = 2.\nProof. Admitted.`;
    const after = addLemma(before, 'foo', '1 = 1', 'bar');
    expect(after).toBe(surr + `\nLemma foo : 1 = 1.\nProof. Admitted.\n` + `Lemma bar : 2 = 2.\nProof. Admitted.`);
  });
});


// ═══════════════════════════════════════════════════════════════════
// BULLET QUERY POSITION: always valid, never past EOF (prevents hangs)
// ═══════════════════════════════════════════════════════════════════

describe('bulletPos: always in-bounds (no hanging)', () => {
  function bulletQueryPos(text: string, proofName: string) {
    const lines = text.split('\n');
    const pLine = findProofLine(lines, proofName);
    if (pLine < 0) return { valid: false, bulletLine: -1, total: lines.length };
    const insPos = insertPosition(text, { line: pLine, character: 0 });
    const bulletLine = Math.min(insPos.line, lines.length - 1);
    return { valid: bulletLine >= 0 && bulletLine < lines.length, bulletLine, total: lines.length };
  }

  it('valid after auto-remove (Proof. + blank + next lemma)', () => {
    const text = `Lemma foo : 1 = 1.\nProof.\n\nLemma bar : 2 = 2.`;
    const bp = bulletQueryPos(text, 'foo');
    expect(bp.valid).toBe(true);
    expect(bp.bulletLine).toBeLessThan(bp.total);
  });

  it('valid when Proof. is at end of file', () => {
    const text = `Lemma foo : 1 = 1.\nProof.`;
    const bp = bulletQueryPos(text, 'foo');
    expect(bp.valid).toBe(true);
    // clamped: insPos might be past EOF, bulletLine clamped to last line
  });

  it('valid for Proof. Admitted. on one line', () => {
    const text = `Lemma foo : 1 = 1.\nProof. Admitted.\n\nLemma bar : 2 = 2.`;
    const bp = bulletQueryPos(text, 'foo');
    expect(bp.valid).toBe(true);
  });

  it('valid with surrounding definitions + multiple lemmas', () => {
    const text = `Inductive ty := TyNat.\n\nLemma foo : 1 = 1.\nProof.\n\nLemma bar : 2 = 2.\nProof. Admitted.`;
    const bp = bulletQueryPos(text, 'foo');
    expect(bp.valid).toBe(true);
    expect(bp.bulletLine).toBeLessThan(bp.total - 1); // not at EOF
  });
});

describe('full chain (with surrounding defs)', () => {
  const template = surr + `Lemma foo : 1 = 1.\nProof. Admitted.\n\nLemma bar : 2 = 2.\nProof. Admitted.`;

  it('proves foo and bar end-to-end', () => {
    const { after: s1 } = focusAutoRemove(template, 'foo');
    const s2 = insertTactic(s1, 'reflexivity.', 'foo');
    const s3 = insertTactic(s2, 'Qed.', 'foo');
    const { after: s4 } = focusAutoRemove(s3, 'bar');
    const s5 = insertTactic(s4, 'reflexivity.', 'bar');
    const s6 = insertTactic(s5, 'Qed.', 'bar');

    expect(s6).toContain('Lemma foo : 1 = 1.');
    expect(s6).toContain('Qed.');
    expect(s6).toContain('Lemma bar : 2 = 2.');
    expect(s6).not.toContain('Admitted');
  });

  it('reset + re-prove works', () => {
    const { after: s1 } = focusAutoRemove(template, 'foo');
    const s2 = insertTactic(s1, 'reflexivity.', 'foo');
    const s3 = insertTactic(s2, 'Qed.', 'foo');

    const s4 = resetProof(s3, 'foo');
    expect(s4!).toContain('Admitted.');
    expect(s4!).not.toContain('reflexivity'); // foo tactics gone

    const { after: s5 } = focusAutoRemove(s4!, 'foo');
    const s6 = insertTactic(s5, 'reflexivity.', 'foo');
    const s7 = insertTactic(s6, 'Qed.', 'foo');

    // foo is Qed, bar still has its own Admitted
    expect(s7).toContain('reflexivity');
    expect(s7).toContain('Qed.');
    // bar's Proof. Admitted. is untouched, so "Admitted" appears in the file
  });
});
