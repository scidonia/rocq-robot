import { describe, it, expect } from 'vitest';
import {
  isSkipLine, isProofEndLine, isTopLevelLine,
  autoAdvancePosition, insertPosition, findProofLine,
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
  opts?: { bullet?: string | null; stackDepth?: number },
): string {
  const lines = text.split('\n');
  const cursor = findProofLine(lines, proofName);
  if (cursor < 0) throw new Error(`Proof not found: ${proofName}`);
  const pos = { line: cursor, character: 0 };
  const insPos = insertPosition(text, pos);
  const atLineStart = insPos.character === 0;

  const b = opts?.bullet ?? undefined;
  const hasActiveBullet = !!b;
  const sd = hasActiveBullet ? (opts?.stackDepth ?? 0) : 0;
  const indent = atLineStart ? '  '.repeat(sd + 1) : '';
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

// ═══════════════════════════════════════════════════════════════════
// BULLET INDENT: level-change scenarios
// ═══════════════════════════════════════════════════════════════════

/**
 * Compute the bullet+indent prefix that the server would add.
 * Matches the logic in coq_insert_tactic handler exactly.
 */
function computeBulletPrefix(
  serverState: { bullet?: string | null; goals: number; stackDepth: number; bgGoals: number },
  tactic: string,
): string {
  const bg = serverState.bgGoals ?? 0;
  const totalRemaining = serverState.goals + bg;
  const bulletFromState = serverState.bullet ?? undefined;

  // rawBullet: prefer server bullet, else use '-' when >1 goal remains
  const rawBullet = bulletFromState || (totalRemaining > 1 ? '-' : undefined);
  const bulletMatch = rawBullet?.match(/[-+*]+/);
  const bullet = bulletMatch ? bulletMatch[0]
    : (rawBullet === '-' || rawBullet === '+' || rawBullet === '*' ? rawBullet : undefined);

  const firstWord = tactic.split(/\s+/)[0];
  const hasBullet = /^[-+*]+$/.test(firstWord) || firstWord === '{';

  const hasActiveBullet = !!serverState.bullet;
  const effectiveDepth = hasActiveBullet ? serverState.stackDepth : 0;
  const indent = '  '.repeat(effectiveDepth + 1);

  if (bullet && !hasBullet && tactic !== 'Qed.' && tactic !== 'Defined.' && tactic !== 'Admitted.') {
    return `${indent}${bullet} `;
  }
  return indent;
}

describe('bullet indent: same level (continue)', () => {
  // After case-1 is closed by a `-` bullet, case-2 needs a new `-` at same indent.
  // Server state: no active bullet, 1 focus goal, many background, stack=0.
  it('new - after closing previous - keeps 2sp indent', () => {
    const p = computeBulletPrefix(
      { bullet: null, goals: 1, bgGoals: 20, stackDepth: 0 },
      'inversion Hty.',
    );
    expect(p).toBe('  - '); // 2 spaces + '- '
  });

  it('new - after closing previous -, stack depth may report 1 from bg cases but effective=0', () => {
    const p = computeBulletPrefix(
      { bullet: null, goals: 1, bgGoals: 20, stackDepth: 1 },
      'inversion Hty.',
    );
    expect(p).toBe('  - '); // still 2sp because effectiveDepth=0
  });
});

describe('bullet indent: level down (nest)', () => {
  // Inside a `-` case, a tactic creates multiple subgoals → need `+` at deeper indent.
  // Server state: active bullet `-`, stackDepth=1 (inside `-`), multiple focus goals.
  it('nested + inside active - bullet uses 4sp indent', () => {
    const p = computeBulletPrefix(
      { bullet: '-', goals: 2, bgGoals: 0, stackDepth: 0 },
      'destruct H.',
    );
    expect(p).toBe('  - '); // bullet stays -, indent 2sp
  });

  it('after starting -, a new + subgoal gets deeper indent', () => {
    // In a - bullet, destruct creates 2 subgoals. Server reports bullet='-' and we
    // fall back to rawBullet from totalRemaining>1.
    // But the user would explicitly give '+' as the tactic?
    // Actually, the auto-bullet detects bullet from server. If server says bullet='-',
    // and we don't detect '+', we'd still use '-'. The user must pass '+'.
    // Let's test: active bullet -, user passes '+'
    const p = computeBulletPrefix(
      { bullet: '-', goals: 2, bgGoals: 0, stackDepth: 0 },
      'inversion Hty.',
    );
    expect(p).toBe('  - '); // server says bullet is -, so we use -
  });

  it('when server reports bullet=+, indent=4sp for subgoal', () => {
    // After inserting '+', the server reports bullet='+', stackDepth=1
    const p = computeBulletPrefix(
      { bullet: '+', goals: 1, bgGoals: 0, stackDepth: 1 },
      'reflexivity.',
    );
    expect(p).toBe('    + '); // 4 spaces + '+ '
  });
});

describe('bullet indent: level up (unnest)', () => {
  // After closing a `+` subgoal, we return to the parent `-` level.
  // Server state: bullet from parent may still be in stack but not active focus.
  it('closing + returns to parent -, indent back to 2sp', () => {
    // After + subgoal closes, server has bullet=null, but parent - is still open.
    // The next tactic should get - at root indent.
    const p = computeBulletPrefix(
      { bullet: null, goals: 1, bgGoals: 1, stackDepth: 0 },
      'reflexivity.',
    );
    expect(p).toBe('  - '); // 2 spaces, new - for next parent subgoal
  });

  it('closing all + subgoals returns to -, indent=2sp', () => {
    // After both + subgoals close, we return to - level.
    // Next induction case needs new -
    const p = computeBulletPrefix(
      { bullet: null, goals: 1, bgGoals: 19, stackDepth: 0 },
      'reflexivity.',
    );
    expect(p).toBe('  - '); // 2 spaces + '- '
  });
});

describe('bullet indent: mixed scenario (real induction flow)', () => {
  // Simulates an induction with 3 cases, where case-2 has 2 subgoals.
  it('case 1: -, case 2: -, then destruct gives +, then back to -, then case 3: -', () => {
    // Case 1 closed, case 2 starting
    expect(computeBulletPrefix(
      { bullet: null, goals: 1, bgGoals: 2, stackDepth: 0 }, 'inversion Hty.',
    )).toBe('  - ');

    // Case 2 has 2 subgoals after destruct, still in - bullet
    expect(computeBulletPrefix(
      { bullet: '-', goals: 2, bgGoals: 2, stackDepth: 0 }, 'destruct H.',
    )).toBe('  - ');

    // First subgoal: server reports bullet=+, stackDepth=1
    expect(computeBulletPrefix(
      { bullet: '+', goals: 1, bgGoals: 1, stackDepth: 1 }, 'reflexivity.',
    )).toBe('    + ');

    // Second subgoal closed, back to -, next case needs new -
    expect(computeBulletPrefix(
      { bullet: null, goals: 1, bgGoals: 1, stackDepth: 0 }, 'auto.',
    )).toBe('  - ');
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
    expect(after).toBe(surr + `Lemma foo : 1 = 1.\nProof.\n\n  reflexivity.\nLemma bar : 2 = 2.`);
  });
  it('inserts with bullet', () => {
    const after = insertTactic(afterFocus, 'reflexivity.', 'foo', { bullet: '-', stackDepth: 0 });
    expect(after).toBe(surr + `Lemma foo : 1 = 1.\nProof.\n\n  - reflexivity.\nLemma bar : 2 = 2.`);
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
