# rocq-piler `focus_proof` False "Proof Complete" — Root Cause

**Original bug report**: `docs/rocq-piler-focus-admitted-bug.md`
**Date resolved**: 2026-05-30

---

## Symptom

For file `docs/rocq-piler-focus-admitted-repro.v`:

- `check_file` correctly reports 3 admitted proofs (lines 138, 146, 156).
- `focus_proof` on e.g. `ftc12_stage_2_correct` reports:

```
goals: 0 at focus
(no goals at focus)

…

next: Proof complete. Qed auto-applied.
```

— while simultaneously showing `goal: (could not query)` in the admits section.
The "Proof complete" claim is false; the lemma is `Admitted.`, not verified.

---

## Root Cause

**Malformed source file — definitions missing terminating `.`**

Five top-level `Definition`s in the file lack the trailing dot required by Coq syntax:

```
Definition ftc12_body : com := … ).   ← no "." before line break
Definition s1 : com := … )).         ← no "."
Definition s2 : com := … )).         ← no "."
Definition Q_ftc12_1 … := … ).      ← no "."
Definition Q_ftc12_2 … := … ).      ← no "."
```

Coq-lsp cannot fully interpret the file. When `focus_proof` queries `proof/goals` at
the `Admitted.` position, the broken context causes coq-lsp to return `goals: []` (0
focused goals) — which `nextHint` interprets as "Proof complete."

---

## Reproduction (after fix)

Adding `.` after each definition makes the file fully valid. After correction:

- `check_file` ⇒ `Yes, 74 spans` (fully checked, previously `Failed, 1 spans`)
- `focus_proof` on `ftc12_stage_2_correct` ⇒ `goals: 1 at focus` / `next: 1 goal. Insert a tactic.` (correct)
- `focus_proof` on `ftc12_post` ⇒ `goals: 1 at focus` (correct)

---

## The `nextHint` blind spot (defense-in-depth)

Even though the original trigger was a malformed file, `nextHint` has a logical gap:
it reports "Proof complete" whenever the goals count is 0, without checking whether
the file text actually says `Admitted.` or `Qed.` A guard was added in `focus_proof`
to override the hint when the proof bounds show `Admitted.` — this prevents a
recurrence if a future coq-lsp version returns 0 goals on a valid-but-admitted proof.

---

## Outcome

**Not a rocq-piler server bug.** The source file had syntax errors. Fix the
definitions and the tool works correctly. The server-side guard is retained as
a safety net.
