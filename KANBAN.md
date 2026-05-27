# Ergonomic Issues — Kanban

## In Progress


## Backlog — High Priority

## Backlog — High Priority

### No way to return to admitted/outstanding bullets
- **Problem:** When you `admit` a case mid-induction, those subgoals become "given-up." No way to navigate back and replace them.
- **Fix:** `list_admitted` scans proof for `admit.` lines, queries goal state at each, returns `{hash, line, goal}`. `replace_admit hash=...` finds the matching admit by goal hash, removes the line, reopening the bullet for `insert_tactic`. Commit `f8120ad`.

### Multi-tactic one-liner silently drops tail
- **Problem:** `intros. inversion; subst. destruct... exists... split... apply...` on one line. If any `.`-separated tactic fails mid-line, Coq stops processing, everything after is dead code. No error reported, file corrupted.
- **Proposed:** Warn when tactic contains >3 `.` separators; suggest splitting into multiple `insert_tactic` calls.

### Undo removes wrong operation in multi-insert bullets
- **Problem:** A bullet with two `insert_tactic` calls (e.g., `intros/inversion` on one line, `destruct/exists` on next). With `replace:true`, `undo_step(1)` restores to an intermediate state (old tactic deleted, new not inserted).
- **Root cause:** `insert_tactic replace:true` pushed history twice — once when deleting old tactic, once when inserting new. `undo_step(1)` only pops one, landing at the intermediate state.
- **Fix:** Flag `historyAlreadyPushed` — skip the second `pushFileHistory` when replace already pushed. Commit `TBD`.

## Backlog — Medium Priority

### Bullet position shifts after mid-sequence undo+reinsert
- **Problem:** Removing and re-inserting a bullet in the middle of a 21-bullet sequence causes subsequent `insert_tactic` calls to land on wrong goals (e.g., S_Ref tactic went into S_AppAbs's slot).
- **Proposed:** Recompute bullet positions after every undo; or use named bullet targets instead of position-based.

### No batch-solve for repeated identical subgoal patterns
- **Problem:** 8+ cases share `intros; inversion; exists S; split; extends_refl; split; Hok; constructor`. Each requires separate `insert_tactic`. Coq supports `all: try (...)` but the tool doesn't help compose or apply bulk tactics.
- **Proposed:** A `batch_tactic` command that applies the same tactic to all remaining background goals at the same stack level.

### LSP/coqc bullet disagreement in `has_type_weaken`
- **Problem:** `has_type_weaken` reports Qed in LSP (`check_file`), but coqc rejects with "No such goal. Focus next goal with bullet -." The `;` chaining with bracket dispatch in multi-premise cases (T_If, T_App, T_Assign) passes LSP validation but fails batch compilation.
- **Impact:** False confidence — `insert_tactic` shows the proof as complete, but `coqc` says otherwise.
- **Problem:** The LLM (or user) uses `admit.` on hard cases. These become "given-up" in the proof state. After the Qed/admitted line, you can't navigate back to fix them. The only option is to manually locate `admit` lines and replace them.
- **Proposed:** `focus_proof` should list given-up goals. `reset_proof` on a subgoal should be possible without wiping the entire proof.

## Done

- [x] Tool renames — removed `coq_` prefix, descriptive names
- [x] Proof-scoped undo — `undo_step` doesn't cross lemma boundaries
- [x] Lemma persistence through undo — `add_lemma` anchors history
- [x] `Proof.` auto-injection — missing `Proof.` is automatically added
- [x] Multi-line `check_file` types — no truncation
- [x] Multi-subgoal strategies in SKILL.md
- [x] Spec preview in `insert_tactic` — shows resulting goals before commit
- [x] `delete_lemma` — removes lemma block + forces LSP re-sync
- [x] `delete_step` — removes last N tactic lines without history
- [x] Auto-`.` — appends period if missing from tactic
- [x] No goal/type truncation — full visibility for AI reasoning
- [x] Stale LSP after edit — close+reopen+poll with petanque memo=false
- [x] Full hypothesis list in spec preview (single-goal cases) — commit `42c6980`
- [x] `list_admitted` + `replace_admit` for bullet navigation — commit `f8120ad`
