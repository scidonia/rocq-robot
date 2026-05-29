# Tool Problems

Problems encountered while using the MCP coq-lsp tools interactively.

## 1. `proof/goals` returns 0 goals after compound tactics

**Severity:** High
**Status:** Open

After inserting a compound tactic like `induction; intros`, the `proof/goals` query
at `insertedUntil` (Prev mode) returns 0 goals even when subgoals remain.
This causes `coq_insert_tactic` to report "done" misleadingly.

In some cases the proof genuinely IS complete (eauto closes everything),
but there's no way for the caller to distinguish "genuinely done" from
"goals query failed".

**Observed in:** `coq_insert_tactic` response after `induction Ht; simpl; intros ...`

**Workaround:** Try `Qed.` — if it fails, the proof wasn't complete.

## 2. `coq_focus` auto-remove of Admitted can corrupt file

**Severity:** Medium
**Status:** Open

When auto-remove of `Admitted.` happens, the remaining proof body may become
empty (0 goals query). The tool doesn't confirm the removal or report what
happened. Sometimes content is removed unexpectedly.

## 3. `coq_reset_proof` can target wrong proof

**Severity:** Medium
**Status:** Open

When cursor is near a proof boundary, `coq_reset_proof` may reset the WRONG
proof (e.g., the one above instead of the current one). The search backwards
for `Proof.` doesn't confirm it found the intended proof.

**Fix suggestion:** Require explicit position or confirm the lemma name.

## 4. `coq_add_lemma` positioning unreliable

**Severity:** Medium
**Status:** Open

Lemma added via `coq_add_lemma` may be inserted between the two lines of a
multi-line lemma statement rather than above it. The walk-backwards search
doesn't properly identify toplevel boundaries.

**Observed in:** PCF additions where lemma was inserted mid-statement.

## 5. "done" response doesn't suggest Qed

**Severity:** Low
**Status:** Fixed (40e6a4b)

Changed "done" to "done — try Qed" to explicitly guide the user.

## 6. No proof shape/context in insert response

**Severity:** Medium
**Status:** Open

`coq_insert_tactic` returns goals but not the proof script context.
The caller can't see what tactics have already been written, making it
hard to understand the current proof state without separate `coq_focus` calls.

**Fix suggestion:** Include proof script in response, or show surrounding context.

## 7. `coq_reset_proof` doesn't report which proof was reset

**Severity:** Medium
**Status:** Open

Returns `"test_issues.v:75 — proof reset to Admitted."` but doesn't
include the lemma/theorem name. The caller can't verify it reset the
intended proof.

**Fix suggestion:** Search backwards from `Proof.` to find the `Lemma`/`Theorem`
name and include it in the response.

## 8. `coq_add_lemma` + `coq_reset_proof` corrupt file when used together

**Severity:** High
**Status:** Open

When `coq_add_lemma` inserts a lemma above the cursor and then
`coq_reset_proof` is called, it may reset the wrong proof. The cursor
tracking between tools is unreliable, causing file corruption.

**Observed in:** PCF proofs where multiple lemmas were added and reset.

## 9. `coq_add_lemma` positions lemma mid-statement instead of above

**Severity:** High
**Status:** Open

The walk-backwards search incorrectly identifies toplevel boundaries,
causing the lemma to be inserted between two lines of a multi-line
lemma statement. Results in mangled files.

**Observed in:** PCF proofs — lemma inserted between `Lemma name :` and
its continuation line.
