# Coq Proof Skill via MCP coq-lsp Tools

This document provides guidance for completing Coq/Rocq proofs using the `coq-lsp` MCP tools.

## Tool Reference

### Proof Navigation

| Tool | Purpose |
|------|---------|
| `focus_proof` | Get the current proof tree: goals, bullet depth, proof script up to cursor. Sets file cursor for subsequent `insert_tactic`. Accepts proof name or explicit position. |
| `open_goals` | Get current open goals for a named proof (Prev mode by default). |
| `proof_state` | Get richer proof context including proof name and statement. |
| `check_file` | Force full document checking and return completion status. |
| `check_file_range` | Check a specific line range and return diagnostics. |

### Tactic Insertion

| Tool | Purpose |
|------|---------|
| `insert_tactic` | Insert a tactic into a proof and return updated goals. **Auto-prepends bullet prefix** (-, +, *) when proof state requires it. Use `replace: true` to retry a failed tactic (undoes last insertion first). |
| `try_step` | Single-call speculative tactic execution: get state, run tactic, return updated goals. Does NOT modify the file. Use to test a tactic before committing. |
| `undo_step` | Restore the file to before the last N edit operations. |

### Lemma Management

| Tool | Purpose |
|------|---------|
| `add_lemma` | Insert a lemma stub (Lemma name : statement. Proof. Admitted.) above a specified proof. Use `before` to name the proof it goes above. |
| `reset_proof` | Wipe a proof body (from Proof. to Qed./Admitted.) and replace with fresh Admitted. Use to restart a broken proof. |

### Exploration & Library Management

| Tool | Purpose |
|------|---------|
| `search_lemmas` | Search the Coq environment for lemmas/theorems. Simple names auto-quote. Use parentheses for patterns: `(_ + 0 = _)`. |
| `check_file_term` | Check the type of a term speculatively. Runs `Check <term>.` |
| `inspect_about` | Get information about a term/definition speculatively. Runs `About <term>.` |
| `locate_term` | Find where a library, module, or term is defined. Useful before Require to check if a module exists. |
| `require_lib` | **Import a library speculatively without modifying the file.** All subsequent speculative queries (search, check, try_tactic) on that file will see the imported library. Use this to explore what lemmas are available before committing to a Require statement. |

### File Editing

| Tool | Purpose |
|------|---------|
| `edit_file` | Apply text edits to a file and re-sync with rocq-lsp. Use `find`/`replace` for simple text search-and-replace instead of computing line numbers. |

## Proof Strategy

### 1. Start with the goal

Use `focus_proof` on the theorem to see the goal and proof context.

```coq
focus_proof name="my_theorem" file="path/file.v"
```

### 2. Import needed libraries

If you need libraries that aren't already imported in the file, use `require_lib` to speculatively import them:

```coq
require_lib file="path/file.v" lib="Coq.Lists.List"
require_lib file="path/file.v" lib="Coq.Arith.Arith"
```

Now you can use `search_lemmas` to find lemmas from these libraries:

```coq
search_lemmas file="path/file.v" pattern="(_ ++ [])"
# Returns: app_nil_r : forall l : list A, l ++ [] = l
```

**Important**: `require_lib` does NOT modify the file. Once your proof works, manually add the `Require Import` statement to the actual file.

### 3. Plan the induction

Most Coq theorems about inductive relations are proved by induction on the relation itself.
- `induction Hstep` — if proving a step relation property
- `induction Hty` — if proving a typing property
- `induction t` — if proving a term property

### 3. Handle base cases first

Simple base cases often just need `inversion` and `exists`:
```coq
- inversion Hty; subst. exists S. split. apply extends_refl. ...
```

### 4. Use induction hypotheses

For inductive cases, `destruct (IH...)` to get the induction hypothesis, then combine with constructors:
```coq
- destruct (IHHstep T S H3 Hok Hlen) as [S' [Hext [Hok' [Hty' Hlen']]]].
  exists S'. split. exact Hext. ...
```

### 5. Search for existing lemmas first

Before writing a new lemma, search to see if it already exists:

```coq
search_lemmas file="path/file.v" pattern="(_ + 0)"
search_lemmas file="path/file.v" pattern="nth_error (_ ++ _)"
```

If the lemma you need is in a library that's not imported:

```coq
locate_term file="path/file.v" thing="Coq.Lists.List"
require_lib file="path/file.v" lib="Coq.Lists.List"
search_lemmas file="path/file.v" pattern="(_ ++ [])"  # Now finds app_nil_r
```

### 6. Add lemmas only when needed

When a case fails because a helper property is truly missing (not in standard libraries), add it with `add_lemma`:

```coq
add_lemma name="my_lemma" statement="forall x, P x"
              before="main_theorem" file="path/file.v"
```

Then prove the lemma before returning to the main theorem.

## Bullet System

### Auto-bullet behavior

When you insert a tactic and there are multiple goals remaining, the tool **automatically prepends a bullet prefix** with correct indentation.

**Bullet rotation**: To prevent Coq's focus stack from collapsing, sibling bullets use the same character but **nested bullets use different characters**:

- Level 0 (outermost): `-`
- Level 1 (first nesting): `+`
- Level 2 (second nesting): `*`
- Level 3+: `--`, `++`, `**`, `---`, ...

The tool determines this automatically. You just type the tactic name (e.g., `split.`), and the tool adds the right bullet and indentation.

### When bullets appear

A bullet is prepended when:
- **LSP says "Focus next goal with bullet X."** — The LSP knows the correct bullet for the next sibling. Trust it.
- **LSP says "unfinished" and >1 focused goals** — The current bullet context has multiple subgoals. A child bullet is needed, using the next character in rotation.
- **No LSP bullet and totalRemaining > 1** — The first bullet group in a branch. Starts with `-`.

No bullet is added when:
- Only 1 goal remains — the tactic runs in the current context.
- The tactic is `Qed.`, `Defined.`, or `Admitted.`.

### Bullet structure in proofs

```
split.               (* 2 goals created *)
- split.             (* focuses on goal 1, creates 2 subgoals *)
  + split.           (* focuses on subgoal 1.1, creates 2 sub-subgoals *)
    * trivial.       (* solves sub-subgoal 1.1.1 *)
    * trivial.       (* solves sub-subgoal 1.1.2 *)
  + trivial.         (* solves subgoal 1.2 *)
- trivial.           (* solves goal 2 *)
```

## Common Tactic Patterns

### Inversion
```coq
inversion Hty; subst.              (* destructure typing derivation *)
inversion H4; subst.               (* destructure value judgment *)
```

### Existence
```coq
exists S. split. exact Hext. split. exact Hok. split. constructor. ...
exists (S ++ [T]). split. exists [T]. reflexivity. ...
```

### Induction Hypothesis
```coq
destruct (IHHstep TyNat S H2 Hok Hlen) as [S' [Hext [Hok' [Hty' Hlen']]]].
```

### Context Weakening
```coq
eapply has_type_weaken; eauto.     (* when store extends *)
rewrite nth_error_app2 by lia.     (* when appending to store *)
```

### Arithmetic
```coq
lia                                (* linear integer arithmetic solver *)
omega                              (* older alternative to lia *)
rewrite app_length. simpl. lia.    (* length calculations *)
```

## Multi-Subgoal Strategies

When `induction` (or `destruct`, `inversion`) produces many subgoals (10+), tackling each with individual bullets is tedious. Coq provides several mechanisms for bulk handling.

### `all:` — apply to every remaining goal
```coq
all: try (inversion Hty; subst; eauto).    (* try to solve all goals *)
all: reflexivity.                           (* all goals are equalities *)
```

**When to use:** Goals are identical or `try` can handle variation. Avoid if different cases need different inversion hypotheses — `inversion` may give different names per goal.

### `;` — sequential chaining
```coq
induction Hstep; intros T S Hty Hok.       (* intros applied to all 21 subgoals *)
```
`tactic1; tactic2` runs `tactic1`, then `tactic2` on every subgoal `tactic1` generated. This is how we handle the generalized induction pattern in the preservation proof: `revert T S Hty Hok; induction Hstep; intros T S Hty Hok.`

**When to use:** When all subgoals need the same initial processing (intro, clear, rename). Combined with `induction`, eliminates per-bullet `intros` repetition.

### `[... | ... | ...]` — per-subgoal dispatch
```coq
split; [exact Hext | split; [exact Hok' | apply T_Succ; exact Hty']].
```
Each bracket corresponds to one generated subgoal. For 21 induction cases, each gets a `-` bullet automatically, but within each bullet you can dispatch sub-subgoals with brackets.

**When to use:** When you know the exact number of subgoals and each needs different handling. Common inside inductive cases: `inversion Hty; subst.` reveals typing contexts, then IH + constructor dispatch closes the case.

### `repeat` — iterate to convergence
```coq
repeat (try split; try reflexivity).       (* eliminates all /\ in goal *)
```
**When to use:** When a tactic needs to run an unknown number of times (splitting conjunctions, destructing `and`, normalizing).

### Practical workflow for 21-goal induction

For the `preservation` proof (PCF+Ref, 21 step rules), the optimal pattern is:
```coq
proof.
  intros t mu t' mu' T S Hty Hstep Hok.
  revert T S Hty Hok.
  induction Hstep; intros T S Hty Hok.
  - (* S_Succ *)    inversion Hty; subst. destruct IH...  exists S'. split... T_Succ.
  - (* S_PredZero *) inversion Hty; subst. exists S. split. apply extends_refl. ...
  - (* S_PredSucc *) (* ... *)
  ...
```
Each bullet follows one of ~3 patterns:
1. **Base case, no heap change:** `inversion Hty; subst. exists S. split; [apply extends_refl | split; [exact Hok | constructor]].`
2. **Inductive case, same heap:** `inversion Hty; subst. destruct (IHHstep ...) as ...  exists S'. split... use constructor.`
3. **Heap-extending case (S_RefV, S_AssignV):** needs `has_type_weaken`, `heap_ok` extension, or `nth_error` properties.

For pattern 1 and 2, a single Ltac script could auto-solve many cases:
```coq
Ltac solve_preservation :=
  intros T S Hty Hok; inversion Hty; subst;
  match goal with
  | [ Hstep: step ?t _ ?t' _, IHHstep: forall T S, has_type _ S ?t T -> _ |- exists S', _, _ /\ _, _ /\ has_type _ _ (Succ ?t') _ ] =>
    destruct (IHHstep TyNat S H2 Hok) as [S' [? [? ?]]]; exists S'; split; [assumption | split; [assumption | econstructor; eauto]]
  | ... (* more patterns *)
  end.
```

**When NOT to use bulk tactics:** If each case needs a completely different lemma or reasoning strategy, individual bullets with clear script are better for readability and maintainability. Compact scripts that solve everything at once become unreadable and hard to debug.

## Lemma Dependency Order

When proving a large theorem, add lemmas in dependency order:

| Lemma | Used By | Purpose |
|-------|---------|---------|
| `extends_refl` | Base cases | Every store extends itself |
| `nth_error_app_l` | `has_type_weaken` | Lookup in extended store |
| `has_type_weaken` | Many cases | Typing preserved under store extension |
| `extends_heap_ok` | S_RefV | Heap well-formedness under store extension |
| `heap_ok_lookup` | S_DerefLoc | Well-formed heap has typed entries |
| `substitution_preserves_typing` | S_AppAbs, S_Fix | Substitution preserves types |
| `heap_ok_update` | S_AssignV | Heap update preserves well-formedness |

## Working with Libraries

### Workflow for discovering and using library lemmas

1. **Check if a library exists**:
   ```coq
   locate_term file="proof.v" thing="Coq.Lists.List"
   # Returns: Module Coq.Lists.List
   ```

2. **Speculatively import the library**:
   ```coq
   require_lib file="proof.v" lib="Coq.Lists.List"
   # Returns: Imported Coq.Lists.List — available for subsequent queries on proof.v
   ```

3. **Search for lemmas you need**:
   ```coq
   search_lemmas file="proof.v" pattern="(_ ++ [])"
   # Returns: app_nil_r : forall l : list A, l ++ [] = l

   search_lemmas file="proof.v" pattern="length (_ ++ _)"
   # Returns: app_length : forall l l', length (l ++ l') = length l + length l'
   ```

4. **Test tactics using the library**:
   ```coq
   try_step file="proof.v" name="my_theorem" tactic="rewrite app_nil_r."
   # Tests if the tactic works without modifying the file
   ```

5. **Once verified, add to file**:
   After your proof works with the speculative import, manually add at the top of the file:
   ```coq
   Require Import Coq.Lists.List.
   ```

### Common standard libraries

| Library | Import Statement | Contains |
|---------|------------------|----------|
| Lists | `Coq.Lists.List` | List operations, lemmas (app, length, nth, etc.) |
| Arith | `Coq.Arith.Arith` | Natural number arithmetic, comparison |
| Bool | `Coq.Bool.Bool` | Boolean operations and lemmas |
| Lia | `Coq.micromega.Lia` | Linear integer arithmetic solver (lia tactic) |
| Omega | `Coq.omega.Omega` | Older arithmetic solver (omega tactic) |
| Program | `Coq.Program.Tactics` | Program mode tactics |

### Multiple libraries

You can import multiple libraries for the same file:

```coq
require_lib file="proof.v" lib="Coq.Lists.List"
require_lib file="proof.v" lib="Coq.Arith.Arith"
require_lib file="proof.v" lib="Coq.micromega.Lia"

# Now all three are available for queries on proof.v
search_lemmas file="proof.v" pattern="(_ + 0)"  # Finds Arith lemmas
search_lemmas file="proof.v" pattern="(_ ++ _)"  # Finds List lemmas
```

### Persistence

Speculative imports persist for the entire MCP session:
- Once you `require_lib` a library for a file, all subsequent queries on that file see it
- The imports are tracked per-file URI
- Restarting the MCP server clears the cache
- The actual `.v` file is never modified — you must manually add `Require Import` statements

## Troubleshooting

### LSP stale after bulk edits

If the LSP reports errors after `edit_file`, run `check_file` to force re-processing:
```coq
check_file file="path/file.v"
```

### Proof out of sync

If `insert_tactic` inserts at the wrong position, use `focus_proof` to reset the cursor:
```coq
focus_proof name="my_theorem" file="path/file.v"
```

### Speculative check fails for proof-closing commands

`Qed.` and `Admitted.` bypass petanque pre-flight checks. Insert them directly.

### Replace a failed tactic

Use `replace: true` to undo the last insertion and retry:
```coq
insert_tactic name="my_theorem" tactic="reflexivity." file="path/file.v" replace=true
```
