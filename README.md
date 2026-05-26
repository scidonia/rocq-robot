# Neurosymbolic Programming with Rocq LSP

## Overview

This project demonstrates how a **Language Server Protocol (LSP)** interface to the **Rocq proof assistant** (formerly Coq) enables **neurosymbolic programming**: the seamless integration of neural networks (LLMs) with symbolic reasoning systems (proof assistants).

## What is Neurosymbolic Programming?

Neurosymbolic programming combines:

- **Neural/Statistical AI** (LLMs): Pattern recognition, natural language understanding, heuristic search
- **Symbolic AI** (Proof assistants): Logical reasoning, formal verification, guaranteed correctness

This approach leverages the complementary strengths of both paradigms:

| Neural (LLM) | Symbolic (Rocq) |
|--------------|-----------------|
| Intuition & pattern matching | Rigorous logical deduction |
| Generates candidate solutions | Verifies correctness |
| Probabilistic & approximate | Deterministic & exact |
| Learns from examples | Reasons from axioms |
| Fast but fallible | Slow but infallible |

## How LSP Enables Neurosymbolic Rocq Programming

### The Traditional Problem

Historically, interacting with proof assistants required:
- Deep knowledge of proof tactics and syntax
- Understanding of internal proof state representations
- Manual, tedious proof construction
- Limited automation capabilities

This created a barrier between AI systems (which excel at pattern matching and generation) and proof assistants (which excel at verification).

### The LSP Solution

The **Language Server Protocol** provides a standardized, machine-friendly interface that:

1. **Exposes Proof State**: Query current goals, hypotheses, and proof context at any position
2. **Enables Interactive Editing**: Apply tactics and immediately observe their effects
3. **Supports Speculative Execution**: Try tactics without committing to file edits (Pétanque API)
4. **Provides Structured Feedback**: Parse errors, type information, and verification results

This transforms the proof assistant into a **verification oracle** that an LLM can query interactively.

In this implementation, the bridge is also **project-aware**: it can detect Coq/Rocq project roots, reopen documents under the correct workspace, and keep `rocq-lsp` aligned with `_CoqProject`, `_RocqProject`, or `dune-project` layouts.

### The Neurosymbolic Loop

```
┌─────────────┐
│   LLM       │  ← Reads: proof goals, context, error messages
│  (Neural)   │  → Generates: candidate tactics, proof strategies
└──────┬──────┘
       │
       ↓ (proposes tactics)
┌──────────────┐
│  LSP Server  │  ← Bridges neural and symbolic systems
│  (Interface) │  → Translates between LLM and Rocq
└──────┬───────┘
       │
       ↓ (executes & verifies)
┌──────────────┐
│    Rocq      │  ← Verifies: type-checks, proves correctness
│  (Symbolic)  │  → Returns: success/failure, updated goals
└──────────────┘
```

**Workflow:**
1. LLM reads proof goal via LSP (`coq_open_goals`)
2. LLM generates candidate tactic(s) based on patterns learned from training
3. Tactics are applied via LSP (`coq_insert_tactic`)
4. Rocq verifies the tactic is type-correct and logically sound
5. If successful: proof progresses (new subgoals or QED)
6. If failed: error message guides LLM to try alternatives
7. Loop continues until proof is complete

### Why This Is Powerful

This architecture achieves:

**Guided Generation**: The LLM doesn't need to be "correct" — only creative. Rocq acts as a discriminator that filters out invalid proofs.

**Incremental Verification**: Each step is verified immediately, preventing cascading errors.

**Explainable AI**: Every LLM decision is justified by a formal proof that can be audited by humans.

**Learning from Mistakes**: Structured error feedback allows the LLM to refine its search strategy.

**Safe Automation**: The LLM can explore aggressively because Rocq guarantees soundness.

## Key Capabilities Enabled by LSP

### 1. Goal-Directed Search

The LLM can:
- Query the current proof goal: "Prove that `forall n, n + 0 = n`"
- Understand the hypothesis context: "Given: `n : nat`"
- Generate relevant tactics: "I'll try induction on `n`"

**LSP Tool**: `coq_open_goals` — returns structured goal representation

### 2. Speculative Execution

The LLM can:
- Try multiple tactics without modifying the file
- Quickly discard failures
- Only commit tactics that successfully reduce the goal

**LSP Tools**: `coq_get_state_at_pos`, `coq_run_tactic`, `coq_goals_for_state` (Pétanque API)

### 3. Interactive Proof Refinement

The LLM can:
- Incrementally build proofs tactic-by-tactic
- Respond to verification failures by adjusting strategy
- Learn which patterns work in different contexts

**LSP Tool**: `coq_insert_tactic` — applies tactic and returns updated goals

### 4. Error-Driven Learning

The LLM can:
- Receive structured error messages from Rocq
- Understand type mismatches, unification failures, etc.
- Adjust tactics based on specific error feedback

**LSP Feature**: All tools return structured error information

## Concrete Example: LLM Proving a Theorem

**Goal**: Prove `forall n, n + 0 = n` in Rocq

**Without LSP (traditional)**:
```coq
(* Human manually writes: *)
Lemma add_zero_r : forall n, n + 0 = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.
```

**With LSP (neurosymbolic)**:

```
1. LLM: "Let me check the goal"
   → coq_open_goals(file="Add.v", line=13)
   ← Goal: "forall n : nat, n + 0 = n"

2. LLM: "I need to prove a universal quantifier, I'll introduce the variable"
   → coq_insert_tactic(tactic="induction n.")
   ← Success! New goals:
      • Goal 1: "0 + 0 = 0"
      • Goal 2: "S n + 0 = S n" (with IH: "n + 0 = n")

3. LLM: "First goal is trivial by reflexivity"
   → coq_insert_tactic(tactic="- reflexivity.")
   ← Success! Goal 1 complete. Now on Goal 2.

4. LLM: "Let me simplify and use the induction hypothesis"
   → coq_insert_tactic(tactic="- simpl. rewrite IHn. reflexivity.")
   ← Success! Proof complete. QED.
```

**Key neurosymbolic elements**:
- LLM uses **pattern recognition** (recognizes ∀ needs intro, S needs induction)
- Rocq provides **verification** (each tactic is type-checked)
- LSP provides **interaction protocol** (query → propose → verify → iterate)

## Architecture: This Project

This MCP (Model Context Protocol) server implements the LSP bridge:

```
┌──────────────────────────────────────┐
│  OpenCode / LLM Agent                │
│  (Claude, GPT-4, etc.)               │
└─────────────┬────────────────────────┘
              │ MCP Protocol
              │ (tool calls)
┌─────────────▼────────────────────────┐
│  rocq-robot                          │
│  • Exposes 20+ MCP tools             │
│  • Manages document state            │
│  • Handles LSP ↔ MCP translation     │
└─────────────┬────────────────────────┘
              │ JSON-RPC (LSP + Pétanque)
              │ (stdio)
┌─────────────▼────────────────────────┐
│  rocq-lsp                            │
│  • Type-checks Rocq files            │
│  • Tracks proof state                │
│  • Executes tactics                  │
└─────────────┬────────────────────────┘
              │ OCaml API
              │
┌─────────────▼────────────────────────┐
│  Rocq Kernel                         │
│  • Formal verification engine        │
│  • Proof checker                     │
│  • Type theory implementation        │
└──────────────────────────────────────┘
```

### MCP Tools for Neurosymbolic Rocq

#### Core Proof Interaction Tools

| Tool | Neural Use Case | Symbolic Capability |
|------|----------------|---------------------|
| `coq_focus` | "Let me work on this proof" | Sets cursor to proof, returns full proof tree with goals & bullet stack |
| `coq_open_goals` | "What do I need to prove?" | Returns current goals & hypotheses at a proof position |
| `coq_insert_tactic` | "Try this tactic and show results" | Inserts tactic, auto-handles bullets, returns updated goals |
| `coq_try_tactic` | "Will this tactic work?" | Speculatively executes tactic without modifying file |
| `coq_undo` | "Roll back the last proof steps" | Removes the last N edit operations |
| `coq_reset_proof` | "Start this proof over" | Wipes proof body, replaces with fresh Admitted |

#### Proof Navigation & Structure

| Tool | Neural Use Case | Symbolic Capability |
|------|----------------|---------------------|
| `coq_add_lemma` | "I need a helper lemma" | Inserts lemma stub above specified proof |
| `coq_proof_state` | "What proof am I working on?" | Returns proof name, statements & rich context |

#### Knowledge & Search Tools

| Tool | Neural Use Case | Symbolic Capability |
|------|----------------|---------------------|
| `coq_search` | "What lemmas are relevant?" | Runs speculative `Search` query |
| `coq_check_term` | "What type does this have?" | Runs speculative `Check` command |
| `coq_about` | "Tell me about this definition" | Runs speculative `About` command |
| `coq_locate` | "Where is this defined?" | Runs speculative `Locate` to find definitions |
| `coq_require` | "Import this library" | Speculatively imports library for subsequent queries |

#### Low-Level State Management (Pétanque API)

| Tool | Neural Use Case | Symbolic Capability |
|------|----------------|---------------------|
| `coq_get_state_at_pos` | "Save this proof state" | Returns opaque state ID at position |
| `coq_run_tactic` | "Execute against this state" | Runs tactic against state ID, returns new state |
| `coq_goals_for_state` | "Show goals for this state" | Returns goals for a state ID |

#### File Operations

| Tool | Neural Use Case | Symbolic Capability |
|------|----------------|---------------------|
| `coq_apply_edit` | "Update specific text ranges" | Applies LSP-style text edits & re-syncs |
| `coq_check` | "Is the whole file valid?" | Forces full document checking |
| `coq_check_range` | "What's wrong in this region?" | Returns diagnostics for specific line range |

### Current Server Capabilities

- **Dynamic workspace switching**: opening a file from another Rocq project restarts `rocq-lsp` under the correct project root
- **Project-root detection**: walks upward looking for `_CoqProject`, `_RocqProject`, or `dune-project`
- **Readable goal output**: goal responses are formatted for MCP clients with hypotheses first and goal rendered compactly
- **Automatic bullet management**: `coq_insert_tactic` auto-prepends bullet prefixes (-, +, *) when the proof state requires them
- **Speculative execution**: both low-level Pétanque state APIs and higher-level single-call helpers (`coq_try_tactic`)
- **Proof navigation**: `coq_focus` returns complete proof tree including bullet stack depth and proof script
- **Helper lemma insertion**: `coq_add_lemma` inserts lemma stubs at the correct position in the file
- **Safe undo/reset**: `coq_undo` tracks edit operations (not just tactics), `coq_reset_proof` wipes proof to Admitted
- **Library management**: `coq_require` speculatively imports libraries for use in queries without modifying the file
- **Lifecycle hardening**: the LSP client waits for readiness, guards overlapping restarts, and retries transient states

## Benefits of This Approach

### For AI/LLM Developers
- **Structured Interface**: No need to parse Rocq syntax or output
- **Immediate Feedback**: Know instantly if a tactic succeeds
- **Safe Exploration**: Can't generate unsound proofs
- **Reduced Search Space**: Type system eliminates invalid candidates

### For Proof Engineers
- **AI Assistance**: Let LLMs handle tedious proof details
- **Guaranteed Soundness**: All proofs are formally verified
- **Interactive Refinement**: Guide AI when it gets stuck
- **Explainable Results**: Every proof step is auditable

### For Researchers
- **Benchmark Platform**: Test AI proof capabilities
- **Formal ML**: Train models on verified code
- **Safe Code Generation**: Generate formally verified programs
- **Hybrid Intelligence**: Study human-AI-proof collaboration

## Real-World Applications

### 1. Automated Theorem Proving
LLMs can tackle routine lemmas while experts focus on complex proofs.

### 2. Formally Verified Software
Generate code with machine-checked correctness proofs (e.g., crypto, compilers).

### 3. Mathematical Formalization
Convert natural language math into Rocq, assisted by LLMs.

### 4. Education
Interactive tutoring systems that teach both intuition (LLM) and rigor (Rocq).

### 5. AI Safety Research
Build verifiably safe AI systems with formal guarantees.

## Getting Started

### Prerequisites
```bash
# Install Rocq and rocq-lsp
opam install coq-lsp  # rocq-lsp coming soon

# Verify installation
coq-lsp --version  # or rocq-lsp --version
```

### Installation
```bash
cd rocq-robot
npm install
npm run build
```

### Usage with OpenCode

Add to your MCP settings:
```json
{
  "mcpServers": {
    "rocq-robot": {
      "command": "node",
      "args": [
        "/path/to/rocq-robot/dist/index.js",
        "--workspace-root",
        "/path/to/your/rocq/project"
      ]
    }
  }
}
```

The server can start with one workspace root and later switch automatically when a tool call targets a file inside a different Rocq project.

Then in OpenCode:
```
You: "Help me prove that addition is commutative in Rocq"

OpenCode: [Uses coq_open_goals to see the goal]
OpenCode: [Uses coq_insert_tactic to try "induction n"]
OpenCode: [Iteratively builds the proof using LSP feedback]
OpenCode: "Proof complete! Here's what I did..."
```

## Real Proof Example: Preservation Theorem

The repository includes a complete, working example in `examples/test_issues.v` demonstrating:

**Theorem**: Type preservation for PCF with references
```coq
Theorem preservation : forall t mu t' mu' T S,
  has_type [] S t T -> step t mu t' mu' ->
  heap_ok mu S ->
  exists S', extends S' S /\ heap_ok mu' S' /\ has_type [] S' t' T.
```

**Proof completed using only MCP tools**:
- ✅ 7 lemmas proved (extends_refl, nth_error_extends, weakening_store, substitution_preserves_typing_0, heap_lookup_type, heap_update_ok, **preservation**)
- ✅ All 21 cases of the induction on step relation completed
- ✅ Main preservation theorem fully closed with **Qed**
- ✅ Proper use of: inversion, induction, weakening lemmas, store extension, heap invariants

The LLM successfully:
1. Identified necessary helper lemmas (extends_refl, nth_error_extends, weakening_store, etc.)
2. Proved each lemma using appropriate tactics
3. Structured the main proof by induction on the step relation
4. Handled complex cases (S_RefV with store extension, S_DerefLoc with heap lookup)
5. Applied weakening lemmas where needed to adjust contexts
6. Managed bullet-structured subgoals across 21 cases

This demonstrates **neurosymbolic theorem proving in action**: the LLM proposes tactics guided by patterns, while Rocq verifies each step is logically sound.

## Additional Examples

See `examples/example.v` for simpler examples including:
- A finished proof (to query goals)
- An incomplete proof (to practice tactics)
- Test cases for each MCP tool

## The Future of Neurosymbolic Programming

This LSP-based architecture represents a paradigm shift:

**From**: "AI generates code, humans verify"  
**To**: "AI and proof assistants collaborate in real-time"

**From**: "LLMs are black boxes"  
**To**: "Every LLM decision has a formal proof"

**From**: "Formal verification is for experts"  
**To**: "LLMs make formal methods accessible"

### What's Already Possible

As demonstrated by the preservation theorem proof in this repository:
- ✅ **LLM-driven theorem proving**: Complete non-trivial proofs (21 cases, multiple helper lemmas)
- ✅ **Strategic proof planning**: Identifying needed lemmas and structuring induction proofs
- ✅ **Interactive refinement**: Real-time tactic application with immediate verification feedback
- ✅ **Error recovery**: Adjusting tactics based on Rocq's structured error messages
- ✅ **Proof management**: Adding lemmas, resetting proofs, undoing operations

### What's Coming

As LLMs improve and proof assistants expose richer APIs:
- **Automated formalization** of mathematical papers
- **AI-assisted discovery** of new theorems  
- **Verified AI systems** with formal safety guarantees
- **Natural language to formal proof** translation
- **Large-scale formal verification** of real-world software

## Learn More

- **Specification**: See `MCP_COQ_LSP_SPEC.md`
- **Implementation**: See `docs/IMPLEMENTATION.md`
- **Quick Start**: See `docs/QUICKSTART.md`
- **Project config detection**: See `docs/PROJECT-CONFIG-DETECTION.md`
- **Rocq Documentation**: https://rocq-prover.org/
- **rocq-lsp Project**: https://github.com/ejgallego/coq-lsp

## Contributing

This is a research prototype demonstrating neurosymbolic programming principles. Contributions welcome:
- Add support for other proof assistants (Lean, Isabelle)
- Improve tactic suggestion heuristics
- Build benchmark suites for AI proof capabilities
- Develop training datasets from verified code

## License

MIT License - See LICENSE file for details

---

**Built with**: TypeScript, rocq-lsp, Model Context Protocol

**Enables**: LLMs + Rocq = Formally Verified AI-Assisted Programming
