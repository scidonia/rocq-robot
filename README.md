# 🤖 rocq-piler

**Let rocq-piler do the heavy lifting for your proofs.**

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

## The Hash-Driven Workflow

rocq-piler uses a **content-addressed admit system**: every open goal in a proof has a unique hash computed from its goal text. This turns proof construction into a clean cycle:

```
focus_proof → get hashes → insert_tactic(admit_hash=X) → repeat until Qed
```

### Example: Proving `(True /\ True) /\ True` in 3 calls

```
1. focus_proof(file="Thm.v", name="deep_conj")
   ← 1 admit: abc123  L7: (True / True) / True

2. insert_tactic(admit_hash="abc123", tactic="split.\n- admit.\n- admit.")
   ← 2 admits remaining:
      def456  L8: True / True   (hyps: empty, goal: True / True)
      ghi789  L9: True           (hyps: empty, goal: True)

3. insert_tactic(admit_hash="def456", tactic="split; exact I.")
   insert_tactic(admit_hash="ghi789", tactic="exact I.")
   ← Qed applied
```

**Why hashes?** Every admit with the same goal text shares the same hash. Close four `True` admits at once — across any bullet depth — in a single call. The LLM reads hashes from `focus_proof`, writes tactics for them, and counts down to `Qed`.

### Example: Dependent Type Progress Theorem in 9 calls

See `examples/dep_vec.v` for a full dependently-typed language (Nat + Vec n) with both preservation and progress theorems proved entirely via hash-driven MCP calls:

```
1. focus_proof → hash for the theorem goal
2. insert_tactic(admit_hash=X, tactic="{induction + 7 stubs}") → 7 case hashes with hyps+goal inline
3-9. insert_tactic(admit_hash=<case>, tactic="...") × 7 → Qed
```

Each response shows **hypotheses + goal** per admit, so the LLM writes each case's tactic without extra `focus_proof` calls.

### MCP Tools

| Tool | Description |
|------|-------------|
| `focus_proof` | One-stop shop: proof state, script, all open admits with hashes + hyps + goals |
| `insert_tactic` | Insert a tactic; pass `admit_hash` to target specific admits by hash; multi-line blocks supported |
| `try_step` | Speculatively execute a tactic without modifying the file |
| `open_goals` | Quick goal query with compact/Prev mode options |
| `proof_state` | Full proof context including name, statements, goal state |
| `undo_step` | Roll back the last N edit operations |
| `reset_proof` | Wipe a proof body to fresh `Admitted.` |
| `add_lemma` / `delete_lemma` | Insert/remove lemma stubs |
| `delete_step` | Remove the last tactic line from a proof |
| `edit_file` | Find-and-replace text edits with LSP re-sync |
| `check_file` | Force full document checking |
| `check_range` | Get diagnostics for a specific line range |
| `search_lemmas` / `inspect_term` / `inspect_about` / `locate_term` / `require_lib` | Knowledge & search |
| `snap_state` / `exec_tactic` / `state_goals` | Low-level Pétanque API |

### Current Server Capabilities

- **Content-addressed admits**: every open goal gets a hash — same goal text = same hash, close all matching admits at once across any bullet depth
- **Hypotheses + goal per admit**: `focus_proof` and `insert_tactic` responses include full hypothesis context for each open admit
- **Multi-line stub insertion**: open a proof, insert N bulleted admits, and get N hashes back — all in one `insert_tactic` call
- **Re-seal with multi-goal expansion**: when a tactic produces N > 1 goals, they are optionally expanded to N individually addressable bulleted admits
- **Auto-Qed**: proof automatically closed when all tactic admits and focused goals are eliminated; guarded against premature firing when background goals remain
- **Dynamic workspace switching**: automates restarting `rocq-lsp` under different project roots
- **Speculative execution**: try tactics safely via `try_step` or Pétanque state APIs before committing
- **Bullet-aware proof navigation**: `focus_proof` reports bullet stack depth, given-up counts, and sibling context
- **Safe undo/reset**: tracks edit operations, supports multi-step undo

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
cd rocq-piler
npm install
npm run build
```

### Usage with OpenCode

Add to your MCP settings:
```json
{
  "mcpServers": {
    "rocq-piler": {
      "command": "node",
      "args": [
        "/path/to/rocq-piler/dist/index.js",
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

## Real Proof Example: Dependent Type System

See `examples/dep_vec.v` for a complete, working example of a simple dependently-typed language:

**Language**: Nat + Vec n — base type Nat, dependent Vec n of length n  
**Theorems proved via MCP tools**:
- ✅ **Preservation** (7 cases): `has_type t T → step t t' → has_type t' T` — proved in 9 MCP calls  
- ✅ **Progress** (7 cases): `has_type t T → value t ∨ ∃ t', step t t'` — proved in 9 MCP calls  

Both proofs use the same pattern: `focus_proof` → multi-line stub → case hashes with hyps+goal → close by hash one-by-one.

A larger PCF+References example is in `examples/test_issues.v`:
- ✅ 7 helper lemmas + preservation theorem (21 cases)  
- ✅ Full heap semantics with store extension and weakening  
- ✅ All cases closed with `Qed`

## Additional Examples

- `examples/dep_vec.v` — Dependent type system (Nat + Vec n) with preservation and progress theorems, proved hash-driven
- `examples/test_issues.v` — PCF + References (21-case preservation theorem)
- `examples/example.v` — Simple examples for each MCP tool

## The Future of Neurosymbolic Programming

This LSP-based architecture represents a paradigm shift:

**From**: "AI generates code, humans verify"  
**To**: "AI and proof assistants collaborate in real-time"

**From**: "LLMs are black boxes"  
**To**: "Every LLM decision has a formal proof"

**From**: "Formal verification is for experts"  
**To**: "LLMs make formal methods accessible"

### What's Already Possible

As demonstrated by the proofs in this repository:
- ✅ **Hash-driven proof construction**: `focus_proof` → get hashes → `insert_tactic(admit_hash=X)` → repeat until Qed
- ✅ **Multi-case induction proofs**: 7 cases closed in 9 total MCP calls with full hypothesis context per case
- ✅ **Multi-bullet depth**: same hash works across `-`/`+`/`*` bullet levels — close all matching admits in one call
- ✅ **Dependent type progress + preservation**: Nat + Vec n language fully verified
- ✅ **Interactive refinement**: speculative execution via `try_step` with immediate feedback

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

**Design**: Content-addressed admits, hash-driven workflow, full hypothesis context per goal
