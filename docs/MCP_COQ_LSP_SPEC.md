# MCP Server Spec: `mcp-coq-lsp` (opencode integration)

## 0. Summary

This document specifies an MCP server intended to be used by **opencode** to interact with **Coq/Rocq** proofs via **`coq-lsp` / `rocq-lsp`**.

The server must be able to:

1. Query **open goals** at a position in a file.
2. Interrogate the **current proof state** (goal stack, focused goals, messages, errors).
3. **Drive proofs by editing code** (insert/replace tactics / proof scripts), then re-check and return updated goals.

The design leverages two APIs exposed by `rocq-lsp`:

- LSP extension `proof/goals` (a goal display request).
- JSON-RPC “**Pétanque**” API for low-overhead proof-state manipulation (`petanque/get_state_at_pos`, `petanque/run`, `petanque/goals`, etc.).


## 1. Background: Coq/Rocq tooling ecosystem (what to build on)

The “modern” Coq tooling stack has converged around these interaction layers:

- **`coqtop` / `rocqtop`**: classic toplevel; direct interaction is possible but brittle for editor-like workflows.
- **`coqidetop`**: the CoqIDE protocol endpoint; mostly legacy today.
- **SerAPI**: structured API around Coq; historically popular for programmatic use.
- **`coq-lsp` / `rocq-lsp`**: an LSP server built on Flèche, with extra machine-friendly APIs:
  - `proof/goals` request for goals-at-point.
  - `coq/getDocument` for spans/AST/goals.
  - **Pétanque**: fast proof-state and command execution API designed for AI/automation.

For an opencode+LLM integration, `rocq-lsp` is the best “front door” because it:

- Understands the *file* as a document (positions, ranges, incremental checking).
- Provides goals at arbitrary positions.
- Provides a low-overhead “sandbox” (`petanque`) to test tactics/commands without committing edits.


## 2. Recommended implementation language

### Recommendation: **TypeScript (Node.js)**

TypeScript is the most practical choice for an MCP server that talks to `rocq-lsp` because:

- **MCP ecosystem**: the most widely used MCP SDK and examples are in Node/TypeScript.
- **LSP/JSON-RPC ecosystem**: Node has mature, well-tested libraries for JSON-RPC/LSP framing (stdio), including `vscode-jsonrpc` and related tooling.
- **Concurrency & streaming**: Node handles a long-lived subprocess (the LSP server) and multiplexed MCP tool calls cleanly.
- **Interop**: the server can spawn and control `coq-lsp` as a child process and implement both LSP requests and Pétanque calls over JSON-RPC.

### When Python is reasonable

Python is viable if the project strongly prefers Python (this repo is Python), and especially if you plan to reuse Python clients like **Coqpyt** (a Python client for `rocq-lsp`, referenced by `rocq-lsp`’s docs).

The tradeoffs:

- Python has MCP SDK support, but the LSP-client ecosystem is less standardized than Node’s.
- You may end up writing (and maintaining) more JSON-RPC/LSP transport code yourself.

**Net**: default to **TypeScript** unless there is a strong “single-language repo” constraint.


## 3. Scope and non-goals

### In scope

- Start and manage a `rocq-lsp` subprocess (stdio JSON-RPC).
- Maintain open documents (URI, version, text) and synchronize edits.
- Query goals at a given position.
- Query proof state (goals + focus stack + messages + last error).
- Apply edits to a proof file (insert/replace tactic blocks) and re-check.
- Optionally: “speculative” tactic execution via Pétanque before editing the file.

### Non-goals

- Full-featured editor UI.
- Proof search / tactic synthesis itself (that’s the LLM’s job).
- Supporting non-`file:///` URIs.
- Being a replacement for a full LSP client (we implement only what opencode needs).


## 4. Architecture

### 4.1 Processes and protocols

- **MCP server** (this project): stdio MCP transport with tool endpoints.
- **`rocq-lsp`** subprocess: stdio JSON-RPC 2.0 (LSP + extensions + Pétanque).

The MCP server acts as a bridge:

```
opencode/LLM  <->  MCP (tools/resources)  <->  mcp-coq-lsp  <->  rocq-lsp  <->  Coq/Rocq
```

### 4.2 Document model

The server tracks for each open file:

- `path` (workspace-relative or absolute)
- `uri` = `file:///...`
- `languageId` = `coq` / `rocq` (for `.v` files)
- `version` (monotonic int)
- `text` (full contents)

Important constraint from `rocq-lsp`: `textDocument/didChange` currently supports `TextDocumentSyncKind.Full`, so the server should send full text on each change.

### 4.3 Proof-state sources

- “User-facing goals at point” should come from `proof/goals`.
- “Automation-friendly state execution” should use Pétanque:
  - `petanque/get_state_at_pos` to get an opaque `stateId`.
  - `petanque/run` to execute a tactic/command and get a new `stateId`.
  - `petanque/goals` to retrieve a goal configuration from a `stateId`.
  - `petanque/proof_info(_at_pos)` to identify lemma/proof context.

### 4.4 Editing strategy (driving proofs)

The server supports two modes:

1. **Direct edit mode (authoritative)**
   - Apply an edit to the file (insert tactic text / replace a range).
   - Push updated text to `rocq-lsp` (`didChange`).
   - Query `proof/goals` again.

2. **Speculative mode (recommended)**
   - Use Pétanque to try a tactic against a state at a position.
   - If it behaves as intended, then apply the corresponding textual edit.

This reduces “edit churn” and makes the system more predictable.


## 5. MCP Surface Area

The MCP server exposes **tools** (and optionally **resources**) designed for opencode.

### 5.1 Tool naming conventions (opencode)

opencode’s tool picker works best when tool names are stable, searchable, and collision-free.

Conventions for this server:

- Tool names use `snake_case`.
- Tool names are prefixed with `coq_` (e.g. `coq_open_goals`) to avoid collisions with other MCP servers.
- Avoid `/` and `.` in tool names (some clients treat them as namespaces; opencode generally expects simple names).
- Do not rename tools once published; if a breaking change is required, add a new tool (e.g. `coq_open_goals_v2`) and keep the old one as an alias if possible.

If opencode later standardizes on a different convention, implement a compatibility layer by exposing *additional* alias tool names rather than migrating existing names.

### 5.2 Common types

All tools take a `file` parameter as a filesystem path, and internally convert to a `file:///` URI.

Positions are LSP `Position` (0-based):

```ts
type Position = { line: number; character: number };
```

Ranges are LSP `Range`:

```ts
type Range = { start: Position; end: Position };
```


## 6. Tools

### 6.1 `coq_open_goals`

Get current open goals at a given file position.

**Input**

```json
{
  "file": "path/to/Foo.v",
  "position": { "line": 42, "character": 0 },
  "pp_format": "Str",
  "compact": true,
  "mode": "After"
}
```

**Behavior**

- Ensures the document is opened and synchronized to `rocq-lsp`.
- Issues `proof/goals` request.

**Output**

```json
{
  "range": {"start": {"line": 41, "character": 0}, "end": {"line": 43, "character": 3}},
  "goals": {
    "goals": [
      {"hyps": [{"names": ["n"], "ty": "nat"}], "ty": "n = n"}
    ],
    "stack": [],
    "shelf": [],
    "given_up": []
  },
  "messages": [],
  "error": null
}
```

Notes:

- `mode` corresponds to `rocq-lsp`’s `proof/goals` mode (`Prev`/`After`).
- The server should default to `pp_format = "Str"` for LLM-friendliness.


### 6.2 `coq_proof_state`

Return a richer snapshot of proof context at a position.

**Input**

```json
{
  "file": "path/to/Foo.v",
  "position": { "line": 42, "character": 0 }
}
```

**Behavior**

- Calls `coq_open_goals`.
- Also calls `petanque/proof_info_at_pos` to return proof name / statements (if any).

**Output**

```json
{
  "proof": {"name": "foo", "statements": ["forall n, n = n"], "range": null},
  "goals": {"goals": [...], "stack": [...], "shelf": [...], "given_up": [...]},
  "messages": [...],
  "error": null
}
```


### 6.3 `coq_get_state_at_pos`

Get an opaque state identifier from a file position.

**Input**

```json
{
  "file": "path/to/Foo.v",
  "position": { "line": 42, "character": 0 },
  "memo": true,
  "hash": true
}
```

**Output**

```json
{
  "state_id": 123,
  "hash": 456,
  "proof_finished": false,
  "feedback": []
}
```


### 6.4 `coq_run_tactic`

Run a tactic/command against an existing `state_id` (speculative execution).

**Input**

```json
{
  "state_id": 123,
  "tactic": "intros. reflexivity.",
  "memo": true,
  "hash": true
}
```

**Output**

```json
{
  "state_id": 124,
  "hash": 789,
  "proof_finished": true,
  "feedback": [[1, "..."]]
}
```


### 6.5 `coq_goals_for_state`

Return goals for a `state_id`.

**Input**

```json
{ "state_id": 124, "compact": true }
```

**Output**

```json
{
  "goals": {"goals": [], "stack": [], "shelf": [], "given_up": []}
}
```


### 6.6 `coq_apply_edit`

Apply a textual edit to a file and re-sync with `rocq-lsp`.

This is the core “drive the proof by editing code” primitive.

**Input**

```json
{
  "file": "path/to/Foo.v",
  "edits": [
    {
      "range": {
        "start": {"line": 50, "character": 0},
        "end": {"line": 50, "character": 0}
      },
      "newText": "  intros.\n"
    }
  ]
}
```

**Behavior**

- Loads current file text (from disk or from internal cache).
- Applies edits in descending order by position (standard LSP edit semantics).
- Writes file back to disk.
- Sends `textDocument/didChange` with full text and increments version.

**Output**

```json
{
  "file": "path/to/Foo.v",
  "new_version": 17
}
```


### 6.7 `coq_insert_tactic`

High-level helper: insert a tactic into the current proof and return updated goals.

**Input**

```json
{
  "file": "path/to/Foo.v",
  "position": {"line": 50, "character": 2},
  "tactic": "intros.",
  "follow_with_goals": true
}
```

**Behavior**

- Computes insertion point (either exact `position`, or start of line).
- Inserts `tactic` with trailing `\n`.
- Calls `coq_apply_edit`.
- If `follow_with_goals`, calls `coq_open_goals` at the same (or next) position.

**Output**

```json
{
  "applied": true,
  "goals": { ... },
  "messages": [ ... ],
  "error": null
}
```


### 6.8 `coq_check`

Force a “check” pass by asking `rocq-lsp` for document completion.

**Input**

```json
{ "file": "path/to/Foo.v" }
```

**Behavior**

- Calls `coq/getDocument` with `ast=false` and optionally `goals="Str"`.

**Output**

```json
{
  "completed": {"status": "Yes", "range": {"start": {"line": 0,"character": 0}, "end": {"line": 120,"character": 0}}},
  "spans": [
    {"range": {"start": {"line": 0,"character": 0}, "end": {"line": 2,"character": 0}}}
  ]
}
```


## 7. Initialization and configuration

### 7.1 Locating and launching `rocq-lsp`

The server should be configurable with:

- `rocqLsp.path` (default: `coq-lsp` or `rocq-lsp` on PATH)
- `rocqLsp.args` (optional)
- `root` (workspace root folder)

It should start `rocq-lsp` once and keep it alive across tool calls.

### 7.2 LSP initialize

The server must send LSP `initialize` with:

- Workspace folder(s)
- `initializationOptions` tuned for automation

Recommended defaults:

- `check_only_on_request = true` (avoid background CPU in agent loops)
- `pp_type = 0` (string output)
- `goal_after_tactic = true`


## 8. Error handling

- All JSON-RPC failures should be converted into MCP tool errors with:
  - a short human-readable summary
  - any `RocqErrorData.feedback` attached (when present)
- `coq_apply_edit` must validate:
  - file exists and is within configured `root` (unless explicitly allowed)
  - edit ranges are within document bounds


## 9. Performance considerations

- Because `didChange` is full-text, batch edits when possible.
- Prefer Pétanque for repeated tactic trial.
- Cache document text and version to avoid redundant disk IO.


## 10. Security considerations

- Treat the workspace root as a sandbox; do not allow arbitrary file writes outside it by default.
- Do not execute arbitrary shell commands.


## 11. Acceptance criteria

A minimal MVP is complete when opencode can:

1. Open a `.v` file and ask for goals at a cursor position (`coq_open_goals`).
2. Insert a tactic line (`coq_insert_tactic`) and see goals update.
3. Use Pétanque to try a tactic without editing the file (`coq_get_state_at_pos` + `coq_run_tactic` + `coq_goals_for_state`).
4. Recover structured feedback when a tactic fails.


## 12. References

- `rocq-lsp` protocol documentation (extensions + Pétanque):
  - https://raw.githubusercontent.com/ejgallego/rocq-lsp/main/etc/doc/PROTOCOL.md
- `rocq-lsp` project (overview, pointers to related tooling like Coqpyt):
  - https://github.com/ejgallego/rocq-lsp
