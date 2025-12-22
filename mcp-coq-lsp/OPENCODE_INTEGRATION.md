# OpenCode Integration Guide

## Configuration Added

Your `~/.config/opencode/opencode.json` has been updated with the MCP server configuration.

### What was added:

```json
"mcp": {
  "morph-mcp": { ... },  // Your existing MCP server
  "coq-lsp": {           // NEW: MCP server for Coq/Rocq
    "type": "local",
    "command": [
      "node",
      "/home/gavin/dev/Scidonia/geodesic/mcp-coq-lsp/dist/index.js",
      "--workspace-root",
      "{workspaceRoot}"
    ]
  }
}
```

### How it works:

- The `{workspaceRoot}` placeholder will be replaced with the root directory of your current OpenCode workspace
- The MCP server will automatically use that as the Coq project root
- It will look for `_CoqProject` or `_RocqProject` in that directory

## Usage

### 1. Open a Coq Project

```bash
# Open OpenCode in a directory with Coq files
cd /path/to/your/coq/project
opencode .
```

Make sure your project has either:
- `_CoqProject` file, or
- `_RocqProject` file

### 2. Available Tools

Once OpenCode is running, you'll have access to these MCP tools for `.v` files:

#### Query Goals
Ask OpenCode:
> "What are the goals at line 42 in MyProof.v?"

This calls `coq_open_goals` internally.

#### Get Proof Context
Ask OpenCode:
> "Show me the proof state at line 50 in Theorem.v"

This calls `coq_proof_state` internally.

#### Insert Tactics
Ask OpenCode:
> "Insert the tactic 'intros.' at line 30 in Proof.v"

This calls `coq_insert_tactic` internally.

#### Speculative Execution
Ask OpenCode:
> "Try the tactic 'reflexivity.' without modifying the file"

This uses `coq_get_state_at_pos` + `coq_run_tactic` internally.

#### Apply Edits
Ask OpenCode:
> "Replace lines 40-45 with this new proof script: ..."

This calls `coq_apply_edit` internally.

#### Check Document
Ask OpenCode:
> "Check if MyProof.v compiles successfully"

This calls `coq_check` internally.

## Example Workflow

### Scenario: Completing an incomplete proof

1. Open a Coq file with an incomplete proof:
   ```coq
   Lemma add_comm : forall n m, n + m = m + n.
   Proof.
     (* Need to complete this *)
   Admitted.
   ```

2. Ask OpenCode:
   > "What are the goals for add_comm at line 2?"

3. OpenCode shows:
   ```
   Goals:
   n, m : nat
   ========================
   n + m = m + n
   ```

4. Ask OpenCode:
   > "Complete this proof using induction on n"

5. OpenCode will:
   - Call `coq_insert_tactic` to insert tactics
   - Check goals after each step
   - Continue until the proof is complete

6. Final result:
   ```coq
   Lemma add_comm : forall n m, n + m = m + n.
   Proof.
     intros n m.
     induction n as [| n' IHn'].
     - simpl. rewrite Nat.add_0_r. reflexivity.
     - simpl. rewrite IHn'. rewrite Nat.add_succ_r. reflexivity.
   Qed.
   ```

## Dual LSP + MCP Setup

Your config now has **both** LSP and MCP for Coq:

### LSP (`lsp.coq-lsp`)
- Provides: syntax highlighting, diagnostics, hover info
- Real-time feedback in the editor
- Document symbols, go-to-definition
- Located at: `/home/gavin/.opam/rocq-9/bin/coq-lsp`

### MCP (`mcp.coq-lsp`)
- Provides: programmatic proof interaction for the AI
- Goal querying, tactic insertion, speculative execution
- Enables AI-driven proof development
- Located at: `/home/gavin/dev/Scidonia/geodesic/mcp-coq-lsp/dist/index.js`

Both work together seamlessly!

## Verifying the Setup

### Check MCP Server is Running

When you open a Coq project in OpenCode, check the output panel:
```
View > Output > Select "MCP Servers" or "Extensions"
```

You should see logs like:
```
[coq-lsp MCP] Starting...
[coq-lsp MCP] LSP initialized: rocq-lsp v0.2.x
```

### Test with Example File

```bash
cd /home/gavin/dev/Scidonia/geodesic/mcp-coq-lsp
opencode .
```

Then ask:
> "Show me the goals at line 7 of example.v"

Expected response:
```
Goals:
n : nat
========================
n = n
```

## Troubleshooting

### MCP server not starting

Check OpenCode logs:
```
View > Output > MCP Servers
```

Common issues:
1. **Node not found**: Make sure `node` is on PATH
2. **coq-lsp not found**: Make sure `/home/gavin/.opam/rocq-9/bin/coq-lsp` exists
3. **Workspace root wrong**: Make sure you opened OpenCode in a directory with `_CoqProject`

### No goals returned

1. Check the file has a `_CoqProject` in the workspace root
2. Try calling `coq_check` first to force document validation
3. Verify the line number is inside a proof

### File edits not applying

1. Make sure the file is saved
2. Check file permissions (needs write access)
3. Verify range positions are correct (0-based lines)

## Advanced Configuration

### Use a Different coq-lsp

If you want to use a different `coq-lsp` binary:

```json
"coq-lsp": {
  "type": "local",
  "command": [
    "node",
    "/home/gavin/dev/Scidonia/geodesic/mcp-coq-lsp/dist/index.js",
    "--workspace-root",
    "{workspaceRoot}",
    "--coq-lsp-path",
    "/custom/path/to/coq-lsp"
  ]
}
```

### Multiple Coq Projects

If you work with multiple Coq projects, the `{workspaceRoot}` variable will automatically adjust to whichever project you have open.

### Disable On-Demand Checking

By default, the MCP server uses on-demand checking (only checks when you query). To enable continuous checking:

Add to the command:
```json
"command": [
  "node",
  "/home/gavin/dev/Scidonia/geodesic/mcp-coq-lsp/dist/index.js",
  "--workspace-root",
  "{workspaceRoot}"
  // Note: continuous checking would be configured via LSP initializationOptions
  // The MCP server currently uses on-demand by default (good for AI workflows)
]
```

## Next Steps

1. ✅ Configuration is complete
2. Open a Coq project in OpenCode
3. Try the example workflows above
4. Start proving theorems with AI assistance!

## References

- Full tool documentation: [README.md](README.md)
- Architecture details: [IMPLEMENTATION.md](IMPLEMENTATION.md)
- Specification: [../MCP_COQ_LSP_SPEC.md](../MCP_COQ_LSP_SPEC.md)
