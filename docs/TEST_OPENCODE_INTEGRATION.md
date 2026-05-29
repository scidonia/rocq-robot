# Testing OpenCode + mcp-coq-lsp Integration

## ✅ Configuration Complete

Your `~/.config/opencode/opencode.json` now includes the MCP server for Coq/Rocq.

## Quick Test

### Step 1: Open the example project

```bash
cd /home/gavin/dev/Scidonia/geodesic/mcp-coq-lsp
opencode .
```

### Step 2: Test MCP tools are available

In OpenCode chat, try these commands:

#### Test 1: Query goals
```
What are the goals at line 7 of example.v?
```

**Expected:** OpenCode calls `coq_open_goals` and shows:
```
Goals:
n : nat
========================
n = n
```

#### Test 2: Check proof state
```
Show me the proof state at line 13 in example.v
```

**Expected:** OpenCode calls `coq_proof_state` and shows:
```json
{
  "proof": {
    "name": "add_zero",
    "statements": ["forall n : nat, n + 0 = n"]
  },
  "goals": {
    "goals": [
      {
        "hyps": [],
        "ty": "forall n : nat, n + 0 = n"
      }
    ],
    ...
  }
}
```

#### Test 3: Complete the incomplete proof
```
Complete the proof of add_zero in example.v using induction on n
```

**Expected:** OpenCode will:
1. Query the current goals
2. Insert tactics step-by-step using `coq_insert_tactic`
3. Check goals after each tactic
4. Complete the proof

#### Test 4: Try speculative execution
```
Without modifying example.v, what happens if we apply "intros." to add_zero?
```

**Expected:** OpenCode uses `coq_get_state_at_pos` + `coq_run_tactic` to test the tactic without file edits.

## Verify MCP Server is Running

### Check Logs

1. In OpenCode: `View` > `Output`
2. Select dropdown: `MCP Servers` or similar
3. Look for messages like:
   ```
   [coq-lsp MCP] Starting...
   [LSP initialized]: rocq-lsp v0.2.x
   ```

### Check Available Tools

In OpenCode chat, you can ask:
```
What MCP tools do you have available for Coq?
```

OpenCode should list:
- `coq_open_goals`
- `coq_proof_state`
- `coq_get_state_at_pos`
- `coq_run_tactic`
- `coq_goals_for_state`
- `coq_apply_edit`
- `coq_insert_tactic`
- `coq_check`

## What You Have Now

### Dual Setup: LSP + MCP

1. **LSP Server** (`lsp.coq-lsp`)
   - File: `/home/gavin/.opam/rocq-9/bin/coq-lsp`
   - Provides: Real-time syntax, diagnostics, hover
   - Runs: Always active when `.v` files are open

2. **MCP Server** (`mcp.coq-lsp`)
   - File: `/home/gavin/dev/Scidonia/geodesic/mcp-coq-lsp/dist/index.js`
   - Provides: AI-driven proof interaction
   - Runs: On-demand when OpenCode calls MCP tools

Both work together! The LSP gives you editor features, the MCP gives the AI proof manipulation powers.

## Configuration Details

Your full OpenCode config at `~/.config/opencode/opencode.json`:

```json
{
  "lsp": {
    "coq-lsp": {
      "command": ["/home/gavin/.opam/rocq-9/bin/coq-lsp"],
      "extensions": [".v"],
      "languageId": "rocq",
      "initialization": {
        "client_version": "opencode-0.1.0",
        "eager_diagnostics": true,
        "goal_after_tactic": true,
        "show_coq_info_messages": true,
        "show_notices_as_diagnostics": true,
        "check_only_on_request": false
      }
    }
  },
  "mcp": {
    "coq-lsp": {
      "type": "local",
      "command": [
        "node",
        "/home/gavin/dev/Scidonia/geodesic/mcp-coq-lsp/dist/index.js",
        "--workspace-root",
        "{workspaceRoot}"
      ]
    }
  }
}
```

## Troubleshooting

### If MCP server doesn't start

```bash
# Test manually
cd /home/gavin/dev/Scidonia/geodesic/mcp-coq-lsp
node dist/index.js --workspace-root .
```

If that works, the issue is with OpenCode configuration.

### If tools aren't available

1. Restart OpenCode
2. Check OpenCode version supports MCP
3. Check output logs for errors

### If queries fail

1. Make sure `_CoqProject` exists in workspace root
2. Check LSP server is running (separate from MCP)
3. Try `coq_check` to force document validation first

## Example Prompts to Try

Once everything is working, try these:

1. **Goal exploration:**
   > "Show me all the open goals in example.v"

2. **Proof completion:**
   > "Complete the proof of nat_eq_refl in example.v"

3. **Proof strategy:**
   > "What tactic should I use to prove add_zero in example.v?"

4. **Debugging:**
   > "Why does the proof at line 15 fail?"

5. **Refactoring:**
   > "Simplify the proof of nat_eq_refl using auto"

## Success Criteria

✅ You'll know it's working when:
1. OpenCode can query goals at any line in a `.v` file
2. OpenCode can insert tactics and see updated goals
3. OpenCode can complete proofs step-by-step
4. No errors in OpenCode output logs

## Next Steps

1. Open `mcp-coq-lsp` directory in OpenCode
2. Try the test commands above
3. Once working, use it on your real Coq projects!

For more details, see:
- [mcp-coq-lsp/OPENCODE_INTEGRATION.md](mcp-coq-lsp/OPENCODE_INTEGRATION.md)
- [mcp-coq-lsp/README.md](mcp-coq-lsp/README.md)
