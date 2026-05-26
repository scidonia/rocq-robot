# ✅ Setup Complete!

## What Was Done

Your OpenCode is now configured to use **mcp-coq-lsp** for AI-assisted Coq/Rocq theorem proving!

### 1. Configuration Updated ✅

File: `~/.config/opencode/opencode.json`

Added MCP server entry:
```json
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
```

### 2. How to Use

#### Start OpenCode in a Coq project:
```bash
cd /path/to/your/coq/project  # Must have _CoqProject file
opencode .
```

#### Try these commands in OpenCode chat:
- "What are the goals at line X in MyFile.v?"
- "Complete this proof using induction"
- "Insert the tactic 'intros.' at line X"
- "What happens if I apply reflexivity here?"

### 3. Quick Test

```bash
# Open the example project
cd /home/gavin/dev/Scidonia/geodesic/mcp-coq-lsp
opencode .

# Then in OpenCode chat:
# "Show me the goals at line 7 of example.v"
```

### 4. What You Get

🎯 **8 MCP Tools for Coq:**
- `coq_open_goals` - Query goals at any position
- `coq_proof_state` - Get full proof context
- `coq_get_state_at_pos` - Get proof state ID
- `coq_run_tactic` - Try tactics without editing
- `coq_goals_for_state` - Goals from state ID
- `coq_apply_edit` - Apply text edits
- `coq_insert_tactic` - Insert tactics with goal updates
- `coq_check` - Force document validation

🔧 **Dual Setup:**
- **LSP**: Real-time syntax, diagnostics (you already had this)
- **MCP**: AI proof interaction (newly added)

### 5. Architecture

```
You ask OpenCode
      ↓
OpenCode AI decides to call MCP tool
      ↓
mcp-coq-lsp (Node.js server)
      ↓
rocq-lsp (Your existing LSP server)
      ↓
Coq/Rocq kernel
```

### 6. Documentation

- **Usage guide**: [OPENCODE_INTEGRATION.md](OPENCODE_INTEGRATION.md)
- **Testing**: [../TEST_OPENCODE_INTEGRATION.md](../TEST_OPENCODE_INTEGRATION.md)
- **Full docs**: [README.md](README.md)
- **Architecture**: [IMPLEMENTATION.md](IMPLEMENTATION.md)

### 7. Troubleshooting

If something doesn't work:

1. Check OpenCode output logs: `View > Output > MCP Servers`
2. Verify manually: `node dist/index.js --workspace-root .`
3. Make sure workspace has `_CoqProject` file
4. See [OPENCODE_INTEGRATION.md](OPENCODE_INTEGRATION.md) troubleshooting section

### 8. What's Next

🚀 **You're ready to:**
1. Open any Coq project in OpenCode
2. Ask the AI to help with proofs
3. Let OpenCode query goals and insert tactics
4. Leverage AI for theorem proving!

## Example Workflow

```
You: "I have an incomplete proof in Theorems.v at line 50. Can you help?"

OpenCode: [calls coq_proof_state]
"I see you're proving forall n, n + 0 = n. Let me help..."

OpenCode: [calls coq_insert_tactic]
"I'll insert 'intros n.'"

OpenCode: [calls coq_open_goals]
"Now the goal is: n + 0 = n. I'll use induction..."

OpenCode: [calls coq_insert_tactic]
"Inserting 'induction n as [|n IHn].'"

... [continues until proof is complete]

OpenCode: "Proof complete! ✅"
```

---

**🎉 Congratulations! Your AI-assisted Coq environment is ready!**

For questions, see the documentation or check the test file:
- Test: `cd mcp-coq-lsp && opencode .`
- Ask: "Show me the goals at line 7 of example.v"
