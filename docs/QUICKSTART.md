# Quick Start Guide

## Prerequisites

1. **Install Coq/Rocq LSP server**
   ```bash
   opam install coq-lsp
   # Verify installation
   which coq-lsp
   ```

2. **Install Node.js** (>= 18)
   ```bash
   node --version  # Should be >= 18.x
   ```

## Setup (First Time)

```bash
# Navigate to mcp-coq-lsp directory
cd mcp-coq-lsp

# Install dependencies and build
npm install

# The build happens automatically during install
# If you need to rebuild manually:
npm run build
```

## Test the Server (Standalone)

```bash
# Run with the example file
node dist/index.js --workspace-root .
```

The server is now running and waiting for MCP requests on stdin/stdout.

## Configure with OpenCode

### Step 1: Find absolute paths

```bash
# Get the absolute path to the server
pwd
# Example output: /home/user/geodesic/mcp-coq-lsp

# Get the absolute path to your Coq project
cd /path/to/your/coq/project
pwd
```

### Step 2: Add to OpenCode config

In your OpenCode settings, add to MCP servers configuration:

```json
{
  "mcpServers": {
    "coq-lsp": {
      "command": "node",
      "args": [
        "/home/user/geodesic/mcp-coq-lsp/dist/index.js",
        "--workspace-root",
        "/path/to/your/coq/project"
      ]
    }
  }
}
```

### Step 3: Restart OpenCode

The MCP server will now be available in OpenCode's tool picker.

## Quick Test Workflow

### 1. Query Goals

Ask OpenCode: "What are the goals at line 7 of example.v?"

OpenCode should call `coq_open_goals` with:
```json
{
  "file": "example.v",
  "position": { "line": 7, "character": 0 }
}
```

### 2. Insert a Tactic

Ask OpenCode: "Insert 'intros.' at line 13 of example.v"

OpenCode should call `coq_insert_tactic` with:
```json
{
  "file": "example.v",
  "position": { "line": 13, "character": 2 },
  "tactic": "intros.",
  "follow_with_goals": true
}
```

### 3. Try Speculative Execution

1. Get a state: `coq_get_state_at_pos`
2. Try a tactic: `coq_run_tactic` with state_id
3. Check results without modifying the file!

## Troubleshooting

### Server won't start

```bash
# Check if coq-lsp is installed
which coq-lsp

# If not found, install it
opam install coq-lsp

# Try running manually
node dist/index.js --coq-lsp-path /path/to/coq-lsp --workspace-root .
```

### Document not found errors

Make sure:
1. Your workspace root contains a `_CoqProject` or `_RocqProject` file
2. File paths are relative to the workspace root
3. Files have `.v` extension

### Goals not showing

The server uses on-demand checking. Try:
1. Call `coq_check` first to force document validation
2. Or query goals at a position - this will trigger checking up to that point

## Example Queries

### Get goals at a position
```json
{
  "tool": "coq_open_goals",
  "arguments": {
    "file": "example.v",
    "position": { "line": 7, "character": 0 }
  }
}
```

### Get proof context
```json
{
  "tool": "coq_proof_state",
  "arguments": {
    "file": "example.v",
    "position": { "line": 13, "character": 0 }
  }
}
```

### Insert a tactic
```json
{
  "tool": "coq_insert_tactic",
  "arguments": {
    "file": "example.v",
    "position": { "line": 14, "character": 2 },
    "tactic": "intros.",
    "follow_with_goals": true
  }
}
```

### Check document
```json
{
  "tool": "coq_check",
  "arguments": {
    "file": "example.v"
  }
}
```

## Development Mode

If you're modifying the server code:

```bash
# Watch mode (auto-rebuilds on changes)
npm run watch

# In another terminal, test with tsx (no build needed)
npm run dev -- --workspace-root .
```

## Next Steps

- Read [README.md](README.md) for full documentation
- Read [IMPLEMENTATION.md](IMPLEMENTATION.md) for architecture details
- Read [../MCP_COQ_LSP_SPEC.md](../MCP_COQ_LSP_SPEC.md) for the full specification
- Try the example file: `example.v`
- Create your own Coq project with `_CoqProject` file

## Support

If you encounter issues:
1. Check the OpenCode output panel for MCP server logs
2. Check stderr output from rocq-lsp
3. Verify your Coq project structure (`_CoqProject` file)
4. Ensure file paths are correct and relative to workspace root
