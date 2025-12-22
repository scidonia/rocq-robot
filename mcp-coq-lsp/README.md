# mcp-coq-lsp

MCP server for Coq/Rocq proof assistant integration via `coq-lsp` / `rocq-lsp`.

This server enables OpenCode (and other MCP clients) to interact with Coq/Rocq proofs by:
- Querying open goals at any position in a `.v` file
- Interrogating proof state (goals, messages, errors)
- Driving proofs by editing code (inserting tactics, applying edits)
- Using Pétanque for speculative tactic execution without file edits

## Requirements

- Node.js >= 18
- `coq-lsp` or `rocq-lsp` installed and available on PATH
  - Install via: `opam install coq-lsp`
  - Or see: https://github.com/ejgallego/rocq-lsp

## Installation

```bash
cd mcp-coq-lsp
npm install
npm run build
```

## Usage

### With OpenCode

Add to your OpenCode MCP configuration:

```json
{
  "mcpServers": {
    "coq-lsp": {
      "command": "node",
      "args": [
        "/path/to/geodesic/mcp-coq-lsp/dist/index.js",
        "--workspace-root",
        "/path/to/your/coq/project"
      ]
    }
  }
}
```

### Standalone (for testing)

```bash
# Run the server
node dist/index.js --workspace-root /path/to/coq/project

# With custom coq-lsp path
node dist/index.js \
  --workspace-root /path/to/project \
  --coq-lsp-path /custom/path/to/coq-lsp
```

## Available Tools

### `coq_open_goals`

Get current open goals at a file position.

```json
{
  "file": "src/Foo.v",
  "position": { "line": 42, "character": 0 },
  "pp_format": "Str",
  "compact": true,
  "mode": "After"
}
```

### `coq_proof_state`

Get richer proof context (includes proof name, statements, goals).

```json
{
  "file": "src/Foo.v",
  "position": { "line": 42, "character": 0 }
}
```

### `coq_get_state_at_pos`

Get an opaque state identifier for Pétanque operations.

```json
{
  "file": "src/Foo.v",
  "position": { "line": 42, "character": 0 },
  "memo": true,
  "hash": true
}
```

### `coq_run_tactic`

Execute a tactic speculatively against a state (no file edits).

```json
{
  "state_id": 123,
  "tactic": "intros. reflexivity.",
  "memo": true,
  "hash": true
}
```

### `coq_goals_for_state`

Get goals for a state identifier.

```json
{
  "state_id": 124,
  "compact": true
}
```

### `coq_apply_edit`

Apply text edits to a file and re-sync with rocq-lsp.

```json
{
  "file": "src/Foo.v",
  "edits": [
    {
      "range": {
        "start": { "line": 50, "character": 0 },
        "end": { "line": 50, "character": 0 }
      },
      "newText": "  intros.\n"
    }
  ]
}
```

### `coq_insert_tactic`

High-level helper: insert a tactic and optionally return updated goals.

```json
{
  "file": "src/Foo.v",
  "position": { "line": 50, "character": 2 },
  "tactic": "intros.",
  "follow_with_goals": true
}
```

### `coq_check`

Force document checking and return completion status.

```json
{
  "file": "src/Foo.v"
}
```

## Architecture

```
opencode/LLM  <->  MCP  <->  mcp-coq-lsp  <->  rocq-lsp (subprocess)  <->  Coq/Rocq
```

The MCP server:
1. Spawns `rocq-lsp` as a subprocess
2. Manages document synchronization (didOpen, didChange, didSave)
3. Translates MCP tool calls into LSP requests and Pétanque calls
4. Returns structured results to the MCP client

## Development

```bash
# Watch mode (rebuilds on changes)
npm run watch

# Run with tsx (no build needed)
npm run dev

# Build for production
npm run build
```

## Configuration Options

- `--workspace-root <path>`: Root directory of your Coq project (should contain `_CoqProject` or `_RocqProject`)
- `--coq-lsp-path <path>`: Path to `coq-lsp` / `rocq-lsp` binary (default: `coq-lsp` on PATH)
- `--coq-lsp-args "<args>"`: Additional arguments to pass to coq-lsp (space-separated)

## Troubleshooting

### rocq-lsp not found

Make sure `coq-lsp` is installed and on your PATH:

```bash
which coq-lsp
# or
opam install coq-lsp
```

### Document not checking

The server uses `check_only_on_request` mode by default. You may need to explicitly call `coq_check` to force document validation, or query goals at a position to trigger checking up to that point.

### File not found errors

Ensure `--workspace-root` points to the correct directory containing your `.v` files and `_CoqProject` / `_RocqProject`.

## License

MIT

## References

- [MCP Specification](https://modelcontextprotocol.io/)
- [rocq-lsp Project](https://github.com/ejgallego/rocq-lsp)
- [rocq-lsp Protocol Documentation](https://raw.githubusercontent.com/ejgallego/rocq-lsp/main/etc/doc/PROTOCOL.md)
- [Full Specification](../MCP_COQ_LSP_SPEC.md)
