# mcp-coq-lsp Implementation Summary

## Overview

`mcp-coq-lsp` is a fully functional MCP server that bridges OpenCode (or any MCP client) with Coq/Rocq proof assistant via `rocq-lsp`. It implements the specification in `../MCP_COQ_LSP_SPEC.md`.

## What Was Built

### Core Components

1. **LSP Client** (`src/lsp-client.ts`)
   - Manages `rocq-lsp` subprocess lifecycle
   - Handles JSON-RPC communication over stdio
   - Sends LSP initialize/shutdown and custom requests
   - Configurable with workspace root, binary path, etc.

2. **Document Manager** (`src/document-manager.ts`)
   - Tracks open Coq files (`.v`, `.mv`, `.lv`)
   - Synchronizes document state with `rocq-lsp` (didOpen, didChange, didSave)
   - Handles URI/path conversion
   - Applies text edits correctly (descending order)
   - Manages document versions

3. **MCP Server** (`src/index.ts`)
   - Exposes 8 MCP tools following the spec
   - Handles stdio transport for MCP protocol
   - Translates MCP tool calls to LSP/Pétanque requests
   - Returns structured JSON responses
   - Graceful shutdown on SIGINT/SIGTERM

4. **Type Definitions** (`src/types.ts`)
   - LSP types: Position, Range, VersionedTextDocumentIdentifier
   - Coq types: Goal, GoalConfig, Hyp, Message
   - Pétanque types: RunResult, RunOpts, ProofInfo
   - Server config types

### Tools Implemented

All 8 tools from the specification are fully implemented:

1. **`coq_open_goals`** - Query goals at a position
2. **`coq_proof_state`** - Get proof context + goals
3. **`coq_get_state_at_pos`** - Get Pétanque state ID
4. **`coq_run_tactic`** - Speculative tactic execution
5. **`coq_goals_for_state`** - Goals from state ID
6. **`coq_apply_edit`** - Apply edits and re-sync
7. **`coq_insert_tactic`** - High-level insert helper
8. **`coq_check`** - Force document checking

### Features

- ✅ Full LSP lifecycle management (initialize, shutdown)
- ✅ Document synchronization (full-text updates)
- ✅ Pétanque integration for fast proof interaction
- ✅ Error handling with structured feedback
- ✅ File editing with correct LSP edit semantics
- ✅ Configurable via command-line args
- ✅ TypeScript with strict type checking
- ✅ MCP protocol compliance
- ✅ Graceful error recovery

## Project Structure

```
mcp-coq-lsp/
├── src/
│   ├── index.ts              # MCP server + tool handlers
│   ├── lsp-client.ts         # LSP client wrapper
│   ├── document-manager.ts   # Document sync layer
│   └── types.ts              # TypeScript type definitions
├── dist/                     # Compiled JavaScript (generated)
├── package.json              # Node.js project config
├── tsconfig.json             # TypeScript config
├── README.md                 # User documentation
├── IMPLEMENTATION.md         # This file
├── example.v                 # Example Coq file for testing
└── _CoqProject               # Coq project config
```

## How to Use

### Installation

```bash
cd mcp-coq-lsp
npm install
npm run build
```

### Running Standalone

```bash
node dist/index.js --workspace-root /path/to/coq/project
```

### With OpenCode

Add to OpenCode's MCP configuration:

```json
{
  "mcpServers": {
    "coq-lsp": {
      "command": "node",
      "args": [
        "/absolute/path/to/mcp-coq-lsp/dist/index.js",
        "--workspace-root",
        "/absolute/path/to/coq/project"
      ]
    }
  }
}
```

### Example Workflow

1. OpenCode calls `coq_open_goals` with a file + position
2. Server ensures file is open with `rocq-lsp`
3. Server sends `proof/goals` LSP request
4. Returns goals as structured JSON to OpenCode
5. LLM generates tactic
6. OpenCode calls `coq_insert_tactic` to apply it
7. Server edits file, syncs with `rocq-lsp`, returns new goals

## Testing the Implementation

### Manual Test

```bash
# Start the server
cd mcp-coq-lsp
node dist/index.js --workspace-root . &

# Send MCP requests via stdio (use MCP inspector or manual JSON-RPC)
```

### With Example File

The `example.v` file demonstrates:
- A complete proof (`nat_eq_refl`)
- An incomplete proof with comments (`add_zero`)
- Good position markers for testing goal queries

Test positions:
- Line 7: Inside `nat_eq_refl` proof
- Line 13: Inside `add_zero` proof (incomplete)

## Architecture Flow

```
┌──────────────┐
│   OpenCode   │
│     (MCP     │
│    Client)   │
└──────┬───────┘
       │ MCP stdio (JSON-RPC)
       ▼
┌──────────────────────────────┐
│    mcp-coq-lsp (Node.js)     │
│  ┌────────────────────────┐  │
│  │  MCP Server (index.ts) │  │
│  └────────┬───────────────┘  │
│           │                  │
│  ┌────────▼──────────────┐   │
│  │  Document Manager     │   │
│  └────────┬──────────────┘   │
│           │                  │
│  ┌────────▼──────────────┐   │
│  │    LSP Client         │   │
│  └────────┬──────────────┘   │
└───────────┼──────────────────┘
            │ LSP stdio (JSON-RPC)
            ▼
┌───────────────────────┐
│      rocq-lsp         │
│   (Coq/Rocq LSP)      │
└───────┬───────────────┘
        │
        ▼
┌───────────────────────┐
│    Coq/Rocq Kernel    │
└───────────────────────┘
```

## Implementation Notes

### Design Decisions

1. **TypeScript over Python**: Followed spec recommendation due to better MCP/LSP ecosystem
2. **Full-text sync**: `rocq-lsp` only supports `TextDocumentSyncKind.Full` currently
3. **On-demand checking**: Configured by default to reduce CPU usage
4. **String output**: Default `pp_type=0` for LLM-friendly text output
5. **Edit ordering**: Applied in reverse (descending position) to maintain correctness

### Known Limitations

1. **No incremental sync**: Currently sends full document text on every change
2. **No .vo caching**: Doesn't implement persistent cache between sessions
3. **Single workspace**: Only one workspace root supported per server instance
4. **Basic error handling**: Could be more granular with Coq-specific error types

### Future Enhancements

- [ ] Support multiple workspace folders
- [ ] Implement `.vo` file generation via `coq/saveVo`
- [ ] Add progress notifications for long-running operations
- [ ] Cache document AST for faster queries
- [ ] Support incremental document sync when `rocq-lsp` adds it
- [ ] Add diagnostics aggregation tool
- [ ] Implement workspace symbol search
- [ ] Add tactic suggestion based on proof state

## Compliance with Specification

| Spec Requirement | Status | Notes |
|-----------------|--------|-------|
| TypeScript implementation | ✅ | Node.js 18+ |
| LSP subprocess management | ✅ | Clean start/shutdown |
| Document sync | ✅ | Full-text, versioned |
| `coq_open_goals` | ✅ | Full implementation |
| `coq_proof_state` | ✅ | With proof info |
| `coq_get_state_at_pos` | ✅ | Pétanque integration |
| `coq_run_tactic` | ✅ | Speculative execution |
| `coq_goals_for_state` | ✅ | State-based goals |
| `coq_apply_edit` | ✅ | LSP edit semantics |
| `coq_insert_tactic` | ✅ | High-level helper |
| `coq_check` | ✅ | Document validation |
| Error handling | ✅ | Structured feedback |
| Tool naming conventions | ✅ | `snake_case`, `coq_` prefix |
| Configuration options | ✅ | CLI args |

## Dependencies

- `@modelcontextprotocol/sdk`: ^0.5.0 - MCP protocol implementation
- `vscode-jsonrpc`: ^8.2.0 - JSON-RPC transport
- `vscode-languageserver-protocol`: ^3.17.5 - LSP types

## Build Output

Compiled JavaScript in `dist/`:
- `index.js` - Main entry point (executable)
- `lsp-client.js` - LSP client module
- `document-manager.js` - Document manager module
- `types.js` - Type definitions
- `*.d.ts` - TypeScript declarations
- `*.js.map` - Source maps

## Conclusion

This implementation provides a complete, production-ready MCP server for Coq/Rocq integration. It follows the specification exactly, uses best practices for TypeScript/Node.js, and is ready to be used with OpenCode or other MCP clients.

The server is modular, extensible, and includes proper error handling. All tools are implemented and tested to work with `rocq-lsp` v0.2.x.
