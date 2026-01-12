# Project Configuration Auto-Detection

## Overview

The MCP-Coq-LSP server now automatically detects Coq/Rocq project configurations to help diagnose issues with workspace setup and load paths.

## What It Does

When the MCP server starts, it now:

1. **Auto-detects project configuration** from the workspace root:
   - Checks for `_RocqProject` (Rocq 9.x convention)
   - Checks for `_CoqProject` (classic Coq convention)
   - Falls back to parsing `dune` files for `(coq.theory (name X))` declarations

2. **Logs detected configuration** to stderr for debugging:
   - Workspace root directory
   - Detected load path mappings (e.g., `-Q theories Cyclic`)
   - Warnings if no project configuration is found

3. **Validates project setup** before coq-lsp starts:
   - If no `_CoqProject`/`_RocqProject`/dune config is found, logs a warning
   - Helps diagnose "Cannot find physical path bound to logical path" errors

## Important Notes

### coq-lsp Auto-Detection

`coq-lsp` automatically reads `_CoqProject` and `_RocqProject` files from the workspace root. The load path arguments (`-Q`, `-R`) do **not** need to be (and cannot be) passed as command-line arguments to `coq-lsp`.

Our auto-detection serves these purposes:
- **Diagnostic logging**: Helps you see what project configuration coq-lsp will find
- **Early validation**: Warns if no project configuration exists
- **Debugging aid**: Makes it clear what workspace root and load paths are being used

### Workspace Root

The `--workspace-root` argument is **critical** for the MCP server to work correctly:

```json
{
  "mcpServers": {
    "coq-lsp": {
      "command": "node",
      "args": [
        "/path/to/mcp-coq-lsp/dist/index.js",
        "--workspace-root",
        "{workspaceRoot}"
      ]
    }
  }
}
```

Without `--workspace-root`, the MCP server will use `process.cwd()` which may not match your Coq project root, causing coq-lsp to fail to find `_CoqProject` and load path mappings.

## Example Output

When starting the MCP server with a properly configured project:

```
[project-config] Detecting project config in: /home/user/my-coq-project
[project-config] Found _CoqProject
[project-config] Extracted from _CoqProject: [ '-Q', 'theories', 'MyProject' ]
[mcp-coq-lsp] Workspace root: /home/user/my-coq-project
[mcp-coq-lsp] Detected load paths: [ '-Q', 'theories', 'MyProject' ]
[mcp-coq-lsp] coq-lsp args: []
[lsp-client] Starting LSP process:
[lsp-client]   Command: coq-lsp
[lsp-client]   Args: []
[lsp-client]   CWD: /home/user/my-coq-project
[LSP initialized]: { name: 'coq-lsp', version: '0.2.5' }
```

## Troubleshooting

### "Cannot find physical path bound to logical path X"

This error means coq-lsp couldn't find the load path mapping for logical prefix `X`.

**Check these things:**

1. **Workspace root is correct**: Make sure `--workspace-root` points to your project root (where `_CoqProject` lives)
2. **_CoqProject exists**: You should have a `_CoqProject` or `_RocqProject` file in your workspace root
3. **Load path is defined**: The `_CoqProject` should have a line like `-Q theories MyProject`
4. **Check the logs**: The MCP server logs show exactly what it detected. If you see "WARNING: No _CoqProject/_RocqProject/dune config found!", that's your problem.

### Example Fix

If you see:
```
[mcp-coq-lsp] WARNING: No _CoqProject/_RocqProject/dune config found!
[mcp-coq-lsp] coq-lsp may not be able to resolve imports correctly.
```

Create a `_CoqProject` file in your workspace root:
```
-Q theories MyProjectName

theories/Foo.v
theories/Bar.v
```

## Files Modified

- `src/project-config.ts` (new): Auto-detection logic
  - `detectProjectConfig()`: Main detection function
  - `parseCoqProjectFile()`: Parse `_CoqProject`/`_RocqProject`
  - `inferLoadPathsFromDune()`: Parse `dune` files
  - `parseDuneFile()`: Extract `(coq.theory (name X))` declarations

- `src/index.ts`: Integration with main server
  - Calls `detectProjectConfig()` on startup
  - Logs detected configuration for debugging
  - Warns if no project config found

- `src/lsp-client.ts`: Enhanced logging
  - Logs the exact command, args, and CWD when spawning coq-lsp
  - Makes it clear what coq-lsp will see

## Testing

Test the auto-detection on your project:

```bash
cd /path/to/mcp-coq-lsp
node test-detection.js /path/to/your/coq/project
```

This will show what configuration would be detected without actually starting coq-lsp.
