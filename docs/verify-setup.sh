#!/bin/bash

# Verification script for mcp-coq-lsp setup

set -e

echo "🔍 Verifying mcp-coq-lsp setup..."
echo ""

# Check Node.js
echo "1. Checking Node.js..."
if command -v node &> /dev/null; then
    NODE_VERSION=$(node --version)
    echo "   ✅ Node.js found: $NODE_VERSION"
    
    # Check if version >= 18
    NODE_MAJOR=$(echo $NODE_VERSION | cut -d'v' -f2 | cut -d'.' -f1)
    if [ "$NODE_MAJOR" -ge 18 ]; then
        echo "   ✅ Version is >= 18"
    else
        echo "   ❌ Node.js version should be >= 18, found: $NODE_VERSION"
        exit 1
    fi
else
    echo "   ❌ Node.js not found. Please install Node.js >= 18"
    exit 1
fi
echo ""

# Check npm
echo "2. Checking npm..."
if command -v npm &> /dev/null; then
    NPM_VERSION=$(npm --version)
    echo "   ✅ npm found: v$NPM_VERSION"
else
    echo "   ❌ npm not found"
    exit 1
fi
echo ""

# Check coq-lsp
echo "3. Checking coq-lsp..."
if command -v coq-lsp &> /dev/null; then
    COQ_LSP_PATH=$(which coq-lsp)
    echo "   ✅ coq-lsp found: $COQ_LSP_PATH"
else
    echo "   ❌ coq-lsp not found. Please install via: opam install coq-lsp"
    exit 1
fi
echo ""

# Check if node_modules exists
echo "4. Checking dependencies..."
if [ -d "node_modules" ]; then
    echo "   ✅ node_modules/ exists"
else
    echo "   ⚠️  node_modules/ not found. Run: npm install"
    exit 1
fi
echo ""

# Check if dist exists
echo "5. Checking build output..."
if [ -d "dist" ] && [ -f "dist/index.js" ]; then
    echo "   ✅ dist/ exists with index.js"
else
    echo "   ⚠️  dist/ not found or incomplete. Run: npm run build"
    exit 1
fi
echo ""

# Check if example.v exists
echo "6. Checking example file..."
if [ -f "example.v" ]; then
    echo "   ✅ example.v exists"
else
    echo "   ⚠️  example.v not found"
fi
echo ""

# Check if _CoqProject exists
echo "7. Checking Coq project config..."
if [ -f "_CoqProject" ]; then
    echo "   ✅ _CoqProject exists"
else
    echo "   ⚠️  _CoqProject not found"
fi
echo ""

# Try to get absolute path
echo "8. Server path information..."
SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
echo "   📂 Server directory: $SCRIPT_DIR"
echo "   📂 Executable: $SCRIPT_DIR/dist/index.js"
echo ""

echo "✅ All checks passed!"
echo ""
echo "🚀 Quick start:"
echo ""
echo "   # Test standalone:"
echo "   node dist/index.js --workspace-root ."
echo ""
echo "   # Configure OpenCode:"
echo "   Add to MCP config:"
echo '   {
     "mcpServers": {
       "coq-lsp": {
         "command": "node",
         "args": [
           "'$SCRIPT_DIR'/dist/index.js",
           "--workspace-root",
           "/path/to/your/coq/project"
         ]
       }
     }
   }'
echo ""
echo "📖 See QUICKSTART.md for detailed instructions"
