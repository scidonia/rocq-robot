/**
 * Document manager: tracks open documents and syncs with rocq-lsp
 */

import { promises as fs } from 'fs';
import { resolve } from 'path';
import { pathToFileURL } from 'url';
import type { RocqLspClient } from './lsp-client.js';

interface DocumentState {
  uri: string;
  languageId: string;
  version: number;
  text: string;
}

export function applyTextEdits(
  text: string,
  edits: Array<{ range: { start: { line: number; character: number }; end: { line: number; character: number } }; newText: string }>
): string {
  const lines = text.split('\n');

  // Sort edits in reverse order (last edit first)
  const sortedEdits = [...edits].sort((a, b) => {
    if (a.range.start.line !== b.range.start.line) {
      return b.range.start.line - a.range.start.line;
    }
    return b.range.start.character - a.range.start.character;
  });

  for (const edit of sortedEdits) {
    const { start, end } = edit.range;

    // Extract parts
    const beforeStart = lines.slice(0, start.line);
    const startLine = lines[start.line] || '';
    const endLine = lines[end.line] || '';

    const prefix = startLine.substring(0, start.character);
    const suffix = endLine.substring(end.character);

    const afterEnd = lines.slice(end.line + 1);

    // Build new content
    const newLines = edit.newText.split('\n');
    let resultLines: string[];
    if (newLines.length === 1) {
      resultLines = [...beforeStart, prefix + newLines[0] + suffix, ...afterEnd];
    } else {
      const firstNew = prefix + newLines[0];
      const lastNew = newLines[newLines.length - 1] + suffix;
      const middleNew = newLines.slice(1, -1);
      resultLines = [...beforeStart, firstNew, ...middleNew, lastNew, ...afterEnd];
    }

    // Update lines for next iteration
    lines.length = 0;
    lines.push(...resultLines);
  }

  return lines.join('\n');
}

export class DocumentManager {
  private documents = new Map<string, DocumentState>();
  private workspaceRoot: string;

  constructor(
    private lspClient: RocqLspClient,
    workspaceRoot: string
  ) {
    this.workspaceRoot = workspaceRoot;
  }

  /**
   * Convert filesystem path to file:// URI
   */
  pathToUri(path: string): string {
    const absPath = resolve(this.workspaceRoot, path);
    return pathToFileURL(absPath).toString();
  }

  /**
   * Determine languageId from file extension
   */
  private getLanguageId(path: string): string {
    if (path.endsWith('.v')) return 'coq';
    if (path.endsWith('.mv')) return 'markdown';
    if (path.endsWith('.lv') || path.endsWith('.v.tex')) return 'latex';
    return 'coq'; // default
  }

  /**
   * Open a document (load from disk and notify rocq-lsp)
   */
  async openDocument(path: string): Promise<DocumentState> {
    const uri = this.pathToUri(path);

    // Check if already open
    if (this.documents.has(uri)) {
      return this.documents.get(uri)!;
    }

    // Load file content
    const absPath = resolve(this.workspaceRoot, path);
    const text = await fs.readFile(absPath, 'utf-8');
    const languageId = this.getLanguageId(path);

    const doc: DocumentState = {
      uri,
      languageId,
      version: 1,
      text,
    };

    // Wait for LSP client to be ready (e.g., during workspace switch restart)
    await this.lspClient.waitUntilReady(20000);

    // Notify rocq-lsp — only cache after successful open
    await this.lspClient.sendNotification('textDocument/didOpen', {
      textDocument: {
        uri,
        languageId,
        version: doc.version,
        text,
      },
    });

    this.documents.set(uri, doc);

    return doc;
  }

  /**
   * Update document content (full sync)
   */
  async updateDocument(path: string, newText: string): Promise<DocumentState> {
    const uri = this.pathToUri(path);
    let doc = this.documents.get(uri);

    if (!doc) {
      // Open it first
      doc = await this.openDocument(path);
    }

    doc.version += 1;
    doc.text = newText;

    // Notify rocq-lsp (full sync)
    await this.lspClient.sendNotification('textDocument/didChange', {
      textDocument: {
        uri,
        version: doc.version,
      },
      contentChanges: [
        {
          text: newText,
        },
      ],
    });

    return doc;
  }

  /**
   * Save document to disk
   */
  async saveDocument(path: string): Promise<void> {
    const uri = this.pathToUri(path);
    const doc = this.documents.get(uri);

    if (!doc) {
      throw new Error(`Document not open: ${path}`);
    }

    const absPath = resolve(this.workspaceRoot, path);
    await fs.writeFile(absPath, doc.text, 'utf-8');

    // Notify rocq-lsp
    await this.lspClient.sendNotification('textDocument/didSave', {
      textDocument: { uri, version: doc.version },
      text: doc.text,
    });
  }

  /**
   * Close a document
   */
  async closeDocument(path: string): Promise<void> {
    const uri = this.pathToUri(path);
    const doc = this.documents.get(uri);

    if (!doc) {
      return; // Already closed
    }

    await this.lspClient.sendNotification('textDocument/didClose', {
      textDocument: { uri },
    });

    this.documents.delete(uri);
  }

  /**
   * Clear all cached documents (use after LSP restart)
   */
  clear(): void {
    this.documents.clear();
  }

  /**
   * Get current document state
   */
  getDocument(path: string): DocumentState | undefined {
    const uri = this.pathToUri(path);
    return this.documents.get(uri);
  }

  /**
   * Apply text edits to a document
   * Edits should be in descending order by position
   */
  applyEdits(
    text: string,
    edits: Array<{ range: { start: { line: number; character: number }; end: { line: number; character: number } }; newText: string }>
  ): string {
    return applyTextEdits(text, edits);
  }
}
