/**
 * Auto-detect Coq/Rocq project configuration from _CoqProject, _RocqProject, or dune files
 */

import { readFileSync, existsSync, readdirSync, statSync } from 'fs';
import { join, resolve } from 'path';

export interface ProjectConfig {
  loadPaths: string[];  // Array of -Q and -R arguments (e.g., ['-Q', 'theories', 'Cyclic'])
  workspaceRoot: string;
}

/**
 * Parse _CoqProject or _RocqProject file for -Q and -R flags
 */
function parseCoqProjectFile(filePath: string): string[] {
  if (!existsSync(filePath)) {
    return [];
  }

  const content = readFileSync(filePath, 'utf-8');
  const lines = content.split('\n');
  const args: string[] = [];

  for (const line of lines) {
    const trimmed = line.trim();
    
    // Skip comments and empty lines
    if (!trimmed || trimmed.startsWith('#')) {
      continue;
    }

    // Parse -Q and -R flags
    const tokens = trimmed.split(/\s+/);
    for (let i = 0; i < tokens.length; i++) {
      const token = tokens[i];
      
      if (token === '-Q' || token === '-R') {
        // -Q and -R take two arguments: physical_path logical_path
        if (i + 2 < tokens.length) {
          args.push(token, tokens[i + 1], tokens[i + 2]);
          i += 2;
        }
      }
    }
  }

  return args;
}

/**
 * Find all dune files recursively in a directory
 */
function findDuneFiles(dir: string, maxDepth: number = 3): string[] {
  const duneFiles: string[] = [];

  function recurse(currentDir: string, depth: number) {
    if (depth > maxDepth) {
      return;
    }

    try {
      const entries = readdirSync(currentDir);
      
      for (const entry of entries) {
        const fullPath = join(currentDir, entry);
        
        // Skip hidden directories and common build directories
        if (entry.startsWith('.') || entry === '_build' || entry === 'node_modules') {
          continue;
        }

        try {
          const stat = statSync(fullPath);
          
          if (stat.isDirectory()) {
            recurse(fullPath, depth + 1);
          } else if (entry === 'dune') {
            duneFiles.push(fullPath);
          }
        } catch {
          // Skip files/dirs we can't stat
          continue;
        }
      }
    } catch {
      // Skip directories we can't read
      return;
    }
  }

  recurse(dir, 0);
  return duneFiles;
}

/**
 * Parse a dune file to extract library/theory names and their directories
 */
function parseDuneFile(filePath: string): Array<{ name: string; dir: string }> {
  if (!existsSync(filePath)) {
    return [];
  }

  const content = readFileSync(filePath, 'utf-8');
  const results: Array<{ name: string; dir: string }> = [];
  const dir = resolve(filePath, '..');

  // Match (coq.theory (name X)) or (library (name X))
  // This is a simple regex-based parser; proper s-expression parsing would be better
  // but this covers the common cases
  
  // Match (coq.theory ... (name LogicalName) ...)
  const theoryRegex = /\(coq\.theory\s+[^)]*\(name\s+(\w+)\)/gs;
  let match;
  
  while ((match = theoryRegex.exec(content)) !== null) {
    results.push({ name: match[1], dir });
  }

  // Also check for (library (name X)) which is used in some dune files
  const libraryRegex = /\(library\s+[^)]*\(name\s+(\w+)\)/gs;
  
  while ((match = libraryRegex.exec(content)) !== null) {
    results.push({ name: match[1], dir });
  }

  return results;
}

/**
 * Infer -Q flags from dune project structure
 * Common pattern: theories/dune declares (name Cyclic) → -Q theories Cyclic
 */
function inferLoadPathsFromDune(workspaceRoot: string): string[] {
  const duneFiles = findDuneFiles(workspaceRoot);
  const args: string[] = [];

  for (const duneFile of duneFiles) {
    const theories = parseDuneFile(duneFile);
    
    for (const theory of theories) {
      // Calculate relative path from workspace root to the directory containing dune
      const relPath = theory.dir.replace(workspaceRoot, '').replace(/^\//, '') || '.';
      
      // Add -Q flag: -Q <physical_path> <logical_name>
      args.push('-Q', relPath, theory.name);
    }
  }

  return args;
}

/**
 * Auto-detect project configuration from workspace root
 * Checks in order:
 * 1. _RocqProject (Rocq-specific)
 * 2. _CoqProject (classic Coq)
 * 3. dune files (modern build system)
 */
export function detectProjectConfig(workspaceRoot: string): ProjectConfig {
  const resolvedRoot = resolve(workspaceRoot);
  const loadPaths: string[] = [];

  console.error('[project-config] Detecting project config in:', resolvedRoot);

  // Try _RocqProject first (Rocq 9.x convention)
  const rocqProjectPath = join(resolvedRoot, '_RocqProject');
  if (existsSync(rocqProjectPath)) {
    console.error('[project-config] Found _RocqProject');
    const args = parseCoqProjectFile(rocqProjectPath);
    loadPaths.push(...args);
    console.error('[project-config] Extracted from _RocqProject:', args);
  }

  // Try _CoqProject (classic convention, still widely used)
  const coqProjectPath = join(resolvedRoot, '_CoqProject');
  if (existsSync(coqProjectPath)) {
    console.error('[project-config] Found _CoqProject');
    const args = parseCoqProjectFile(coqProjectPath);
    loadPaths.push(...args);
    console.error('[project-config] Extracted from _CoqProject:', args);
  }

  // Try dune-based detection if no project file found, or as a fallback
  if (loadPaths.length === 0) {
    console.error('[project-config] No _CoqProject/_RocqProject found, trying dune detection');
    const duneArgs = inferLoadPathsFromDune(resolvedRoot);
    loadPaths.push(...duneArgs);
    console.error('[project-config] Inferred from dune:', duneArgs);
  }

  return {
    loadPaths,
    workspaceRoot: resolvedRoot,
  };
}

/**
 * Merge user-provided coq-lsp args with auto-detected project config
 * User args take precedence to allow overrides
 */
export function mergeProjectArgs(
  userArgs: string[] | undefined,
  detectedConfig: ProjectConfig
): string[] {
  const merged = [...detectedConfig.loadPaths];

  // Append user args at the end so they can override detected settings
  if (userArgs && userArgs.length > 0) {
    merged.push(...userArgs);
  }

  return merged;
}
