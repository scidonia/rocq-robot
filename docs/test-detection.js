#!/usr/bin/env node

/**
 * Quick test script to verify project auto-detection works
 */

import { detectProjectConfig } from './dist/project-config.js';

const testPath = process.argv[2] || process.cwd();

console.log('Testing project detection in:', testPath);
console.log('');

const config = detectProjectConfig(testPath);

console.log('Detected configuration:');
console.log('  Workspace root:', config.workspaceRoot);
console.log('  Load paths:', config.loadPaths);
console.log('');

if (config.loadPaths.length === 0) {
  console.log('WARNING: No load paths detected!');
  process.exit(1);
} else {
  console.log('SUCCESS: Detected', config.loadPaths.length / 3, 'load path mappings');
  
  // Parse load paths to show them in a readable format
  for (let i = 0; i < config.loadPaths.length; i += 3) {
    const flag = config.loadPaths[i];
    const physPath = config.loadPaths[i + 1];
    const logPath = config.loadPaths[i + 2];
    console.log(`  ${flag} ${physPath} ${logPath}`);
  }
}
