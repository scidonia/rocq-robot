/**
 * Common LSP and Coq/Rocq types used throughout the MCP server
 */

// LSP Position (0-based)
export interface Position {
  line: number;
  character: number;
}

// LSP Range
export interface Range {
  start: Position;
  end: Position;
}

// LSP VersionedTextDocumentIdentifier
export interface VersionedTextDocumentIdentifier {
  uri: string;
  version: number;
}

// Coq/Rocq hypothesis in a goal
export interface Hyp<Pp> {
  names: Pp[];
  def?: Pp;
  ty: Pp;
}

// Coq/Rocq goal
export interface Goal<Pp> {
  hyps: Hyp<Pp>[];
  ty: Pp;
}

// Coq/Rocq goal configuration (full proof state)
export interface GoalConfig<Pp> {
  goals: Goal<Pp>[];
  stack: [Goal<Pp>[], Goal<Pp>[]][];
  bullet?: Pp;
  shelf: Goal<Pp>[];
  given_up: Goal<Pp>[];
}

// Coq/Rocq message with optional range and level
export interface Message<Pp> {
  range?: Range;
  level: number;
  text: Pp;
}

// Program information (obligations, etc.)
export interface ProgramInfo {
  // To be detailed as needed
  [key: string]: unknown;
}

// Goal answer from proof/goals request
export interface GoalAnswer<Pp> {
  textDocument: VersionedTextDocumentIdentifier;
  position: Position;
  range?: Range;
  goals?: GoalConfig<Pp>;
  messages: Message<Pp>[];
  error?: Pp;
  program?: ProgramInfo;
}

// Proof information from petanque
export interface ProofInfo {
  name: string;
  statements: string[];
  range?: Range;
}

// Pétanque run options
export interface RunOpts {
  memo?: boolean;
  hash?: boolean;
}

// Pétanque run result
export interface RunResult<T> {
  st: T;
  hash?: number;
  proof_finished: boolean;
  feedback: [number, string][];
}

// Rocq error data (in LSP error responses)
export interface RocqErrorData {
  feedback: Message<string>[];
}

// Configuration for the MCP server
export interface ServerConfig {
  rocqLspPath?: string;
  rocqLspArgs?: string[];
  workspaceRoot?: string;
  checkOnlyOnRequest?: boolean;
  ppType?: number;
  goalAfterTactic?: boolean;
}
