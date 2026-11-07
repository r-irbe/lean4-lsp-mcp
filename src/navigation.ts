// src/navigation.ts
// P1: live LSP navigation surface (`lean_navigate`) - pure, side-effect-free parts.
//
// Everything here is deterministic and spawn-free so the gate and the request
// mapping can be tested with process-boundary doubles. The stateful half
// (session binding, admission currency, dispatch) lives in FileWorkerManager.

/** Closed operation set. Mutations (rename, executeCommand, codeAction apply) are P1b. */
export const NAV_OPERATIONS = [
  "hover",
  "definition",
  "typeDefinition",
  "declaration",
  "implementation",
  "references",
  "documentSymbol",
  "workspaceSymbol",
  "findSymbol",
  "prepareCallHierarchy",
  "incomingCalls",
  "outgoingCalls",
  "codeAction",
  "moduleImports",
  "moduleImportedBy",
  "capabilities",
] as const;
export type NavOperation = (typeof NAV_OPERATIONS)[number];

/** Refusal taxonomy: `environment_unavailable: <code>: <operation>: <detail>`. */
export const NAV_REFUSAL_CODES = [
  "admission-missing",
  "context-changed",
  "live-identity-unavailable",
  "ambiguous-warm-route",
  "artifact-unavailable",
  "bounds-exceeded",
] as const;
export type NavRefusalCode = (typeof NAV_REFUSAL_CODES)[number];

/** A gate refusal. Never an empty successful result, never "not found". */
export class NavRefusal extends Error {
  readonly code: NavRefusalCode;
  readonly operation: string;
  constructor(code: NavRefusalCode, operation: string, detail: string) {
    super(`environment_unavailable: ${code}: ${operation}: ${detail}`);
    this.name = "NavRefusal";
    this.code = code;
    this.operation = operation;
  }
}

export type NavClass = "introspection" | "pathless" | "offline-module" | "lean-targeted";

export function classifyOperation(op: NavOperation): NavClass {
  if (op === "capabilities") return "introspection";
  if (op === "workspaceSymbol" || op === "findSymbol") return "pathless";
  if (op === "moduleImports" || op === "moduleImportedBy") return "offline-module";
  return "lean-targeted";
}

export interface NavArgs {
  operation: NavOperation;
  filePath?: string;
  line?: number;
  col?: number;
  query?: string;
  symbol?: string;
  includeDeclaration?: boolean;
  callHierarchyItem?: { uri: string; name: string; [k: string]: unknown };
}

const POSITION_OPS: ReadonlySet<NavOperation> = new Set([
  "hover", "definition", "typeDefinition", "declaration", "implementation",
  "references", "prepareCallHierarchy", "codeAction",
]);

/** Step 1 of the gate: closed-enum + argument validation. Plain Errors, no side effects. */
export function validateNavArgs(raw: any): NavArgs {
  if (!raw || typeof raw !== "object") throw new Error("lean_navigate: arguments must be an object");
  const op = raw.operation;
  if (typeof op !== "string" || !(NAV_OPERATIONS as readonly string[]).includes(op)) {
    throw new Error(`lean_navigate: 'operation' must be one of ${NAV_OPERATIONS.join(", ")}`);
  }
  const operation = op as NavOperation;
  if (raw.apply !== undefined && raw.apply !== false) {
    throw new Error("lean_navigate: 'apply' is not supported; codeAction is advertise-only (workspace mutation is deferred to P1b)");
  }
  const out: NavArgs = { operation };
  const cls = classifyOperation(operation);
  const filePath = raw.filePath ?? raw.path ?? raw.file;
  if (filePath !== undefined && (typeof filePath !== "string" || filePath.length === 0 || filePath.length > 4096 || /[\0\r\n]/.test(filePath))) {
    throw new Error("lean_navigate: 'filePath' must be a non-empty path string");
  }
  if (typeof filePath === "string") out.filePath = filePath;
  if (cls === "lean-targeted" || cls === "offline-module") {
    if (!filePath && operation !== "incomingCalls" && operation !== "outgoingCalls") {
      throw new Error(`lean_navigate: '${operation}' requires 'filePath'`);
    }
  }
  if (POSITION_OPS.has(operation)) {
    const line = Number(raw.line ?? 1);
    const col = Number(raw.col ?? raw.character ?? 1);
    if (!Number.isInteger(line) || line < 1 || !Number.isInteger(col) || col < 1) {
      throw new Error("lean_navigate: 'line' and 'col' must be positive integers (1-based)");
    }
    out.line = line;
    out.col = col;
  }
  if (cls === "pathless") {
    if (typeof raw.query !== "string" || raw.query.length === 0 || raw.query.length > 256) {
      throw new Error(`lean_navigate: '${operation}' requires a non-empty 'query' (max 256 chars)`);
    }
    out.query = raw.query;
  }
  if (operation === "incomingCalls" || operation === "outgoingCalls") {
    const item = raw.callHierarchyItem;
    if (!item || typeof item !== "object" || typeof item.uri !== "string" || typeof item.name !== "string") {
      throw new Error(`lean_navigate: '${operation}' requires 'callHierarchyItem' from prepareCallHierarchy`);
    }
    out.callHierarchyItem = item;
  }
  if (raw.symbol !== undefined) {
    if (typeof raw.symbol !== "string" || !/^[^\s;`\\]+$/.test(raw.symbol) || raw.symbol.length > 512) {
      throw new Error("lean_navigate: 'symbol' must be a Lean name without whitespace/semicolons");
    }
    out.symbol = raw.symbol;
  }
  if (raw.includeDeclaration !== undefined) out.includeDeclaration = raw.includeDeclaration !== false;
  return out;
}

export interface NavLspRequest {
  method: string;
  params: Record<string, unknown>;
}

/** Operation -> LSP request. `uri` is the synced document URI for document-scoped operations. */
export function buildNavRequest(args: NavArgs, uri?: string): NavLspRequest {
  const position = { line: Math.max(0, (args.line ?? 1) - 1), character: Math.max(0, (args.col ?? 1) - 1) };
  const doc = { textDocument: { uri } };
  switch (args.operation) {
    case "hover": return { method: "textDocument/hover", params: { ...doc, position } };
    case "definition": return { method: "textDocument/definition", params: { ...doc, position } };
    case "typeDefinition": return { method: "textDocument/typeDefinition", params: { ...doc, position } };
    case "declaration": return { method: "textDocument/declaration", params: { ...doc, position } };
    case "implementation": return { method: "textDocument/implementation", params: { ...doc, position } };
    case "references":
      return { method: "textDocument/references", params: { ...doc, position, context: { includeDeclaration: args.includeDeclaration !== false } } };
    case "documentSymbol": return { method: "textDocument/documentSymbol", params: { ...doc } };
    case "workspaceSymbol":
    case "findSymbol":
      return { method: "workspace/symbol", params: { query: args.query } };
    case "prepareCallHierarchy": return { method: "textDocument/prepareCallHierarchy", params: { ...doc, position } };
    case "incomingCalls": return { method: "callHierarchy/incomingCalls", params: { item: args.callHierarchyItem } };
    case "outgoingCalls": return { method: "callHierarchy/outgoingCalls", params: { item: args.callHierarchyItem } };
    case "codeAction":
      return { method: "textDocument/codeAction", params: { ...doc, range: { start: position, end: position }, context: { diagnostics: [] } } };
    default:
      throw new Error(`lean_navigate: '${args.operation}' has no LSP request`);
  }
}

/** codeAction is advertise-only: strip every `edit`/`command` payload so nothing is applicable. */
export function sanitizeAdvertisedActions(result: unknown): unknown {
  if (!Array.isArray(result)) return result;
  return result.map((a: any) => ({ title: a?.title, kind: a?.kind, isPreferred: a?.isPreferred }));
}

/** findSymbol is workspace/symbol narrowed to the exact (or dot-suffixed) name. */
export function narrowFindSymbol(result: unknown, query: string): unknown {
  if (!Array.isArray(result)) return result;
  return result.filter((s: any) => typeof s?.name === "string" && (s.name === query || s.name.endsWith("." + query)));
}

export const NAV_MAX_ITEMS = 500;
export const NAV_MAX_JSON_BYTES = 256 * 1024;

/** Bounded result: arrays are capped with an explicit marker; an oversize payload is refused. */
export function boundNavResult(operation: string, result: unknown): unknown {
  let bounded = result;
  if (Array.isArray(result) && result.length > NAV_MAX_ITEMS) {
    bounded = { truncated: true, total: result.length, items: result.slice(0, NAV_MAX_ITEMS) };
  }
  const size = Buffer.byteLength(JSON.stringify(bounded ?? null), "utf-8");
  if (size > NAV_MAX_JSON_BYTES) {
    throw new NavRefusal("bounds-exceeded", operation, `result is ${size} bytes (limit ${NAV_MAX_JSON_BYTES}); narrow the query`);
  }
  return bounded;
}

export type NavMode = "exact" | "ambient";

/**
 * Mode resolution (P1 §5). Returns the mode, or throws the admission-missing refusal.
 *  - context admitted                  -> exact (no ambient fallback)
 *  - no context, strict switch set     -> refused
 *  - no context, root is a Lake project-> ambient (0.3.0 behaviour preserved)
 *  - otherwise                         -> refused
 */
export function resolveNavMode(input: {
  operation: string;
  admitted: boolean;
  requireExact: boolean;
  isLakeRoot: boolean;
  location: string;
}): NavMode {
  if (input.admitted) return "exact";
  if (input.requireExact) {
    throw new NavRefusal("admission-missing", input.operation, `strict mode requires an admitted Lean context (${input.location})`);
  }
  if (input.isLakeRoot) return "ambient";
  throw new NavRefusal("admission-missing", input.operation, `no admitted Lean context and the root is not a Lake project (${input.location})`);
}

export const NAV_CAPABILITIES = {
  tool: "lean_navigate",
  operations: NAV_OPERATIONS,
  deferred: ["rename", "rename_file", "executeCommand", "codeAction apply"],
  refusalCodes: NAV_REFUSAL_CODES,
  modes: { exact: "context admitted; no ambient fallback", ambient: "Lake project without admission; contextCertified=false" },
} as const;
