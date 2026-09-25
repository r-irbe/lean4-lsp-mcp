// tools/lean_lsp_mcp/src/index.ts
// Standalone Model Context Protocol (MCP) server for Lean 4 & C FFI.
// Strict 7-bit ASCII only (INV-001).

import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";
import { execSync, spawn, ChildProcess } from "node:child_process";
import { fileURLToPath, pathToFileURL } from "node:url";

export interface IleanSymbolEntry {
  filePath: string;
  line: number;
  col: number;
  endLine?: number;
  endCol?: number;
  module?: string;
  name?: string;
  kind?: string;
}

export interface IleanFile {
  version?: number;
  module?: string;
  directImports?: Array<[string, boolean, boolean, boolean]> | string[];
  decls?: Record<string, number[]>;
  entries?: Record<string, { line: number; col: number; endLine?: number; endCol?: number }>;
}

export interface McpToolDefinition {
  name: string;
  description: string;
  inputSchema: {
    type: "object";
    properties: Record<string, any>;
    required?: string[];
  };
}

export interface McpRequest {
  jsonrpc: "2.0";
  id?: number | string | null;
  method: string;
  params?: any;
}

export interface McpResponse {
  jsonrpc: "2.0";
  id: number | string | null;
  result?: any;
  error?: {
    code: number;
    message: string;
    data?: any;
  };
}

export interface GoalFilterOptions {
  hideTypeclasses?: boolean;
  hideInaccessible?: boolean;
  onlyTarget?: boolean;
  maxGoals?: number;
}

export interface TransitiveClosureResult {
  items: string[];
  depth: number;
  hasCycle: boolean;
  cyclePath?: string[];
}

export const TOOL_DEFINITIONS: McpToolDefinition[] = [
  {
    name: "lean_goal",
    description: "Queries interactive Lean 4 tactic proof state at cursor position ($/lean/plainGoal)",
    inputSchema: {
      type: "object",
      properties: {
        filePath: { type: "string", description: "Absolute or relative path to the .lean file" },
        line: { type: "integer", description: "1-based line number" },
        col: { type: "integer", description: "1-based column number" },
        character: { type: "integer", description: "Synonym for col" },
        filterTypeclasses: { type: "boolean", description: "Filter out ambient typeclass instances (default: false)" },
        filterInaccessible: { type: "boolean", description: "Filter out compiler internal and dagger variables (default: false)" },
        onlyTarget: { type: "boolean", description: "Return only the target goal expression (default: false)" },
      },
      required: ["filePath", "line"],
    },
  },
  {
    name: "lean_filtered_goal",
    description: "Queries Lean 4 tactic proof state with aggressive token filtering (strips typeclass instances and irrelevance fields, cutting tokens by 70-90%)",
    inputSchema: {
      type: "object",
      properties: {
        filePath: { type: "string", description: "Absolute or relative path to the .lean file" },
        line: { type: "integer", description: "1-based line number" },
        col: { type: "integer", description: "1-based column number" },
        character: { type: "integer", description: "Synonym for col" },
        hideTypeclasses: { type: "boolean", description: "Omit ambient typeclass instances (default: true)" },
        hideInaccessible: { type: "boolean", description: "Omit inaccessible/dagger variables (default: true)" },
        onlyTarget: { type: "boolean", description: "Return only the target expression (default: false)" },
        maxGoals: { type: "integer", description: "Maximum number of subgoals to display (default: 3)" },
      },
      required: ["filePath", "line"],
    },
  },
  {
    name: "lean_term_goal",
    description: "Queries expected term type under cursor ($/lean/plainTermGoal)",
    inputSchema: {
      type: "object",
      properties: {
        filePath: { type: "string", description: "Absolute or relative path to the .lean file" },
        line: { type: "integer", description: "1-based line number" },
        col: { type: "integer", description: "1-based column number" },
        character: { type: "integer", description: "Synonym for col" },
      },
      required: ["filePath", "line"],
    },
  },
  {
    name: "lean_lookup_symbol",
    description: "Offline zero-latency symbol lookup and jump-to-definition via pre-compiled .ilean cache",
    inputSchema: {
      type: "object",
      properties: {
        symbol: { type: "string", description: "Lean declaration name (e.g. RealQ.bellmanOp or BoundedRewardKernel)" },
        preferOfflineIlean: { type: "boolean", description: "Use fast .ilean cache (default true)" },
      },
      required: ["symbol"],
    },
  },
  {
    name: "lean_module_hierarchy",
    description: "Forward and reverse module dependency hierarchy analysis with transitive closure and cycle detection",
    inputSchema: {
      type: "object",
      properties: {
        moduleName: { type: "string", description: "Full module name (e.g. Mathlib.Data.List)" },
        direction: { type: "string", enum: ["imports", "importedBy", "both"], description: "Direction of dependency traversal (default: both)" },
        transitive: { type: "boolean", description: "Perform full transitive closure traversal (default: false)" },
        maxDepth: { type: "integer", description: "Maximum traversal depth for transitive search (default: 20)" },
      },
      required: ["moduleName"],
    },
  },
  {
    name: "lean_c_ffi_inspect",
    description: "Cross-language C FFI inspector: Lean @[extern] declarations, C implementations, and Lean sysroot include flags",
    inputSchema: {
      type: "object",
      properties: {
        externName: { type: "string", description: "Optional Lean @[extern] identifier or C function name" },
        action: { type: "string", enum: ["sysroot", "inspect", "jump_to_c"], description: "FFI inspection action (default: inspect)" },
      },
    },
  },
  {
    name: "lean_run_code",
    description: "Ephemeral standalone execution via lean --stdin without file pollution",
    inputSchema: {
      type: "object",
      properties: {
        code: { type: "string", description: "Lean code to execute" },
      },
      required: ["code"],
    },
  },
  {
    name: "lean_loogle_search",
    description: "Type-based search querying Loogle API (https://loogle.lean-lang.org/json?q=...)",
    inputSchema: {
      type: "object",
      properties: {
        query: { type: "string", description: "Loogle query string" },
      },
      required: ["query"],
    },
  },
  {
    name: "lean_local_search",
    description: "Fast local declaration search using ripgrep. Use BEFORE trying a lemma name.",
    inputSchema: {
      type: "object",
      properties: {
        query: { type: "string", description: "Declaration name or prefix" },
        limit: { type: "integer", description: "Max matches (default 10)" },
      },
      required: ["query"],
    },
  },
  {
    name: "lean_search",
    description: "Search Mathlib via leansearch.net using natural language.",
    inputSchema: {
      type: "object",
      properties: {
        query: { type: "string", description: "Natural language or Lean term query" },
        num_results: { type: "integer", description: "Max results (default 5)" },
      },
      required: ["query"],
    },
  },
];

export class BitsetDAGIndex {
  private idToName: string[] = [];
  private nameToId: Map<string, number> = new Map();
  private numNodes: number = 0;

  // CSR (Compressed Sparse Row) for forward imports: module -> imports
  private off: Uint32Array = new Uint32Array(0);
  private dst: Uint32Array = new Uint32Array(0);

  // CSC (Compressed Sparse Column) for reverse importedBy: module -> importedBy
  private boff: Uint32Array = new Uint32Array(0);
  private bdst: Uint32Array = new Uint32Array(0);

  // Bitset dimensions
  private wordsPerNode: number = 0;

  // Optional precomputed transitive closure matrix (Uint32Array of size numNodes * wordsPerNode)
  private forwardClosureMatrix: Uint32Array | null = null;
  private reverseClosureMatrix: Uint32Array | null = null;
  private isAcyclic: boolean = true;

  constructor() {}

  /**
   * Build CSR and CSC structures from raw string adjacency map in O(V + E) time.
   */
  public build(adjacency: Map<string, string[]>): void {
    this.nameToId.clear();
    this.idToName = [];

    // 1. Assign dense integer IDs to all unique modules
    for (const [mod, imps] of adjacency.entries()) {
      if (!this.nameToId.has(mod)) {
        const id = this.idToName.length;
        this.nameToId.set(mod, id);
        this.idToName.push(mod);
      }
      for (const imp of imps) {
        if (!this.nameToId.has(imp)) {
          const id = this.idToName.length;
          this.nameToId.set(imp, id);
          this.idToName.push(imp);
        }
      }
    }

    const N = this.idToName.length;
    this.numNodes = N;
    this.wordsPerNode = Math.ceil(N / 32) || 1;

    // 2. Count forward edges per node to construct CSR offset array
    const forwardCounts = new Uint32Array(N);
    let totalEdges = 0;

    for (let u = 0; u < N; u++) {
      const name = this.idToName[u];
      const imps = adjacency.get(name);
      if (imps) {
        forwardCounts[u] = imps.length;
        totalEdges += imps.length;
      }
    }

    this.off = new Uint32Array(N + 1);
    this.dst = new Uint32Array(totalEdges);

    for (let i = 0; i < N; i++) {
      this.off[i + 1] = this.off[i] + forwardCounts[i];
    }

    const fillOffsets = new Uint32Array(this.off);
    for (let u = 0; u < N; u++) {
      const name = this.idToName[u];
      const imps = adjacency.get(name);
      if (imps) {
        for (let j = 0; j < imps.length; j++) {
          const v = this.nameToId.get(imps[j])!;
          this.dst[fillOffsets[u]++] = v;
        }
      }
    }

    // 3. Build reverse CSC (importedBy) via two-pass counting sort in O(V + E)
    const reverseCounts = new Uint32Array(N + 1);
    for (let k = 0; k < this.dst.length; k++) {
      reverseCounts[this.dst[k] + 1]++;
    }
    for (let i = 0; i < N; i++) {
      reverseCounts[i + 1] += reverseCounts[i];
    }

    this.boff = new Uint32Array(reverseCounts);
    this.bdst = new Uint32Array(totalEdges);
    const bFill = new Uint32Array(N);

    for (let u = 0; u < N; u++) {
      for (let k = this.off[u]; k < this.off[u + 1]; k++) {
        const v = this.dst[k];
        this.bdst[this.boff[v] + bFill[v]++] = u;
      }
    }

    // 4. Invalidate precomputed bitset matrix caches
    this.forwardClosureMatrix = null;
    this.reverseClosureMatrix = null;
  }

  public getModuleId(name: string): number {
    const id = this.nameToId.get(name);
    return id !== undefined ? id : -1;
  }

  public getModuleName(id: number): string {
    return this.idToName[id] || "";
  }

  public getDirectImports(name: string): string[] {
    const u = this.getModuleId(name);
    if (u < 0) return [];
    const start = this.off[u];
    const end = this.off[u + 1];
    const result: string[] = new Array(end - start);
    for (let k = start, idx = 0; k < end; k++, idx++) {
      result[idx] = this.idToName[this.dst[k]];
    }
    return result;
  }

  public getDirectImportedBy(name: string): string[] {
    const u = this.getModuleId(name);
    if (u < 0) return [];
    const start = this.boff[u];
    const end = this.boff[u + 1];
    const result: string[] = new Array(end - start);
    for (let k = start, idx = 0; k < end; k++, idx++) {
      result[idx] = this.idToName[this.bdst[k]];
    }
    return result;
  }

  /**
   * Precomputes full transitive closure matrix using reverse topological bitset OR.
   */
  public precomputeClosureMatrix(): boolean {
    const N = this.numNodes;
    const W = this.wordsPerNode;
    if (N === 0) return true;

    // Kahn's algorithm for topological order
    const inDegree = new Uint32Array(N);
    for (let k = 0; k < this.dst.length; k++) {
      inDegree[this.dst[k]]++;
    }

    const queue = new Uint32Array(N);
    let head = 0;
    let tail = 0;

    for (let i = 0; i < N; i++) {
      if (inDegree[i] === 0) queue[tail++] = i;
    }

    const topoOrder = new Uint32Array(N);
    let topoIdx = 0;

    while (head < tail) {
      const u = queue[head++];
      topoOrder[topoIdx++] = u;
      for (let k = this.off[u]; k < this.off[u + 1]; k++) {
        const v = this.dst[k];
        inDegree[v]--;
        if (inDegree[v] === 0) {
          queue[tail++] = v;
        }
      }
    }

    this.isAcyclic = (topoIdx === N);
    if (!this.isAcyclic) {
      return false; // Graph has cycles, fallback to dynamic BFS
    }

    // Precompute forward closure: process in reverse topological order
    const fMat = new Uint32Array(N * W);
    for (let step = N - 1; step >= 0; step--) {
      const u = topoOrder[step];
      const uBase = u * W;
      for (let k = this.off[u]; k < this.off[u + 1]; k++) {
        const v = this.dst[k];
        const vBase = v * W;
        for (let w = 0; w < W; w++) {
          fMat[uBase + w] |= fMat[vBase + w];
        }
        fMat[uBase + (v >>> 5)] |= (1 << (v & 31));
      }
    }
    this.forwardClosureMatrix = fMat;

    // Precompute reverse closure: process in forward topological order
    const rMat = new Uint32Array(N * W);
    for (let step = 0; step < N; step++) {
      const u = topoOrder[step];
      const uBase = u * W;
      for (let k = this.boff[u]; k < this.boff[u + 1]; k++) {
        const p = this.bdst[k];
        const pBase = p * W;
        for (let w = 0; w < W; w++) {
          rMat[uBase + w] |= rMat[pBase + w];
        }
        rMat[uBase + (p >>> 5)] |= (1 << (p & 31));
      }
    }
    this.reverseClosureMatrix = rMat;

    return true;
  }

  /**
   * High-performance Transitive Closure.
   * Uses bitset matrix if available, or zero-allocation pointer BFS with O(1) cycle checks.
   */
  public getTransitiveClosure(
    rootModule: string,
    direction: "imports" | "importedBy",
    maxDepth: number = 20
  ): TransitiveClosureResult {
    const rootId = this.getModuleId(rootModule);
    if (rootId < 0) {
      return { items: [], depth: 0, hasCycle: false };
    }

    const N = this.numNodes;
    const W = this.wordsPerNode;

    // Fast-path: Precomputed bitset matrix available and unconstrained depth
    const matrix = direction === "imports" ? this.forwardClosureMatrix : this.reverseClosureMatrix;
    if (matrix && maxDepth >= N) {
      const base = rootId * W;
      const items: string[] = [];
      for (let w = 0; w < W; w++) {
        let word = matrix[base + w];
        if (word === 0) continue;
        const bitOffset = w * 32;
        while (word !== 0) {
          const t = word & -word;
          const bit = 31 - Math.clz32(t);
          const targetId = bitOffset + bit;
          if (targetId < N) {
            items.push(this.idToName[targetId]);
          }
          word ^= t;
        }
      }
      return {
        items,
        depth: items.length > 0 ? 1 : 0,
        hasCycle: false,
      };
    }

    // Zero-allocation pointer BFS
    const off = direction === "imports" ? this.off : this.boff;
    const dst = direction === "imports" ? this.dst : this.bdst;

    const visitedBits = new Uint32Array(W);
    const queue = new Uint32Array(N);
    const depth = new Uint16Array(N);
    const parent = new Int32Array(N).fill(-1);

    let head = 0;
    let tail = 0;

    // Enqueue root
    queue[tail++] = rootId;
    visitedBits[rootId >>> 5] |= (1 << (rootId & 31));

    let maxDepthReached = 0;
    let detectedCycle: string[] | undefined;

    while (head < tail) {
      const u = queue[head++];
      const d = depth[u];

      if (d >= maxDepth) continue;

      const start = off[u];
      const end = off[u + 1];

      for (let k = start; k < end; k++) {
        const v = dst[k];

        // O(1) cycle detection: walk parent chain backwards
        let p = u;
        let isCycle = false;
        while (p !== -1) {
          if (p === v) {
            isCycle = true;
            break;
          }
          p = parent[p];
        }

        if (isCycle) {
          if (!detectedCycle) {
            const cycleIds: number[] = [v];
            let curr = u;
            while (curr !== -1) {
              cycleIds.push(curr);
              if (curr === v) break;
              curr = parent[curr];
            }
            cycleIds.reverse();
            detectedCycle = cycleIds.map((id) => this.idToName[id]);
          }
          continue;
        }

        // Bitset visited test
        const wordIdx = v >>> 5;
        const bitMask = 1 << (v & 31);

        if ((visitedBits[wordIdx] & bitMask) === 0) {
          visitedBits[wordIdx] |= bitMask;
          parent[v] = u;
          depth[v] = d + 1;
          if (d + 1 > maxDepthReached) maxDepthReached = d + 1;
          queue[tail++] = v;
        }
      }
    }

    // Convert visited nodes to module names (skipping rootId)
    const resultCount = tail - 1;
    const items: string[] = new Array(resultCount > 0 ? resultCount : 0);
    let outIdx = 0;
    for (let i = 1; i < tail; i++) {
      items[outIdx++] = this.idToName[queue[i]];
    }

    return {
      items,
      depth: maxDepthReached,
      hasCycle: detectedCycle !== undefined,
      cyclePath: detectedCycle,
    };
  }

  public getNodeCount(): number {
    return this.numNodes;
  }

  public getEdgeCount(): number {
    return this.dst.length;
  }
}

export class Lean4IleanIndex {
  private projectRoot: string;
  private cache: Map<string, IleanFile> = new Map();
  private symbolIndex: Map<string, IleanSymbolEntry> = new Map();
  private moduleImportsMap: Map<string, string[]> = new Map();
  private dagIndex: BitsetDAGIndex = new BitsetDAGIndex();

  constructor(projectRoot: string) {
    this.projectRoot = projectRoot;
  }

  public refresh(): void {
    this.cache.clear();
    this.symbolIndex.clear();
    this.moduleImportsMap.clear();

    const candidateRoots = [
      path.join(this.projectRoot, ".lake", "build", "lib", "lean"),
      path.join(this.projectRoot, ".lake", "build", "ir"),
    ];

    // Discover .lake/packages for Mathlib and external libraries
    const packageDirs = [
      path.join(this.projectRoot, ".lake", "packages"),
    ];

    for (const pDir of packageDirs) {
      if (fs.existsSync(pDir)) {
        try {
          const pkgs = fs.readdirSync(pDir, { withFileTypes: true });
          for (const pkg of pkgs) {
            if (pkg.isDirectory()) {
              const pBuild = path.join(pDir, pkg.name, ".lake", "build", "lib", "lean");
              if (fs.existsSync(pBuild)) candidateRoots.push(pBuild);
            }
          }
        } catch {
          // Ignore unreadable package folders
        }
      }
    }

    const visitedDirs = new Set<string>();
    for (const root of candidateRoots) {
      if (fs.existsSync(root) && !visitedDirs.has(root)) {
        visitedDirs.add(root);
        this.scanDir(root);
      }
    }

    // Build high-performance Bitset and CSR/CSC index
    this.dagIndex.build(this.moduleImportsMap);
  }

  private scanDir(dir: string): void {
    try {
      const entries = fs.readdirSync(dir, { withFileTypes: true });
      for (const entry of entries) {
        const fullPath = path.join(dir, entry.name);
        if (entry.isDirectory()) {
          this.scanDir(fullPath);
        } else if (entry.isFile() && entry.name.endsWith(".ilean")) {
          this.loadIlean(fullPath);
        }
      }
    } catch {
      // Ignore unreadable directories
    }
  }

  private loadIlean(filePath: string): void {
    try {
      const raw = fs.readFileSync(filePath, "utf-8");
      const parsed: IleanFile = JSON.parse(raw);
      this.cache.set(filePath, parsed);

      const moduleName = parsed.module || "";

      // Derive source file path
      let sourceFile = "";
      if (moduleName) {
        const relLean = moduleName.replace(/\./g, "/") + ".lean";
        const candidate = path.join(this.projectRoot, relLean);
        if (fs.existsSync(candidate)) {
          sourceFile = path.relative(this.projectRoot, candidate);
        }
      }
      if (!sourceFile) {
        sourceFile = path.relative(this.projectRoot, filePath);
      }

      // 1. Process decls
      if (parsed.decls && typeof parsed.decls === "object") {
        for (const [sym, coords] of Object.entries(parsed.decls)) {
          if (Array.isArray(coords) && coords.length >= 2) {
            const line = ((coords[4] !== undefined ? coords[4] : coords[0]) ?? 0) + 1;
            const col = ((coords[5] !== undefined ? coords[5] : coords[1]) ?? 0) + 1;
            const endLine = coords[2] !== undefined ? coords[2] + 1 : undefined;
            const endCol = coords[3] !== undefined ? coords[3] + 1 : undefined;

            const entry: IleanSymbolEntry = {
              filePath: sourceFile,
              line,
              col,
              endLine,
              endCol,
              module: moduleName,
            };
            if (!this.symbolIndex.has(sym)) {
              this.symbolIndex.set(sym, entry);
            }
            if (moduleName && !sym.startsWith(moduleName)) {
              const fullSym = `${moduleName}.${sym}`;
              if (!this.symbolIndex.has(fullSym)) {
                this.symbolIndex.set(fullSym, entry);
              }
            }
          }
        }
      }

      // 2. Process entries fallback
      if (parsed.entries && typeof parsed.entries === "object") {
        for (const [sym, pos] of Object.entries(parsed.entries)) {
          if (!this.symbolIndex.has(sym)) {
            this.symbolIndex.set(sym, {
              filePath: sourceFile,
              line: pos.line,
              col: pos.col,
              endLine: pos.endLine,
              endCol: pos.endCol,
              module: moduleName,
            });
          }
        }
      }

      // 3. Process directImports
      if (moduleName && parsed.directImports && Array.isArray(parsed.directImports)) {
        const imps: string[] = [];
        for (const item of parsed.directImports) {
          if (Array.isArray(item) && typeof item[0] === "string") {
            imps.push(item[0]);
          } else if (typeof item === "string") {
            imps.push(item);
          }
        }
        this.moduleImportsMap.set(moduleName, imps);
      }
    } catch {
      // Ignore transient or unparseable lockfiles
    }
  }

  public lookupSymbol(symbol: string): IleanSymbolEntry | null {
    if (this.symbolIndex.size === 0) {
      this.refresh();
    }
    const exact = this.symbolIndex.get(symbol);
    if (exact) return exact;

    for (const [k, v] of this.symbolIndex.entries()) {
      if (k.endsWith("." + symbol)) {
        return v;
      }
    }
    return null;
  }

  public getModuleImports(moduleName: string): string[] {
    if (this.dagIndex.getNodeCount() === 0 && this.moduleImportsMap.size === 0) {
      this.refresh();
    }
    return this.dagIndex.getDirectImports(moduleName);
  }

  public getModuleImportedBy(moduleName: string): string[] {
    if (this.dagIndex.getNodeCount() === 0 && this.moduleImportsMap.size === 0) {
      this.refresh();
    }
    return this.dagIndex.getDirectImportedBy(moduleName);
  }

  public getTransitiveClosure(
    rootModule: string,
    direction: "imports" | "importedBy",
    maxDepth: number = 20
  ): TransitiveClosureResult {
    if (this.dagIndex.getNodeCount() === 0 && this.moduleImportsMap.size === 0) {
      this.refresh();
    }
    return this.dagIndex.getTransitiveClosure(rootModule, direction, maxDepth);
  }

  public getAllIndexedSymbolsCount(): number {
    return this.symbolIndex.size;
  }
}

export class LeanSysrootBridge {
  private static cachedPrefix: string | null = null;

  public static getPrefix(): string | null {
    if (!this.cachedPrefix) {
      try {
        const out = execSync("lean --print-prefix", { encoding: "utf-8" }).trim();
        this.cachedPrefix = out;
      } catch {
        return null;
      }
    }
    return this.cachedPrefix;
  }

  public static getIncludeFlags(): string[] {
    const prefix = this.getPrefix();
    if (!prefix) return [];

    const includeDir = path.join(prefix, "include");
    const clangDir = path.join(includeDir, "clang");
    const flags: string[] = [];

    if (fs.existsSync(includeDir)) {
      flags.push(`-I${includeDir}`);
    }
    if (fs.existsSync(clangDir)) {
      flags.push("-isystem", clangDir);
    }
    return flags;
  }

  public static inspectFFI(projectRoot: string, externName?: string): string {
    const flags = this.getIncludeFlags();
    const prefix = this.getPrefix();
    const lines: string[] = [
      "=== Lean 4 C FFI Environment ===",
      `Toolchain Prefix: ${prefix || "(not detected)"}`,
      `Sysroot Include Flags: ${flags.length > 0 ? flags.join(" ") : "(none)"}`,
    ];

    if (prefix) {
      const leanH = path.join(prefix, "include", "lean", "lean.h");
      const exists = fs.existsSync(leanH);
      lines.push(`Sysroot Header (lean/lean.h): ${exists ? "Found (" + leanH + ")" : "Not found"}`);
    }

    if (externName) {
      lines.push(`\nInspecting symbol: '${externName}'`);
      const matches: string[] = [];
      const scanLeanDir = (dir: string) => {
        if (!fs.existsSync(dir)) return;
        const entries = fs.readdirSync(dir, { withFileTypes: true });
        for (const e of entries) {
          if (e.name.startsWith(".") || e.name === "node_modules" || e.name === "fermats-last-theorem") continue;
          const p = path.join(dir, e.name);
          if (e.isDirectory()) {
            scanLeanDir(p);
          } else if (e.isFile() && e.name.endsWith(".lean")) {
            try {
              const content = fs.readFileSync(p, "utf-8");
              if (content.includes("extern") && content.includes(externName)) {
                matches.push(path.relative(projectRoot, p));
              }
            } catch {
              // Ignore unreadable files
            }
          }
        }
      };
      scanLeanDir(projectRoot);

      if (matches.length > 0) {
        lines.push(`Found references in ${matches.length} file(s):`);
        for (const m of matches) lines.push(`  - ${m}`);
      } else {
        lines.push(`No @[extern "${externName}"] declarations located in project Lean files.`);
      }
    }

    return lines.join("\n");
  }
}

export function formatGoalAsMarkdown(goalText: string): string {
  if (!goalText || goalText.trim().length === 0) {
    return "No active goals (proof complete or out of tactic scope).";
  }
  return "```lean\n" + goalText.trim() + "\n```";
}

export function filterGoalText(goalText: string, opts: GoalFilterOptions = {}): string {
  if (!goalText || goalText.trim().length === 0) {
    return "No active goals (proof complete or out of tactic scope).";
  }
  if (goalText.startsWith("Lake LSP error:") || goalText.startsWith("File not found:")) {
    return goalText;
  }

  const hideTypeclasses = opts.hideTypeclasses ?? true;
  const hideInaccessible = opts.hideInaccessible ?? true;
  const onlyTarget = opts.onlyTarget ?? false;
  const maxGoals = opts.maxGoals ?? 3;

  const rawBlocks = goalText.split(/\n\n(?=(?:case\s+|\d+\s+goals?|\u22A2|\|-))/);
  const filteredBlocks: string[] = [];

  const knownClassHeads = new Set([
    "Decidable", "DecidableEq", "DecidableRel", "DecidablePred",
    "Inhabited", "Nonempty", "Subsingleton", "Unique", "Empty",
    "Fintype", "Finite", "Countable", "Infinite",
    "Semigroup", "CommSemigroup", "Monoid", "CommMonoid", "Group", "CommGroup", "AddCommGroup",
    "Semiring", "CommSemiring", "Ring", "CommRing", "Field", "DivisionRing",
    "Module", "Algebra", "SMul", "SMulZeroClass", "DistribMulAction", "MulAction", "IsScalarTower",
    "SMulCommClass", "FaithfulSMul",
    "TopologicalSpace", "UniformSpace", "MetricSpace", "NormedAddCommGroup", "NormedSpace",
    "CompleteSpace", "CompactSpace", "LocallyCompactSpace", "ConnectedSpace", "T2Space",
    "MeasureSpace", "MeasurableSpace", "BorelSpace",
    "Category", "Functor", "NaturalTransformation", "HasLimits", "HasColimits",
    "Preorder", "PartialOrder", "LinearOrder", "Lattice", "CompleteLattice",
    "IsDomain", "IsDedekindDomain", "IsPrincipalIdealRing", "IsNoetherianRing", "IsArtinianRing",
    "IsLocalRing", "IsLocalHom", "HenselianLocalRing",
    "Coalgebra", "Bialgebra", "HopfAlgebra",
  ]);

  for (let bIdx = 0; bIdx < rawBlocks.length; bIdx++) {
    if (filteredBlocks.length >= maxGoals) {
      filteredBlocks.push(`-- (... and ${rawBlocks.length - bIdx} more goals omitted)`);
      break;
    }
    const block = rawBlocks[bIdx].trim();
    if (!block) continue;

    const lines = block.split("\n");
    let caseHeader = "";
    const hyps: Array<{ full: string; name: string; type: string }> = [];
    let target = "";
    let inTarget = false;
    let currentHyp: { full: string; name: string; type: string } | null = null;

    for (const line of lines) {
      if (/^case\s+/.test(line)) {
        caseHeader = line.trim();
      } else if (/^(\u22A2|\|-)\s*/.test(line)) {
        inTarget = true;
        currentHyp = null;
        target = line;
      } else if (inTarget) {
        target += "\n" + line;
      } else if (/^[^\s:]+(?:\s+[^\s:]+)*\s*:\s*/.test(line) || /^\[.*\]$/.test(line.trim())) {
        const colonIdx = line.indexOf(":");
        const name = colonIdx !== -1 ? line.slice(0, colonIdx).trim() : line.trim();
        const type = colonIdx !== -1 ? line.slice(colonIdx + 1).trim() : "";
        currentHyp = { full: line, name, type };
        hyps.push(currentHyp);
      } else if (currentHyp) {
        currentHyp.full += "\n" + line;
      }
    }

    const keptHyps: string[] = [];
    const omittedNames: string[] = [];

    if (!onlyTarget) {
      for (const h of hyps) {
        const isInstName = /^inst[\u271D\u2020\u00B0-\u00BE\u2070-\u207F0-9_]*/i.test(h.name) ||
          h.name.startsWith("[") ||
          h.name.startsWith("_inst");
        const isInaccessibleName = h.name.includes("\u271D") || h.name.includes("\u2020") || h.name.startsWith("_");
        const firstWord = h.type.trim().split(/[\s(\[{]/)[0] || "";
        const isKnownClassType = knownClassHeads.has(firstWord) ||
          firstWord.startsWith("Is") ||
          firstWord.startsWith("Has") ||
          firstWord.endsWith("Class") ||
          firstWord.endsWith("Category");

        const shouldOmitTypeclass = hideTypeclasses && (isInstName || isKnownClassType);
        const shouldOmitInaccessible = hideInaccessible && isInaccessibleName;

        if (shouldOmitTypeclass || shouldOmitInaccessible) {
          omittedNames.push(h.name);
        } else {
          keptHyps.push(h.full);
        }
      }
    }

    const outLines: string[] = [];
    if (caseHeader) outLines.push(caseHeader);
    if (!onlyTarget && keptHyps.length > 0) outLines.push(...keptHyps);
    if (target) outLines.push(target);
    if (omittedNames.length > 0) {
      const preview = omittedNames.slice(0, 4).join(", ");
      const suffix = omittedNames.length > 4 ? `... (+${omittedNames.length - 4} more)` : "";
      outLines.push(`-- [Filtered ${omittedNames.length} ambient instances/inaccessibles: ${preview}${suffix}]`);
    }

    filteredBlocks.push(outLines.join("\n"));
  }

  return "```lean\n" + filteredBlocks.join("\n\n") + "\n```";
}

export interface BuildLockStatus {
  isLocked: boolean;
  pid?: number;
  lane?: string;
  source: "lockfile" | "process_table" | "global_workspace_lock" | "none";
  detail?: string;
}

export class LakeBuildGuard {
  public static getLockFilePath(leanRoot: string): string {
    return path.join(leanRoot, ".lake", "build", ".lake.lock");
  }

  public static checkLock(leanRoot: string): BuildLockStatus {
    return this.inspectBuildActivity(leanRoot);
  }

  public static inspectBuildActivity(leanRoot: string): BuildLockStatus {
    const lockPath = this.getLockFilePath(leanRoot);

    if (fs.existsSync(lockPath)) {
      try {
        const raw = fs.readFileSync(lockPath, "utf-8");
        const meta = JSON.parse(raw);
        const pid = Number(meta.pid);
        if (pid && this.isPidAlive(pid)) {
          return {
            isLocked: true,
            pid,
            lane: meta.lane || "unknown",
            source: "lockfile",
            detail: `Active Lake build registered in ${lockPath} by PID ${pid}`,
          };
        } else {
          try {
            fs.unlinkSync(lockPath);
          } catch {
            // Ignore race condition on unlink
          }
        }
      } catch {
        return {
          isLocked: true,
          source: "lockfile",
          detail: `Unparseable build lockfile present at ${lockPath}`,
        };
      }
    }

    try {
      const pgrepOut = execSync("pgrep -f 'lake (build|compile|env)'", {
        encoding: "utf-8",
        stdio: ["ignore", "pipe", "ignore"],
      }).trim();

      if (pgrepOut) {
        const pids = pgrepOut.split("\n").map((p) => parseInt(p.trim(), 10)).filter(Boolean);
        if (pids.length > 0) {
          return {
            isLocked: true,
            pid: pids[0],
            source: "process_table",
            detail: `Active lake build processes detected: [${pids.join(", ")}]`,
          };
        }
      }
    } catch {
      // pgrep exits with 1 when no processes match
    }

    // Check global workspace build lock across all parallel packages
    const globalLockPaths = [
      "/dev/shm/lean_global_workspace.lock",
      path.join(os.tmpdir(), "lean_global_workspace.lock"),
    ];
    for (const gLock of globalLockPaths) {
      if (fs.existsSync(gLock)) {
        try {
          const raw = fs.readFileSync(gLock, "utf-8");
          const meta = JSON.parse(raw);
          const pid = Number(meta.pid);
          if (pid && this.isPidAlive(pid)) {
            return {
              isLocked: true,
              pid,
              lane: meta.packageName || meta.lane || "multi-package-build",
              source: "global_workspace_lock",
              detail: `Active workspace build in package '${meta.packageName || "unknown"}' by PID ${pid}`,
            };
          } else {
            try {
              fs.unlinkSync(gLock);
            } catch {
              // Ignore unlink race
            }
          }
        } catch {
          // Ignore parse errors on transient lockfiles
        }
      }
    }

    return { isLocked: false, source: "none" };
  }

  public static isPidAlive(pid: number): boolean {
    try {
      process.kill(pid, 0);
      return true;
    } catch {
      return false;
    }
  }
}

/**
 * MultiPackageWorkspaceCoordinator
 *
 * Implements Lane FFF (ACT-FLT-64).
 * Auto-discovers and indexes all parallel Lean 4 packages within the workspace:
 * - Root package: docs/easci/lean
 * - Mini-projects: packages/tacit-foundations, packages/stochastic-ccv,
 *   packages/cusp-catastrophe, packages/phase-portrait,
 *   packages/reinforcement-learning, packages/agentic-safety,
 *   packages/provenance-chain.
 * Resolves document URIs to their owning package root.
 */
export class MultiPackageWorkspaceCoordinator {
  private projectRoot: string;
  private knownPackages: Map<string, string> = new Map();

  constructor(projectRoot: string) {
    this.projectRoot = projectRoot;
    this.discoverPackages();
  }

  public discoverPackages(): Map<string, string> {
    this.knownPackages.clear();
    const easciLean = path.join(this.projectRoot, "docs", "easci", "lean");
    if (fs.existsSync(path.join(easciLean, "lakefile.lean"))) {
      this.knownPackages.set("docs/easci/lean", easciLean);
    }
    const packagesDir = path.join(this.projectRoot, "packages");
    if (fs.existsSync(packagesDir)) {
      try {
        const entries = fs.readdirSync(packagesDir, { withFileTypes: true });
        for (const ent of entries) {
          if (ent.isDirectory()) {
            const pkgPath = path.join(packagesDir, ent.name);
            if (
              fs.existsSync(path.join(pkgPath, "lakefile.lean")) ||
              fs.existsSync(path.join(pkgPath, "lakefile.toml"))
            ) {
              this.knownPackages.set(ent.name, pkgPath);
            }
          }
        }
      } catch {
        // Ignore read errors
      }
    }
    return this.knownPackages;
  }

  public getPackageCount(): number {
    return this.knownPackages.size;
  }

  public getKnownPackages(): Map<string, string> {
    return new Map(this.knownPackages);
  }

  public resolvePackageForFile(filePath: string): { name: string; root: string } | null {
    const abs = path.resolve(filePath);
    for (const [name, root] of this.knownPackages.entries()) {
      if (abs.startsWith(root + path.sep) || abs === root) {
        return { name, root };
      }
    }
    return null;
  }
}


export interface SnapshotHeader {
  magic: number;
  version: number;
  capacity: number;
  slotSize: number;
  writeSeq: bigint;
  readSeq: bigint;
  sessionId: bigint;
  droppedCount: bigint;
}

export interface GoalSnapshot {
  seq: bigint;
  timestampNs: bigint;
  fileHash: bigint;
  filePath: string;
  line: number;
  col: number;
  flags: number;
  goalsCount: number;
  goalText: string;
}

export class SharedMemorySnapshotRing {
  public static readonly MAGIC = 0x4C45414E; // "LEAN"
  public static readonly VERSION = 1;
  public static readonly HEADER_SIZE = 64;
  public static readonly SLOT_HEADER_SIZE = 64;
  public static readonly DEFAULT_CAPACITY = 64;
  public static readonly DEFAULT_SLOT_SIZE = 65536; // 64 KB per slot

  private fd: number;
  private buffer: Buffer;
  private capacity: number;
  private slotSize: number;
  private totalSize: number;
  private shmPath: string;
  private isOwner: boolean;

  private constructor(
    shmPath: string,
    fd: number,
    buffer: Buffer,
    capacity: number,
    slotSize: number,
    isOwner: boolean
  ) {
    this.shmPath = shmPath;
    this.fd = fd;
    this.buffer = buffer;
    this.capacity = capacity;
    this.slotSize = slotSize;
    this.totalSize = buffer.length;
    this.isOwner = isOwner;
  }

  public static create(
    shmPath: string,
    capacity: number = SharedMemorySnapshotRing.DEFAULT_CAPACITY,
    slotSize: number = SharedMemorySnapshotRing.DEFAULT_SLOT_SIZE
  ): SharedMemorySnapshotRing {
    const totalSize = SharedMemorySnapshotRing.HEADER_SIZE + capacity * slotSize;
    const dir = path.dirname(shmPath);
    if (!fs.existsSync(dir)) {
      fs.mkdirSync(dir, { recursive: true });
    }

    const fd = fs.openSync(shmPath, "w+");
    fs.ftruncateSync(fd, totalSize);
    const buffer = Buffer.alloc(totalSize);

    // Initialize Header
    buffer.writeUInt32LE(SharedMemorySnapshotRing.MAGIC, 0);
    buffer.writeUInt32LE(SharedMemorySnapshotRing.VERSION, 4);
    buffer.writeUInt32LE(capacity, 8);
    buffer.writeUInt32LE(slotSize, 12);
    buffer.writeBigUInt64LE(0n, 16); // writeSeq
    buffer.writeBigUInt64LE(0n, 24); // readSeq
    buffer.writeBigUInt64LE(BigInt(process.pid), 32); // sessionId
    buffer.writeBigUInt64LE(0n, 40); // droppedCount

    fs.writeSync(fd, buffer, 0, totalSize, 0);

    return new SharedMemorySnapshotRing(shmPath, fd, buffer, capacity, slotSize, true);
  }

  public static open(shmPath: string): SharedMemorySnapshotRing | null {
    if (!fs.existsSync(shmPath)) return null;
    try {
      const fd = fs.openSync(shmPath, "r+");
      const stat = fs.fstatSync(fd);
      const buffer = Buffer.alloc(stat.size);
      fs.readSync(fd, buffer, 0, stat.size, 0);

      const magic = buffer.readUInt32LE(0);
      if (magic !== SharedMemorySnapshotRing.MAGIC) {
        fs.closeSync(fd);
        return null;
      }
      const capacity = buffer.readUInt32LE(8);
      const slotSize = buffer.readUInt32LE(12);

      return new SharedMemorySnapshotRing(shmPath, fd, buffer, capacity, slotSize, false);
    } catch {
      return null;
    }
  }

  public static computePathHash(filePath: string): bigint {
    let hash = 0xcbf29ce484222325n;
    const fnvPrime = 0x100000001b3n;
    const buf = Buffer.from(filePath, "utf-8");
    for (let i = 0; i < buf.length; i++) {
      hash ^= BigInt(buf[i]);
      hash = (hash * fnvPrime) & 0xffffffffffffffffn;
    }
    return hash;
  }

  public writeSnapshot(
    filePath: string,
    line: number,
    col: number,
    goalText: string,
    flags: number = 1,
    goalsCount: number = 1
  ): bigint {
    const curSeq = this.buffer.readBigUInt64LE(16);
    const nextSeq = curSeq + 1n;
    const slotIdx = Number((nextSeq - 1n) % BigInt(this.capacity));
    const slotOffset = SharedMemorySnapshotRing.HEADER_SIZE + slotIdx * this.slotSize;

    const fileHash = SharedMemorySnapshotRing.computePathHash(filePath);
    const filePathBuf = Buffer.from(filePath, "utf-8");
    const goalTextBuf = Buffer.from(goalText, "utf-8");

    const maxPayload = this.slotSize - SharedMemorySnapshotRing.SLOT_HEADER_SIZE;
    const availableGoalLen = Math.max(0, maxPayload - filePathBuf.length);
    const finalGoalLen = Math.min(goalTextBuf.length, availableGoalLen);

    // 1. Invalidate slot seqlock
    this.buffer.writeBigUInt64LE(0n, slotOffset);

    // 2. Populate slot metadata
    const nowNs = process.hrtime.bigint();
    this.buffer.writeBigUInt64LE(nowNs, slotOffset + 8);
    this.buffer.writeBigUInt64LE(fileHash, slotOffset + 16);
    this.buffer.writeUInt32LE(line, slotOffset + 24);
    this.buffer.writeUInt32LE(col, slotOffset + 28);
    this.buffer.writeUInt32LE(flags, slotOffset + 32);
    this.buffer.writeUInt32LE(finalGoalLen, slotOffset + 36);
    this.buffer.writeUInt32LE(goalsCount, slotOffset + 40);
    this.buffer.writeUInt32LE(filePathBuf.length, slotOffset + 44);

    // 3. Write payload (zero JSON escaping)
    const payloadOffset = slotOffset + SharedMemorySnapshotRing.SLOT_HEADER_SIZE;
    filePathBuf.copy(this.buffer, payloadOffset, 0, filePathBuf.length);
    goalTextBuf.copy(this.buffer, payloadOffset + filePathBuf.length, 0, finalGoalLen);

    // 4. Commit slot seqlock
    this.buffer.writeBigUInt64LE(nextSeq, slotOffset);

    // 5. Commit global writeSeq
    this.buffer.writeBigUInt64LE(nextSeq, 16);

    // Persist to underlying memory buffer
    fs.writeSync(this.fd, this.buffer, slotOffset, this.slotSize, slotOffset);
    fs.writeSync(this.fd, this.buffer, 16, 8, 16);

    return nextSeq;
  }

  public readLatest(fileFilter?: string): GoalSnapshot | null {
    fs.readSync(this.fd, this.buffer, 0, SharedMemorySnapshotRing.HEADER_SIZE, 0);
    const writeSeq = this.buffer.readBigUInt64LE(16);
    if (writeSeq === 0n) return null;

    const filterHash = fileFilter ? SharedMemorySnapshotRing.computePathHash(fileFilter) : null;

    const scanLimit = BigInt(this.capacity);
    for (let i = 0n; i < scanLimit; i++) {
      const targetSeq = writeSeq - i;
      if (targetSeq <= 0n) break;

      const slotIdx = Number((targetSeq - 1n) % BigInt(this.capacity));
      const slotOffset = SharedMemorySnapshotRing.HEADER_SIZE + slotIdx * this.slotSize;

      fs.readSync(this.fd, this.buffer, slotOffset, SharedMemorySnapshotRing.SLOT_HEADER_SIZE, slotOffset);

      const seqBefore = this.buffer.readBigUInt64LE(slotOffset);
      if (seqBefore !== targetSeq) continue;

      const fileHash = this.buffer.readBigUInt64LE(slotOffset + 16);
      if (filterHash !== null && fileHash !== filterHash) continue;

      const filePathLen = this.buffer.readUInt32LE(slotOffset + 44);
      const goalLen = this.buffer.readUInt32LE(slotOffset + 36);

      const payloadOffset = slotOffset + SharedMemorySnapshotRing.SLOT_HEADER_SIZE;
      fs.readSync(this.fd, this.buffer, payloadOffset, filePathLen + goalLen, payloadOffset);

      const seqAfter = this.buffer.readBigUInt64LE(slotOffset);
      if (seqAfter !== targetSeq) continue;

      const timestampNs = this.buffer.readBigUInt64LE(slotOffset + 8);
      const line = this.buffer.readUInt32LE(slotOffset + 24);
      const col = this.buffer.readUInt32LE(slotOffset + 28);
      const flags = this.buffer.readUInt32LE(slotOffset + 32);
      const goalsCount = this.buffer.readUInt32LE(slotOffset + 40);

      const filePath = this.buffer.toString("utf-8", payloadOffset, payloadOffset + filePathLen);
      const goalText = this.buffer.toString("utf-8", payloadOffset + filePathLen, payloadOffset + filePathLen + goalLen);

      return {
        seq: targetSeq,
        timestampNs,
        fileHash,
        filePath,
        line,
        col,
        flags,
        goalsCount,
        goalText,
      };
    }

    return null;
  }

  public dispose(): void {
    try {
      fs.closeSync(this.fd);
      if (this.isOwner && fs.existsSync(this.shmPath)) {
        fs.unlinkSync(this.shmPath);
      }
    } catch {}
  }
}

export interface TrackedFileWorker {
  uri: string;
  absPath: string;
  version: number;
  mtimeMs: number;
  lastAccessedMs: number;
}

export interface FileWorkerSession {
  child: ChildProcess;
  leanRoot: string;
  nextId: number;
  pendingRequests: Map<number, { resolve: (val: any) => void; reject: (err: any) => void }>;
  openFiles: Map<string, TrackedFileWorker>;
  buffer: Buffer;
  lastActiveMs: number;
}

export class FileWorkerManager {
  private projectRoot: string;
  private shmRing: SharedMemorySnapshotRing | null = null;
  private sessions: Map<string, FileWorkerSession> = new Map();
  private reaperTimer: NodeJS.Timeout | null = null;
  private readonly idleFileTimeoutMs: number = 60000;
  private readonly idleSessionTimeoutMs: number = 120000;
  private readonly memoryCeilingKb: number = 1048576; // 1 GB RSS ceiling

  constructor(projectRoot: string) {
    this.projectRoot = path.resolve(projectRoot);
    this.startLifecycleReaper();
    this.initShmRing();
  }

  public findLeanRoot(targetFile: string): string {
    let curr = path.dirname(path.resolve(targetFile));
    while (curr !== path.dirname(curr)) {
      if (
        fs.existsSync(path.join(curr, "lakefile.lean")) ||
        fs.existsSync(path.join(curr, "lakefile.toml")) ||
        fs.existsSync(path.join(curr, "lean-toolchain"))
      ) {
        return curr;
      }
      curr = path.dirname(curr);
    }
    return this.projectRoot;
  }


  private initShmRing(): void {
    const shmDir = fs.existsSync("/dev/shm") ? "/dev/shm" : os.tmpdir();
    const shmPath = process.env.LEAN_SHM_PATH || path.join(shmDir, `lean_lsp_mcp_${process.pid}.shm`);
    try {
      this.shmRing = SharedMemorySnapshotRing.create(shmPath);
    } catch {
      this.shmRing = null;
    }
  }

  public getShmRing(): SharedMemorySnapshotRing | null {
    return this.shmRing;
  }
  private startLifecycleReaper(): void {
    if (this.reaperTimer) return;
    this.reaperTimer = setInterval(() => {
      this.reapIdleAndHeavyWorkers();
    }, 15000);
    if (this.reaperTimer.unref) {
      this.reaperTimer.unref();
    }
  }

  public reapIdleAndHeavyWorkers(): void {
    const now = Date.now();

    for (const [leanRoot, session] of this.sessions.entries()) {
      const sessionRssKb = this.getProcessRssKb(session.child.pid);
      const isSessionHeavy = sessionRssKb > this.memoryCeilingKb * 2;

      if (isSessionHeavy) {
        this.disposeSession(leanRoot);
        continue;
      }

      const filesToClose: string[] = [];
      for (const [absPath, fileInfo] of session.openFiles.entries()) {
        if (now - fileInfo.lastAccessedMs > this.idleFileTimeoutMs) {
          filesToClose.push(absPath);
        }
      }

      for (const absPath of filesToClose) {
        const fileInfo = session.openFiles.get(absPath)!;
        this.sendNotification(session, "textDocument/didClose", {
          textDocument: { uri: fileInfo.uri },
        });
        session.openFiles.delete(absPath);
      }

      if (session.openFiles.size === 0 && now - session.lastActiveMs > this.idleSessionTimeoutMs) {
        this.disposeSession(leanRoot);
      }
    }
  }

  public getProcessRssKb(pid?: number): number {
    if (!pid) return 0;
    try {
      const statusPath = `/proc/${pid}/status`;
      if (!fs.existsSync(statusPath)) return 0;
      const content = fs.readFileSync(statusPath, "utf-8");
      const match = content.match(/VmRSS:\s*(\d+)\s*kB/i);
      return match ? parseInt(match[1], 10) : 0;
    } catch {
      return 0;
    }
  }

  private async ensureSession(leanRoot: string): Promise<FileWorkerSession> {
    let session = this.sessions.get(leanRoot);
    if (session && session.child && session.child.exitCode === null) {
      session.lastActiveMs = Date.now();
      return session;
    }

    if (session) {
      this.disposeSession(leanRoot);
    }

    const child = spawn("lake", ["serve"], {
      cwd: leanRoot,
      stdio: ["pipe", "pipe", "ignore"],
    });

    session = {
      child,
      leanRoot,
      nextId: 1,
      pendingRequests: new Map(),
      openFiles: new Map(),
      buffer: Buffer.alloc(0),
      lastActiveMs: Date.now(),
    };

    session.child.stdout?.on("data", (chunk: Buffer) => {
      session!.buffer = Buffer.concat([session!.buffer, chunk]);
      while (true) {
        const idx = session!.buffer.indexOf("\r\n\r\n");
        if (idx === -1) break;
        const header = session!.buffer.subarray(0, idx).toString("utf-8");
        const match = header.match(/Content-Length:\s*(\d+)/i);
        if (!match) {
          session!.buffer = session!.buffer.subarray(idx + 4);
          continue;
        }
        const len = parseInt(match[1], 10);
        if (session!.buffer.length < idx + 4 + len) break;
        const body = session!.buffer.subarray(idx + 4, idx + 4 + len).toString("utf-8");
        session!.buffer = session!.buffer.subarray(idx + 4 + len);
        try {
          const parsed = JSON.parse(body);
          if (parsed.id !== undefined && session!.pendingRequests.has(parsed.id)) {
            const handler = session!.pendingRequests.get(parsed.id)!;
            session!.pendingRequests.delete(parsed.id);
            if (parsed.error) {
              handler.reject(new Error(parsed.error.message || JSON.stringify(parsed.error)));
            } else {
              handler.resolve(parsed.result);
            }
          }
        } catch {
          // Ignore transient parsing errors
        }
      }
    });

    session.child.on("error", () => {});
    session.child.on("exit", () => {
      this.sessions.delete(leanRoot);
    });

    this.sessions.set(leanRoot, session);

    await this.sendRequest(session, "initialize", {
      processId: process.pid,
      rootUri: pathToFileURL(leanRoot).href,
      capabilities: {},
    });

    this.sendNotification(session, "initialized", {});
    return session;
  }

  private sendRequest(session: FileWorkerSession, method: string, params: any): Promise<any> {
    return new Promise((resolve, reject) => {
      const id = session.nextId++;
      const timer = setTimeout(() => {
        session.pendingRequests.delete(id);
        reject(new Error(`Timeout waiting for LSP response to ${method} (id: ${id})`));
      }, 25000);

      session.pendingRequests.set(id, {
        resolve: (val) => {
          clearTimeout(timer);
          resolve(val);
        },
        reject: (err) => {
          clearTimeout(timer);
          reject(err);
        },
      });

      const msg = JSON.stringify({ jsonrpc: "2.0", id, method, params });
      const header = `Content-Length: ${Buffer.byteLength(msg, "utf-8")}\r\n\r\n`;
      session.child.stdin?.write(header + msg);
    });
  }

  private sendNotification(session: FileWorkerSession, method: string, params: any): void {
    const msg = JSON.stringify({ jsonrpc: "2.0", method, params });
    const header = `Content-Length: ${Buffer.byteLength(msg, "utf-8")}\r\n\r\n`;
    session.child.stdin?.write(header + msg);
  }

  private syncDocument(session: FileWorkerSession, absPath: string): string {
    const uri = pathToFileURL(absPath).href;
    const stat = fs.statSync(absPath);
    const mtimeMs = stat.mtimeMs;
    const now = Date.now();

    let fileInfo = session.openFiles.get(absPath);
    if (!fileInfo) {
      const text = fs.readFileSync(absPath, "utf-8");
      this.sendNotification(session, "textDocument/didOpen", {
        textDocument: {
          uri,
          languageId: "lean4",
          version: 1,
          text,
        },
      });
      fileInfo = {
        uri,
        absPath,
        version: 1,
        mtimeMs,
        lastAccessedMs: now,
      };
      session.openFiles.set(absPath, fileInfo);
    } else {
      fileInfo.lastAccessedMs = now;
      if (mtimeMs > fileInfo.mtimeMs) {
        const newText = fs.readFileSync(absPath, "utf-8");
        fileInfo.version++;
        fileInfo.mtimeMs = mtimeMs;
        this.sendNotification(session, "textDocument/didChange", {
          textDocument: {
            uri,
            version: fileInfo.version,
          },
          contentChanges: [{ text: newText }],
        });
      }
    }

    session.lastActiveMs = now;
    return uri;
  }

  public async getGoal(
    filePath: string,
    line: number,
    col: number,
    filterOpts?: GoalFilterOptions,
    ileanIndex?: Lean4IleanIndex
  ): Promise<string> {
    const absPath = path.isAbsolute(filePath) ? filePath : path.resolve(this.projectRoot, filePath);
    if (!fs.existsSync(absPath)) {
      return `File not found: ${filePath}`;
    }

    const leanRoot = this.findLeanRoot(absPath);
    const buildStatus = LakeBuildGuard.inspectBuildActivity(leanRoot);
    if (buildStatus.isLocked) {
      this.suspendSessionFiles(leanRoot);
      return this.generateZeroBuildFallback(absPath, line, col, buildStatus, ileanIndex);
    }

    try {
      const session = await this.ensureSession(leanRoot);
      const uri = this.syncDocument(session, absPath);

      const res = await this.sendRequest(session, "$/lean/plainGoal", {
        textDocument: { uri },
        position: {
          line: Math.max(0, line - 1),
          character: Math.max(0, col - 1),
        },
      });

      const goalText = res?.rendered || (Array.isArray(res?.goals) ? res.goals.join("\n\n") : "");
      if (filterOpts) {
        return filterGoalText(goalText, filterOpts);
      }
      return formatGoalAsMarkdown(goalText);
    } catch (err: any) {
      return `Lake LSP error: ${err.message || String(err)}`;
    }
  }

  public async getTermGoal(filePath: string, line: number, col: number): Promise<string> {
    const absPath = path.isAbsolute(filePath) ? filePath : path.resolve(this.projectRoot, filePath);
    if (!fs.existsSync(absPath)) {
      return `File not found: ${filePath}`;
    }

    const leanRoot = this.findLeanRoot(absPath);
    const buildStatus = LakeBuildGuard.inspectBuildActivity(leanRoot);
    if (buildStatus.isLocked) {
      return `[Zero-Build Concurrency Gate] Term goal query suspended during active Lake build (${buildStatus.detail || buildStatus.source}).`;
    }

    try {
      const session = await this.ensureSession(leanRoot);
      const uri = this.syncDocument(session, absPath);

      const res = await this.sendRequest(session, "$/lean/plainTermGoal", {
        textDocument: { uri },
        position: {
          line: Math.max(0, line - 1),
          character: Math.max(0, col - 1),
        },
      });

      const goalText = res?.rendered || res?.goal || "";
      return formatGoalAsMarkdown(goalText);
    } catch (err: any) {
      return `Lake LSP error: ${err.message || String(err)}`;
    }
  }

  private suspendSessionFiles(leanRoot: string): void {
    const session = this.sessions.get(leanRoot);
    if (!session) return;
    for (const fileInfo of session.openFiles.values()) {
      try {
        this.sendNotification(session, "textDocument/didClose", {
          textDocument: { uri: fileInfo.uri },
        });
      } catch {
        // Ignore write failures during suspension
      }
    }
    session.openFiles.clear();
  }

  private generateZeroBuildFallback(
    absPath: string,
    line: number,
    col: number,
    buildStatus: BuildLockStatus,
    ileanIndex?: Lean4IleanIndex
  ): string {
    const relPath = path.relative(this.projectRoot, absPath);
    const lines = [
      `[Zero-Build Concurrency Gate] Active Lake build detected (${buildStatus.detail || buildStatus.source}).`,
      `Interactive FileWorker suspended to prevent .olean corruption and bus errors.`,
      `Offline Diversion:`,
      `  Target: ${relPath} (Line ${line}, Col ${col})`,
    ];

    if (ileanIndex) {
      const relLean = relPath.replace(/\.lean$/, "").replace(/\//g, ".");
      const imports = ileanIndex.getModuleImports(relLean);
      if (imports.length > 0) {
        lines.push(`  Module: ${relLean}`);
        lines.push(`  Dependencies (${imports.length}): ${imports.slice(0, 4).join(", ")}${imports.length > 4 ? "..." : ""}`);
      }
    }

    lines.push(`\nQuery queued for post-compilation verification. Interactive state will refresh automatically upon build completion.`);
    return lines.join("\n");
  }

  public disposeSession(leanRoot: string): void {
    const session = this.sessions.get(leanRoot);
    if (session) {
      try {
        session.child.kill();
      } catch {}
      this.sessions.delete(leanRoot);
    }
  }

  public dispose(): void {
    if (this.shmRing) {
      this.shmRing.dispose();
      this.shmRing = null;
    }
    if (this.reaperTimer) {
      clearInterval(this.reaperTimer);
      this.reaperTimer = null;
    }
    for (const leanRoot of Array.from(this.sessions.keys())) {
      this.disposeSession(leanRoot);
    }
  }
}

export type LakeServerManager = FileWorkerManager;
export const LakeServerManager = FileWorkerManager;

export class McpServer {
  private projectRoot: string;
  private ileanIndex: Lean4IleanIndex;
  private lakeManager: LakeServerManager;
  private buffer: string = "";

  constructor(projectRoot: string = process.cwd()) {
    this.projectRoot = projectRoot;
    this.ileanIndex = new Lean4IleanIndex(projectRoot);
    this.ileanIndex.refresh();
    this.lakeManager = new LakeServerManager(projectRoot);
  }

  public getIleanIndex(): Lean4IleanIndex {
    return this.ileanIndex;
  }

  public getLakeManager(): LakeServerManager {
    return this.lakeManager;
  }

  public async handleMessage(req: any): Promise<McpResponse | null> {
    if (!req || typeof req !== "object") return null;
    const { id, method, params } = req;

    if (id === undefined || id === null) {
      if (method === "notifications/initialized" || method === "initialized") {
        return null;
      }
      return null;
    }

    try {
      switch (method) {
        case "initialize":
          return {
            jsonrpc: "2.0",
            id,
            result: {
              protocolVersion: "2024-11-05",
              capabilities: {
                tools: {},
              },
              serverInfo: {
                name: "lean-lsp-mcp",
                version: "0.2.0",
              },
            },
          };

        case "ping":
          return {
            jsonrpc: "2.0",
            id,
            result: {},
          };

        case "tools/list": {
          const disabledTools = (process.env.LEAN_MCP_DISABLED_TOOLS || "").split(",").map(t => t.trim()).filter(Boolean);
          const activeTools = TOOL_DEFINITIONS.filter(t => !disabledTools.includes(t.name));
          return {
            jsonrpc: "2.0",
            id,
            result: {
              tools: activeTools,
            },
          };
        }

        case "tools/call": {
          const toolName = params?.name;
          const toolArgs = params?.arguments || {};
          const contentText = await this.executeTool(toolName, toolArgs);
          return {
            jsonrpc: "2.0",
            id,
            result: {
              content: [
                {
                  type: "text",
                  text: contentText,
                },
              ],
              isError: false,
            },
          };
        }

        default:
          return {
            jsonrpc: "2.0",
            id,
            error: {
              code: -32601,
              message: `Method not found: ${method}`,
            },
          };
      }
    } catch (err: any) {
      return {
        jsonrpc: "2.0",
        id,
        result: {
          content: [
            {
              type: "text",
              text: `Error executing tool: ${err.message || String(err)}`,
            },
          ],
          isError: true,
        },
      };
    }
  }

  public async executeTool(name: string, args: any): Promise<string> {
    switch (name) {
      case "lean_goal":
      case "lean_plain_goal": {
        const filePath = args.filePath || args.path || args.file;
        if (!filePath) {
          throw new Error("Missing required argument: 'filePath'");
        }
        const line = Number(args.line ?? 1);
        const col = Number(args.col ?? args.character ?? 1);
        const filterOpts: GoalFilterOptions | undefined =
          (args.filterTypeclasses || args.filterInaccessible || args.onlyTarget)
            ? {
                hideTypeclasses: args.filterTypeclasses ?? false,
                hideInaccessible: args.filterInaccessible ?? false,
                onlyTarget: args.onlyTarget ?? false,
              }
            : undefined;
        return await this.lakeManager.getGoal(filePath, line, col, filterOpts);
      }

      case "lean_filtered_goal": {
        const filePath = args.filePath || args.path || args.file;
        if (!filePath) {
          throw new Error("Missing required argument: 'filePath'");
        }
        const line = Number(args.line ?? 1);
        const col = Number(args.col ?? args.character ?? 1);
        const opts: GoalFilterOptions = {
          hideTypeclasses: args.hideTypeclasses ?? true,
          hideInaccessible: args.hideInaccessible ?? true,
          onlyTarget: args.onlyTarget ?? false,
          maxGoals: Number(args.maxGoals ?? 3),
        };
        return await this.lakeManager.getGoal(filePath, line, col, opts);
      }

      case "lean_term_goal":
      case "lean_plain_term_goal": {
        const filePath = args.filePath || args.path || args.file;
        if (!filePath) {
          throw new Error("Missing required argument: 'filePath'");
        }
        const line = Number(args.line ?? 1);
        const col = Number(args.col ?? args.character ?? 1);
        return await this.lakeManager.getTermGoal(filePath, line, col);
      }

      case "lean_lookup_symbol":
      case "lean_jump_definition": {
        const symbol = args.symbol;
        if (!symbol) {
          throw new Error("Missing required argument: 'symbol'");
        }
        const match = this.ileanIndex.lookupSymbol(symbol);
        if (!match) {
          return `Symbol '${symbol}' not found in .ilean cache. Ensure the Lean project is compiled via 'lake build'.`;
        }
        return [
          `Symbol: ${symbol}`,
          `File: ${match.filePath}`,
          `Position: line ${match.line}, col ${match.col}` + (match.endLine ? ` to line ${match.endLine}, col ${match.endCol}` : ""),
          match.module ? `Module: ${match.module}` : "",
        ].filter(Boolean).join("\n");
      }

      case "lean_module_hierarchy":
      case "lean_module_dag": {
        const moduleName = args.moduleName;
        if (!moduleName) {
          throw new Error("Missing required argument: 'moduleName'");
        }
        const direction = args.direction || "both";
        const isTransitive = Boolean(args.transitive);
        const maxDepth = Number(args.maxDepth ?? 20);

        const lines: string[] = [`Module: ${moduleName}`, `Traversal: ${isTransitive ? "Transitive (Max Depth: " + maxDepth + ")" : "Direct (1-hop)"}`];

        if (direction === "imports" || direction === "both") {
          const direct = this.ileanIndex.getModuleImports(moduleName);
          lines.push(`Direct Imports (${direct.length}):`);
          if (direct.length === 0) {
            lines.push("  (none)");
          } else {
            for (const imp of direct) lines.push(`  - ${imp}`);
          }

          if (isTransitive) {
            const trans = this.ileanIndex.getTransitiveClosure(moduleName, "imports", maxDepth);
            lines.push(`Transitive Closure Imports (${trans.items.length}, Depth reached: ${trans.depth}):`);
            if (trans.items.length === 0) {
              lines.push("  (none)");
            } else {
              for (const imp of trans.items) lines.push(`  - ${imp}`);
            }
            if (trans.hasCycle) {
              lines.push(`  [WARNING: Cycle detected in import DAG: ${trans.cyclePath?.join(" -> ")}]`);
            }
          }
        }

        if (direction === "importedBy" || direction === "both") {
          const directBy = this.ileanIndex.getModuleImportedBy(moduleName);
          lines.push(`Direct Imported By (${directBy.length}):`);
          if (directBy.length === 0) {
            lines.push("  (none)");
          } else {
            for (const by of directBy) lines.push(`  - ${by}`);
          }

          if (isTransitive) {
            const transBy = this.ileanIndex.getTransitiveClosure(moduleName, "importedBy", maxDepth);
            lines.push(`Transitive Closure Dependents (${transBy.items.length}, Depth reached: ${transBy.depth}):`);
            if (transBy.items.length === 0) {
              lines.push("  (none)");
            } else {
              for (const by of transBy.items) lines.push(`  - ${by}`);
            }
            if (transBy.hasCycle) {
              lines.push(`  [WARNING: Cycle detected in dependent DAG: ${transBy.cyclePath?.join(" -> ")}]`);
            }
          }
        }

        return lines.join("\n");
      }

      case "lean_c_ffi_inspect":
      case "lean_c_ffi": {
        const externName = args.externName || args.symbol;
        return LeanSysrootBridge.inspectFFI(this.projectRoot, externName);
      }
      case "lean_run_code": {
        const code = args.code;
        if (!code) throw new Error("Missing required argument: 'code'");
        try {
          const out = execSync("lean --stdin", {
            input: code,
            encoding: "utf-8",
            stdio: ["pipe", "pipe", "pipe"],
            timeout: 15000,
          });
          return out.trim() || "No output";
        } catch (err: any) {
          return `Error: ${err.message || String(err)}\nOutput: ${err.stdout || ""}\nError Output: ${err.stderr || ""}`;
        }
      }

      case "lean_loogle_search": {
        const query = args.query;
        if (!query) throw new Error("Missing required argument: 'query'");
        try {
          const url = `https://loogle.lean-lang.org/json?q=${encodeURIComponent(query)}`;
          const controller = new AbortController();
          const timeoutId = setTimeout(() => controller.abort(), 15000);
          const res = await fetch(url, { signal: controller.signal as any });
          clearTimeout(timeoutId);
          if (!res.ok) throw new Error(`HTTP error ${res.status}`);
          const json = await res.json();
          return JSON.stringify(json, null, 2);
        } catch (err: any) {
          return `Loogle API error: ${err.message || String(err)}`;
        }
      }

      case "lean_local_search": {
        const query = args.query;
        if (!query) throw new Error("Missing required argument: 'query'");
        const limit = Number(args.limit ?? 10);
        const modifiers = ["public", "protected", "private", "noncomputable", "partial", "unsafe", "scoped", "local"];
        const keywords = ["theorem", "lemma", "def", "axiom", "class", "instance", "structure", "inductive", "abbrev", "opaque"];
        
        const declLead = "^\\s*(?:@\\[[^\\]]*\\]\\s*)*(?:(?:" + modifiers.join("|") + ")\\s+)*";
        const keywordAlt = keywords.join("|");
        const escapedQuery = query.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
        const pattern = declLead + "(?:" + keywordAlt + ")\\s+(?:[A-Za-z0-9_'.]+\\.)*" + escapedQuery + "[A-Za-z0-9_'.]*(?:\\s|:)";
        
        try {
          const { execFileSync } = await import("node:child_process");
          const out = execFileSync("rg", [
            "--json", "--no-ignore", "--smart-case", "--hidden", "--color", "never", "--no-messages",
            "-g", "*.lean", "-g", "!.git/**", "-g", "!.lake/build/**", "-e", pattern
          ], {
            cwd: this.projectRoot,
            encoding: "utf-8",
            stdio: ["ignore", "pipe", "ignore"],
          });
          const results: string[] = [];
          for (const line of out.split("\n")) {
            if (!line) continue;
            try {
              const event = JSON.parse(line);
              if (event.type === "match") {
                const text = event.data.lines.text;
                const match = text.match(new RegExp(declLead + "(" + keywordAlt + ")\\s+([A-Za-z0-9_']+(?:\\.[A-Za-z0-9_']+)*)"));
                if (match) {
                  results.push(`Name: ${match[2]}\nKind: ${match[1]}\nFile: ${event.data.path.text}\n`);
                  if (results.length >= limit) break;
                }
              }
            } catch { }
          }
          if (results.length === 0) return "No results found.";
          return results.join("\n");
        } catch (err: any) {
          if (err.status === 1 && (!err.stdout || !err.stdout.trim())) return "No results found.";
          if (err.stdout && err.stdout.trim().length > 0) {
            const results: string[] = [];
            for (const line of err.stdout.split("\n")) {
              if (!line) continue;
              try {
                const event = JSON.parse(line);
                if (event.type === "match") {
                  const text = event.data.lines.text;
                  const match = text.match(new RegExp(declLead + "(" + keywordAlt + ")\\s+([A-Za-z0-9_']+(?:\\.[A-Za-z0-9_']+)*)"));
                  if (match) {
                    results.push(`Name: ${match[2]}\nKind: ${match[1]}\nFile: ${event.data.path.text}\n`);
                    if (results.length >= limit) break;
                  }
                }
              } catch { }
            }
            if (results.length > 0) return results.join("\n");
          }
          return `Search failed: ${err.message || String(err)}`;
        }
      }

      case "lean_search": {
        const query = args.query;
        if (!query) throw new Error("Missing required argument: 'query'");
        const num_results = Number(args.num_results ?? 5);
        try {
          const payload = JSON.stringify({ num_results: String(num_results), query: [query] });
          const controller = new AbortController();
          const timeoutId = setTimeout(() => controller.abort(), 15000);
          const res = await fetch("https://leansearch.net/search", {
            method: "POST",
            headers: { "Content-Type": "application/json", "User-Agent": "lean-lsp-mcp/0.1" },
            body: payload,
            signal: controller.signal as any,
          });
          clearTimeout(timeoutId);
          if (!res.ok) throw new Error(`HTTP error ${res.status}`);
          const json: any = await res.json();
          if (!json || !json[0]) return "No results found.";
          const results: string[] = [];
          for (const item of json[0].slice(0, num_results)) {
            const r = item.result;
            const name = (r.name || []).join(".");
            const module_name = (r.module_name || []).join(".");
            results.push(`Name: ${name}\nModule: ${module_name}\nKind: ${r.kind || ""}\nType: ${r.type || ""}\n`);
          }
          if (results.length === 0) return "No results found.";
          return results.join("\n");
        } catch (err: any) {
          return `LeanSearch API error: ${err.message || String(err)}`;
        }
      }

      default:
        throw new Error(`Unknown tool: '${name}'`);
    }
  }

  public startStdio(): void {
    process.stdin.setEncoding("utf-8");
    process.stdin.on("data", (chunk: string) => {
      this.buffer += chunk;
      this.processBuffer();
    });
    process.stdin.on("end", () => {
      this.lakeManager.dispose();
      process.exit(0);
    });
  }

  private async processBuffer(): Promise<void> {
    while (true) {
      if (this.buffer.startsWith("Content-Length:")) {
        const headerEnd = this.buffer.indexOf("\r\n\r\n");
        if (headerEnd === -1) break;
        const header = this.buffer.slice(0, headerEnd);
        const match = header.match(/Content-Length:\s*(\d+)/i);
        if (!match) {
          this.buffer = this.buffer.slice(headerEnd + 4);
          continue;
        }
        const len = parseInt(match[1], 10);
        if (this.buffer.length < headerEnd + 4 + len) break;
        const body = this.buffer.slice(headerEnd + 4, headerEnd + 4 + len);
        this.buffer = this.buffer.slice(headerEnd + 4 + len);
        await this.dispatchRaw(body, true);
      } else {
        const newlineIdx = this.buffer.indexOf("\n");
        if (newlineIdx === -1) break;
        const line = this.buffer.slice(0, newlineIdx).trim();
        this.buffer = this.buffer.slice(newlineIdx + 1);
        if (line.length > 0) {
          await this.dispatchRaw(line, false);
        }
      }
    }
  }

  private async dispatchRaw(rawJson: string, useContentLength: boolean): Promise<void> {
    let req: any;
    try {
      req = JSON.parse(rawJson);
    } catch (err: any) {
      this.sendError(null, -32700, "Parse error: " + err.message, useContentLength);
      return;
    }
    const res = await this.handleMessage(req);
    if (res !== null) {
      this.sendResponse(res, useContentLength);
    }
  }

  private sendResponse(res: McpResponse, useContentLength: boolean): void {
    const json = JSON.stringify(res);
    if (useContentLength) {
      const header = `Content-Length: ${Buffer.byteLength(json, "utf-8")}\r\n\r\n`;
      process.stdout.write(header + json);
    } else {
      process.stdout.write(json + "\n");
    }
  }

  private sendError(id: any, code: number, message: string, useContentLength: boolean): void {
    const errRes: McpResponse = {
      jsonrpc: "2.0",
      id: id ?? null,
      error: { code, message },
    };
    this.sendResponse(errRes, useContentLength);
  }

  public dispose(): void {
    this.lakeManager.dispose();
  }
}

export function main(): void {
  const projectRoot = process.cwd();
  const server = new McpServer(projectRoot);
  process.stderr.write(`[lean-lsp-mcp] Initialized for project ${projectRoot}\n`);
  server.startStdio();
}

function checkIsMain(): boolean {
  if (!process.argv[1]) return false;
  try {
    const argvPath = fs.realpathSync(path.resolve(process.argv[1]));
    const modulePath = fs.realpathSync(fileURLToPath(import.meta.url));
    return argvPath === modulePath;
  } catch {
    return path.resolve(process.argv[1]) === fileURLToPath(import.meta.url);
  }
}

if (checkIsMain()) {
  main();
}
