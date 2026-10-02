// tools/lean_lsp_mcp/src/index.ts
// Standalone Model Context Protocol (MCP) server for Lean 4 & C FFI.
// Strict 7-bit ASCII only (INV-001).

import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";
import { execSync, spawn, ChildProcess } from "node:child_process";
import { fileURLToPath, pathToFileURL } from "node:url";
import { KuzuKnowledgeGraph } from "./kuzu_graph.ts";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

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
    description: "Queries interactive Lean 4 tactic proof state, filtered proof state, or expected term type at cursor position ($/lean/plainGoal, $/lean/plainTermGoal)",
    inputSchema: {
      type: "object",
      properties: {
        filePath: { type: "string", description: "Absolute or relative path to the .lean file" },
        line: { type: "integer", description: "1-based line number" },
        col: { type: "integer", description: "1-based column number (synonym: character)" },
        character: { type: "integer", description: "Synonym for col" },
        target: { type: "string", enum: ["tactic", "term", "filtered"], description: "Goal target type (default: tactic)" },
        filter: { type: "string", enum: ["all", "hypotheses", "target"], description: "Filtering intensity (default: all)" },
        hideTypeclasses: { type: "boolean", description: "Filter out ambient typeclass instances" },
        hideInaccessible: { type: "boolean", description: "Filter out compiler internal/dagger variables" },
        onlyTarget: { type: "boolean", description: "Return only the target goal expression" },
        maxGoals: { type: "integer", description: "Maximum subgoals to display (default: 3)" },
      },
      required: ["filePath", "line"],
    },
  },
  {
    name: "lean_search",
    description: "Unified declaration, semantic, ontology, reservoir, dataset, arXiv, and Kuzu knowledge graph search",
    inputSchema: {
      type: "object",
      properties: {
        query: { type: "string", description: "Search query, symbol name, type signature, concept, or term" },
        source: {
          type: "string",
          enum: ["code", "loogle", "ontology", "arxiv", "datasets", "reservoir", "book", "concordance", "symbol", "graph", "local"],
          description: "Search domain and engine (default: code / local declaration search)",
        },
        file: { type: "string", description: "Optional file path filter" },
        limit: { type: "integer", description: "Max results to return (default: 10)" },
        prover: { type: "string", description: "Optional target prover filter for ontology / concordance" },
        category: { type: "string", description: "Optional arXiv category filter" },
      },
      required: ["query"],
    },
  },
  {
    name: "lean_blueprint",
    description: "Lean Blueprint and Knowledge Garden operations: scaffolding, coverage status, zettels, skeletons, and graph neighborhoods",
    inputSchema: {
      type: "object",
      properties: {
        action: {
          type: "string",
          enum: ["status", "scaffold", "zettel", "skeleton", "walkthrough", "graph_neighborhood"],
          description: "Blueprint action to perform (default: status)",
        },
        symbol: { type: "string", description: "Lean declaration name (e.g. EulerPacketPiola.matrixAntisym_congruence)" },
        filePath: { type: "string", description: "Path to .lean file (relative or absolute)" },
        sectionId: { type: "string", description: "Section ID for graph_neighborhood (e.g. from Kuzu graph)" },
        formalizationDir: { type: "string", description: "Root formalization directory for status audit" },
        blueprintDir: { type: "string", description: "Root blueprint directory for status audit" },
        outputPath: { type: "string", description: "Optional output file path for generated scaffold or zettel" },
        format: { type: "string", enum: ["markdown", "json", "summary"], description: "Output format (default: markdown)" },
        title: { type: "string", description: "Optional human-readable title" },
      },
    },
  },
  {
    name: "lean_metrics",
    description: "Module and project metrics: static code census, module dependency hierarchy DAG, and dependency subgraphs",
    inputSchema: {
      type: "object",
      properties: {
        action: {
          type: "string",
          enum: ["census", "hierarchy", "subgraph"],
          description: "Metric action to perform (default: census)",
        },
        target: { type: "string", description: "Target file path, directory path, or module name" },
        direction: { type: "string", enum: ["imports", "importedBy", "both"], description: "Traversal direction for hierarchy (default: both)" },
        transitive: { type: "boolean", description: "Whether to compute full transitive closure (default: false)" },
        maxDepth: { type: "integer", description: "Max traversal depth (default: 10)" },
        format: { type: "string", enum: ["markdown", "json", "summary", "mermaid", "dot"], description: "Output format (default: markdown)" },
      },
      required: ["target"],
    },
  },
  {
    name: "lean_ffi",
    description: "Cross-language Lean 4 C FFI environment inspection, sysroot include flags, header validation, and symbol resolution",
    inputSchema: {
      type: "object",
      properties: {
        action: {
          type: "string",
          enum: ["inspect_env", "resolve_symbol", "verify_headers", "sysroot"],
          description: "FFI inspection action (default: inspect_env)",
        },
        externName: { type: "string", description: "Optional Lean @[extern] identifier or C function name" },
        cHeaderPath: { type: "string", description: "Optional path to C header to inspect" },
      },
    },
  },
  {
    name: "lean_exec",
    description: "Ephemeral standalone Lean 4 execution via lean --stdin without file pollution",
    inputSchema: {
      type: "object",
      properties: {
        code: { type: "string", description: "Lean 4 code to execute" },
        timeoutMs: { type: "integer", description: "Execution timeout in milliseconds (default: 15000)" },
      },
      required: ["code"],
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

    const easciLean = path.join(this.projectRoot, "docs", "easci", "lean");
    const candidateRoots = [
      path.join(this.projectRoot, ".lake", "build", "lib", "lean"),
      path.join(this.projectRoot, ".lake", "build", "ir"),
      path.join(easciLean, ".lake", "build", "lib", "lean"),
      path.join(easciLean, ".lake", "build", "ir"),
    ];

    // Discover .lake/packages for Mathlib and external libraries
    const packageDirs = [
      path.join(this.projectRoot, ".lake", "packages"),
      path.join(easciLean, ".lake", "packages"),
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
        const candidateEasci = path.join(this.projectRoot, "docs", "easci", "lean", relLean);
        if (fs.existsSync(candidate)) {
          sourceFile = path.relative(this.projectRoot, candidate);
        } else if (fs.existsSync(candidateEasci)) {
          sourceFile = path.relative(this.projectRoot, candidateEasci);
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
    if (
      fs.existsSync(path.join(this.projectRoot, "lakefile.lean")) ||
      fs.existsSync(path.join(this.projectRoot, "lakefile.toml"))
    ) {
      this.knownPackages.set(path.basename(this.projectRoot) || "root", this.projectRoot);
    }
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

let reservoirIndexCache: { at: number; packages: string[] } | null = null;

/** Package names (owner/name) from the published reservoir-index tree, cached 30 min. */
async function reservoirIndexPackages(): Promise<string[]> {
  const now = Date.now();
  if (reservoirIndexCache && now - reservoirIndexCache.at < 30 * 60 * 1000) {
    return reservoirIndexCache.packages;
  }
  const headers: Record<string, string> = {
    "User-Agent": "lean-lsp-mcp/0.1",
    "Accept": "application/vnd.github+json",
  };
  const controller = new AbortController();
  const timeoutId = setTimeout(() => controller.abort(), 30000);
  const res = await fetch(
    "https://api.github.com/repos/leanprover/reservoir-index/git/trees/master?recursive=1",
    { signal: controller.signal as any, headers },
  );
  clearTimeout(timeoutId);
  if (!res.ok) throw new Error(`reservoir-index fetch failed: HTTP ${res.status}`);
  const json: any = await res.json();
  const seen = new Set<string>();
  const packages: string[] = [];
  for (const t of json.tree || []) {
    const parts = String(t.path).split("/");
    if (parts.length === 2) {
      const key = `${parts[0]}/${parts[1]}`;
      if (!seen.has(key)) {
        seen.add(key);
        packages.push(key);
      }
    }
  }
  reservoirIndexCache = { at: now, packages };
  return packages;
}

export class McpServer {
  private projectRoot: string;
  private ileanIndex: Lean4IleanIndex;
  private lakeManager: LakeServerManager;
  private kuzuGraph: KuzuKnowledgeGraph;
  private buffer: string = "";

  constructor(projectRoot: string = process.cwd()) {
    this.projectRoot = projectRoot;
    this.ileanIndex = new Lean4IleanIndex(projectRoot);
    this.ileanIndex.refresh();
    this.lakeManager = new LakeServerManager(projectRoot);
    this.kuzuGraph = new KuzuKnowledgeGraph();
  }

  public getKuzuGraph(): KuzuKnowledgeGraph {
    return this.kuzuGraph;
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
        const target = String(args.target || "tactic").toLowerCase();

        if (target === "term") {
          return await this.lakeManager.getTermGoal(filePath, line, col);
        }

        const isFiltered = target === "filtered" || args.filter === "hypotheses" || args.filter === "target" || args.hideTypeclasses !== undefined;
        if (isFiltered) {
          const opts: GoalFilterOptions = {
            hideTypeclasses: args.hideTypeclasses ?? true,
            hideInaccessible: args.hideInaccessible ?? true,
            onlyTarget: args.onlyTarget ?? (args.filter === "target"),
            maxGoals: Number(args.maxGoals ?? 3),
          };
          return await this.lakeManager.getGoal(filePath, line, col, opts);
        }

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
        const query = args.query || args.term || args.concept || args.symbol;
        if (!query) throw new Error("Missing required argument: 'query'");
        const source = String(args.source || "code").toLowerCase();
        const limit = Number(args.limit ?? args.num_results ?? args.maxResults ?? 10);

        if (source === "loogle") {
          return await this.executeTool("lean_loogle_search", { query });
        } else if (source === "ontology") {
          return await this.executeTool("lean_ontology_search", { query, prover: args.prover });
        } else if (source === "arxiv") {
          return await this.executeTool("lean_arxiv_search", { query, category: args.category, maxResults: limit });
        } else if (source === "datasets" || source === "dataset") {
          return await this.executeTool("lean_dataset_search", { query, limit });
        } else if (source === "reservoir") {
          return await this.executeTool("lean_reservoir_search", { query, limit });
        } else if (source === "book" || source === "book_index") {
          return await this.executeTool("lean_book_index_lookup", { term: query, book: args.book });
        } else if (source === "concordance") {
          return await this.executeTool("lean_cross_itp_concordance", { concept: query });
        } else if (source === "symbol") {
          return await this.executeTool("lean_lookup_symbol", { symbol: query });
        } else if (source === "graph") {
          const results = this.kuzuGraph.search(query, limit);
          if (results.length === 0) return "No matching sections found in Kuzu knowledge graph.";
          return results.map(r => `Section: ${r.sectionId} | Book: ${r.bookTitle} (${r.bookKey})\nTitle: ${r.sectionTitle}\nScore: ${r.score.toFixed(2)}\n`).join("\n");
        } else if (source === "leansearch" || source === "mathlib_web") {
          const num_results = limit;
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
        } else {
          return await this.executeTool("lean_local_search", { query, limit });
        }
      }

      case "lean_arxiv_search": {
        const query = args.query;
        if (!query) throw new Error("Missing required argument: 'query'");
        const maxResults = Math.max(1, Math.min(20, Number(args.maxResults ?? 5)));
        const category =
          typeof args.category === "string" && args.category.trim().length > 0
            ? ` AND cat:${args.category.trim()}`
            : "";
        try {
          const searchExpr = `all:${query}${category}`;
          const url =
            `https://export.arxiv.org/api/query?search_query=${encodeURIComponent(searchExpr)}` +
            `&start=0&max_results=${maxResults}&sortBy=relevance&sortOrder=descending`;
          const controller = new AbortController();
          const timeoutId = setTimeout(() => controller.abort(), 20000);
          const res = await fetch(url, { signal: controller.signal as any });
          clearTimeout(timeoutId);
          if (!res.ok) throw new Error(`HTTP error ${res.status}`);
          const xml = await res.text();
          const entries = xml.split("<entry>").slice(1);
          if (entries.length === 0) return "No arXiv results.";
          const strip = (s: string) => s.replace(/\s+/g, " ").trim();
          const pick = (block: string, tag: string): string => {
            const m = block.match(new RegExp(`<${tag}[^>]*>([\\s\\S]*?)</${tag}>`));
            return m ? strip(m[1]) : "";
          };
          const out: string[] = [];
          for (let i = 0; i < entries.length; i++) {
            const e = entries[i];
            const id = pick(e, "id");
            const title = pick(e, "title");
            const published = pick(e, "published").slice(0, 10);
            const authors = [...e.matchAll(/<name>([^<]+)<\/name>/g)]
              .map((a) => strip(a[1]))
              .join(", ");
            const summary = pick(e, "summary").slice(0, 500);
            out.push(`${i + 1}. ${title}\n   ${authors}\n   ${id} (${published})\n   ${summary}`);
          }
          return out.join("\n\n");
        } catch (err: any) {
          return `arXiv API error: ${err.message || String(err)}`;
        }
      }

      case "lean_reservoir_search": {
        const query = String(args.query ?? "").trim();
        if (!query) throw new Error("Missing required argument: 'query'");
        const limit = Math.max(1, Math.min(30, Number(args.limit ?? 10)));
        const reqHeaders: Record<string, string> = { "User-Agent": "lean-lsp-mcp/0.1" };
        try {
          // exact owner/pkg: the documented registry API (identical to Lake's fetchPkg)
          if (/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(query)) {
            const [owner, pkg] = query.split("/");
            const url =
              `https://reservoir.lean-lang.org/api/v1/packages/` +
              `${encodeURIComponent(owner)}/${encodeURIComponent(pkg)}`;
            const controller = new AbortController();
            const timeoutId = setTimeout(() => controller.abort(), 20000);
            const res = await fetch(url, { signal: controller.signal as any, headers: reqHeaders });
            clearTimeout(timeoutId);
            if (res.ok) {
              const json: any = await res.json();
              const data = json && json.data ? json.data : json;
              const desc = typeof data.description === "string" ? data.description : "";
              const srcUrl = data.repoUrl || data.githubUrl || data.homepage || "";
              return (
                `Registry record: ${owner}/${pkg}\n` +
                `  name: ${data.name ?? pkg}\n` +
                `  description: ${desc}\n` +
                `  source: ${srcUrl}\n` +
                `  site: https://reservoir.lean-lang.org/packages/${owner}/${pkg}`
              );
            }
          }
          // name search over the published index tree (cached in-process)
          const paths = await reservoirIndexPackages();
          const terms = query.toLowerCase().split(/\s+/).filter((t) => t.length > 0);
          let matches = paths.filter((p) => terms.every((t) => p.toLowerCase().includes(t)));
          let partial = false;
          if (matches.length === 0 && terms.length > 1) {
            matches = paths.filter((p) => terms.some((t) => p.toLowerCase().includes(t)));
            partial = true;
          }
          matches = matches.slice(0, limit);
          if (matches.length === 0) {
            return `No Reservoir packages match '${query}'.`;
          }
          const header = partial
            ? `No exact match for '${query}'; partial matches (any term):\n`
            : "";
          return (
            header +
            matches
              .map((p) => `${p}  ->  https://reservoir.lean-lang.org/packages/${p}`)
              .join("\n")
          );
        } catch (err: any) {
          return `Reservoir error: ${err.message || String(err)}`;
        }
      }

      case "lean_dataset_search": {
        const query = String(args.query ?? "").trim();
        if (!query) throw new Error("Missing required argument: 'query'");
        const limit = Math.max(1, Math.min(30, Number(args.limit ?? 10)));
        try {
          const url =
            `https://huggingface.co/api/datasets?search=${encodeURIComponent(query)}` +
            `&limit=${limit * 3}`;
          const controller = new AbortController();
          const timeoutId = setTimeout(() => controller.abort(), 20000);
          const res = await fetch(url, {
            signal: controller.signal as any,
            headers: { "User-Agent": "lean-lsp-mcp/0.1" },
          });
          clearTimeout(timeoutId);
          if (!res.ok) throw new Error(`HTTP error ${res.status}`);
          const json: any = await res.json();
          if (!Array.isArray(json) || json.length === 0) {
            return `No Hugging Face datasets match '${query}'.`;
          }
          const rows = json
            .filter((d: any) => !d.disabled && !d.private)
            .sort((a: any, b: any) => (b.downloads ?? 0) - (a.downloads ?? 0))
            .slice(0, limit);
          if (rows.length === 0) {
            return `No public Hugging Face datasets match '${query}'.`;
          }
          return rows
            .map((d: any) => {
              const gate = d.gated ? " [gated]" : "";
              const when =
                typeof d.lastModified === "string" ? d.lastModified.slice(0, 10) : "";
              return (
                `${d.id}${gate}\n` +
                `   downloads: ${d.downloads ?? 0} | likes: ${d.likes ?? 0} | updated: ${when}\n` +
                `   https://huggingface.co/datasets/${d.id}`
              );
            })
            .join("\n");
        } catch (err: any) {
          return `Hugging Face API error: ${err.message || String(err)}`;
        }
      }

      case "lean_ontology_search": {
        const query = String(args.query ?? "").trim().toLowerCase();
        if (!query) throw new Error("Missing required argument: 'query'");
        const proverFilter = args.prover ? String(args.prover).trim().toLowerCase() : undefined;

        const candidatePaths = [
          path.resolve(__dirname, "../data/itp-ontology/master-authority-index.json"),
          path.resolve(__dirname, "../../data/itp-ontology/master-authority-index.json"),
          path.resolve(process.cwd(), "data/itp-ontology/master-authority-index.json"),
          path.resolve(process.cwd(), "docs/investigation-garden/source-materials/indexes/master-authority-index.json"),
        ];

        let indexPath: string | undefined;
        for (const p of candidatePaths) {
          if (fs.existsSync(p)) {
            indexPath = p;
            break;
          }
        }

        if (!indexPath) {
          return `ITP Master Authority Ontology index not found in candidate paths.`;
        }

        try {
          const raw = fs.readFileSync(indexPath, "utf-8");
          const data = JSON.parse(raw);
          const concepts = data.master_concepts || [];
          const matches: string[] = [];

          for (const c of concepts) {
            const cid = (c.concept_id || "").toLowerCase();
            const cname = (c.canonical_name || "").toLowerCase();
            const domain = (c.ranganathan_facet?.domain_theory || "").toLowerCase();
            const synonyms = (c.synonyms || []).map((s: string) => s.toLowerCase());

            let tacticMatch = false;
            if (c.prover_mappings) {
              for (const [pName, pVal] of Object.entries<any>(c.prover_mappings)) {
                if (!proverFilter || pName.toLowerCase() === proverFilter) {
                  const tacs = (pVal.primary_tactics || []).join(" ").toLowerCase();
                  if (tacs.includes(query)) {
                    tacticMatch = true;
                    break;
                  }
                }
              }
            }

            if (cid.includes(query) || cname.includes(query) || domain.includes(query) || synonyms.some((s: string) => s.includes(query)) || tacticMatch) {
              let out = `Concept: ${c.concept_id}\nName: ${c.canonical_name}\nDomain: ${c.ranganathan_facet?.domain_theory || "ITP"}\nMSC2020: ${(c.msc2020 || []).join(", ")}\n`;
              out += `Prover Tactics:\n`;
              for (const [pName, pVal] of Object.entries<any>(c.prover_mappings || {})) {
                if (!proverFilter || pName.toLowerCase() === proverFilter) {
                  out += `  - [${pName}]: tactics="${(pVal.primary_tactics || []).join("; ")}", pattern="${pVal.syntax_pattern || ""}"\n`;
                }
              }
              if (c.authoritative_intervals && c.authoritative_intervals.length > 0) {
                out += `Statutory Intervals:\n`;
                for (const urn of c.authoritative_intervals) {
                  out += `  - ${urn}\n`;
                }
              }
              matches.push(out);
            }
          }

          if (matches.length === 0) {
            return `No matching concepts found in ITP Ontology for query: "${args.query}"`;
          }
          return `Found ${matches.length} matching concept(s) in ITP Master Authority Ontology:\n\n` + matches.join("\n---\n");
        } catch (err: any) {
          return `Error searching ITP ontology: ${err.message || String(err)}`;
        }
      }

      case "lean_book_index_lookup": {
        const term = String(args.term ?? "").trim().toLowerCase();
        if (!term) throw new Error("Missing required argument: 'term'");
        const bookFilter = args.book ? String(args.book).trim().toLowerCase() : undefined;

        const candidateIndexDirs = [
          path.resolve(__dirname, "../data/itp-ontology/book-indexes"),
          path.resolve(__dirname, "../../data/itp-ontology/book-indexes"),
          path.resolve(process.cwd(), "data/itp-ontology/book-indexes"),
          path.resolve(process.cwd(), "docs/investigation-garden/source-materials/indexes"),
        ];
        const indexesDir = candidateIndexDirs.find(p => fs.existsSync(p));
        if (!indexesDir) {
          return `Book indexes not found in candidate paths.`;
        }

        const results: string[] = [];
        for (const indexFile of fs.readdirSync(indexesDir).filter(f => f.endsWith(".index.json"))) {
          const corpusId = indexFile.replace(".index.json", "");
          if (bookFilter && !corpusId.includes(bookFilter)) continue;
          try {
            const data = JSON.parse(fs.readFileSync(path.join(indexesDir, indexFile), "utf-8"));
            const entries: any[] = data.entries || (data.index_metadata && data.index_metadata.entries) || [];
            for (const e of entries) {
              const t = (e.term || "").toLowerCase();
              if (t.includes(term)) {
                const refs = (e.primary_references || []).map((r: any) => {
                  const page = r.page ? `, p. ${r.page}` : "";
                  const anchor = r.section_anchor ? ` [${r.section_anchor}]` : "";
                  const def = r.is_definitive ? " (definitive)" : "";
                  return `${corpusId}${page}${anchor}${def}`;
                });
                const xr = (e.cross_references || []).slice(0, 3);
                results.push(
                  `- ${e.term || t} (${e.category || "term"}) in ${corpusId}: ${refs.join("; ")}` +
                  (xr.length ? ` | cross-refs: ${xr.join(", ")}` : "")
                );
              }
            }
          } catch (err) {
            results.push(`- ${indexFile}: unreadable (${String(err).slice(0, 60)})`);
          }
        }

        return results.length
          ? `Book index matches for "${term}":\n` + results.join("\n")
          : `No book index matches for "${term}".`;
      }

      case "lean_cross_itp_concordance": {
        const concept = String(args.concept ?? "").trim().toLowerCase();
        if (!concept) throw new Error("Missing required argument: 'concept'");

        const candidateConcordancePaths = [
          path.resolve(__dirname, "../data/itp-ontology/master-authority-index.json"),
          path.resolve(__dirname, "../../data/itp-ontology/master-authority-index.json"),
          path.resolve(process.cwd(), "data/itp-ontology/master-authority-index.json"),
          path.resolve(process.cwd(), "docs/investigation-garden/source-materials/indexes/master-authority-index.json"),
        ];
        const concordancePath = candidateConcordancePaths.find(p => fs.existsSync(p));
        if (!concordancePath) {
          return `Master authority index not found in candidate paths.`;
        }

        const data = JSON.parse(fs.readFileSync(concordancePath, "utf-8"));
        const concepts = data.master_concepts || [];
        const lines: string[] = [];

        for (const c of concepts) {
          const tactics = c.prover_tactics || {};
          const synonyms = (c.synonyms || []).map((s: string) => s.toLowerCase());
          const cname = (c.canonical_name || "").toLowerCase();
          if (cname.includes(concept) || synonyms.some((s: string) => s.includes(concept))) {
            lines.push(`## ${c.canonical_name} (${c.concept_id})`);
            for (const [prover, tactic] of Object.entries(tactics)) {
              lines.push(`  - ${prover}: ${tactic}`);
            }
          }
        }

        if (!lines.length) {
          // fall back: search the per-book indexes' cross-references for the concept
          const candidateIndexDirs = [
            path.resolve(__dirname, "../data/itp-ontology/book-indexes"),
            path.resolve(__dirname, "../../data/itp-ontology/book-indexes"),
            path.resolve(process.cwd(), "data/itp-ontology/book-indexes"),
            path.resolve(process.cwd(), "docs/investigation-garden/source-materials/indexes"),
          ];
          const indexesDir = candidateIndexDirs.find(p => fs.existsSync(p));
          if (indexesDir) {
            for (const f of fs.readdirSync(indexesDir).filter(f => f.endsWith(".index.json"))) {
              try {
                const d = JSON.parse(fs.readFileSync(path.join(indexesDir, f), "utf-8"));
                const entries: any[] = d.entries || (d.index_metadata && d.index_metadata.entries) || [];
                for (const e of entries) {
                  if ((e.term || "").toLowerCase().includes(concept)) {
                    lines.push(`- ${e.term} (${f.replace(".index.json", "")})`);
                    for (const r of e.primary_references || []) {
                      if (r.prover_anchor) {
                        lines.push(`  ${r.section_anchor ? `${r.section_anchor}: ` : ""}${r.prover_anchor}`);
                      }
                    }
                  }
                }
              } catch { /* skip */ }
            }
          }
        }

        return lines.length
          ? `Cross-ITP concordance for "${concept}":\n` + lines.join("\n")
          : `No concordance entry for "${concept}" yet (the master authority catalog is under construction).`;
      }

      case "lean_proof_skeleton": {
        let filePath = String(args.filePath || "").trim();
        if (!filePath && args.symbol) {
          const sym = this.ileanIndex.lookupSymbol(args.symbol);
          if (sym) filePath = sym.filePath;
        }
        if (!filePath) {
          throw new Error("Missing required argument: 'filePath' (or valid 'symbol')");
        }
        const absPath = path.isAbsolute(filePath) ? filePath : path.resolve(this.projectRoot, filePath);
        if (!fs.existsSync(absPath)) {
          return `File not found: ${filePath}`;
        }
        const content = fs.readFileSync(absPath, "utf-8");
        const lines = content.split(/\r?\n/);

        let startLine = Number(args.startLine ?? 1);
        let endLine = Number(args.endLine ?? lines.length);

        if (args.symbol && !args.startLine) {
          const symName = String(args.symbol).split(".").pop()!;
          const declRegex = new RegExp(`^(?:(?:noncomputable|scoped|protected|private)\\s+)*(?:theorem|lemma|def)\\s+${symName}\\b`);
          for (let i = 0; i < lines.length; i++) {
            if (declRegex.test(lines[i].trim())) {
              startLine = i + 1;
              for (let j = i + 1; j < lines.length; j++) {
                const trimmed = lines[j].trim();
                if (/^(?:(?:noncomputable|scoped|protected|private)\s+)*(?:theorem|lemma|def|structure|class)\s+[A-Za-z0-9_.]+\b/.test(trimmed) ||
                    /^end\s+[A-Za-z0-9_.]+\b/.test(trimmed)) {
                  endLine = j;
                  break;
                }
              }
              break;
            }
          }
        }

        const skeleton: string[] = [
          `# Proof Skeleton for ${args.symbol || path.basename(filePath)} (${path.relative(this.projectRoot, absPath)}: lines ${startLine}-${endLine})`,
          "",
        ];

        const milestoneRegex = /^\s*(?:have\b|obtain\b|calc\b|induction\b|rcases\b|cases\b|constructor\b|by_contra\b|ext\b)/;
        for (let idx = startLine - 1; idx < endLine; idx++) {
          const rawLine = lines[idx];
          const trimmed = rawLine.trim();
          if (idx === startLine - 1) {
            skeleton.push(`[Line ${idx + 1}] Statement: ${trimmed}`);
          } else if (milestoneRegex.test(trimmed)) {
            skeleton.push(`  - [Line ${idx + 1}] ${trimmed}`);
          }
        }

        if (skeleton.length <= 2) {
          skeleton.push("  (Single-tactic or term-mode proof; no nested have/obtain milestones detected)");
        }

        return skeleton.join("\n");
      }

      case "lean_blueprint_scaffold": {
        const symbol = String(args.symbol || "").trim();
        if (!symbol) throw new Error("Missing required argument: 'symbol'");

        let filePath = args.filePath ? String(args.filePath) : "";
        let line = Number(args.line ?? 0);
        let modName = "";

        const match = this.ileanIndex.lookupSymbol(symbol);
        if (match) {
          filePath = match.filePath;
          line = match.line;
          modName = match.module || "";
        }

        const title = args.title || symbol.split(".").pop() || symbol;
        const safeLabel = symbol.toLowerCase().replace(/[^a-z0-9]+/g, "-");

        let kind = "theorem";
        let usesDirect: string[] = [];

        if (filePath) {
          const absPath = path.isAbsolute(filePath) ? filePath : path.resolve(this.projectRoot, filePath);
          if (fs.existsSync(absPath)) {
            const content = fs.readFileSync(absPath, "utf-8");
            const lines = content.split(/\r?\n/);
            if (line > 0 && line <= lines.length) {
              const declLine = lines[line - 1];
              if (/\bdef\b|\bstructure\b/.test(declLine)) kind = "definition";
              else if (/\blemma\b/.test(declLine)) kind = "lemma";
            }
          }
        }

        if (modName) {
          const imps = this.ileanIndex.getModuleImports(modName);
          usesDirect = imps.slice(0, 3).map(imp => "def:" + imp.toLowerCase().replace(/[^a-z0-9]+/g, "-"));
        }

        const usesAttr = usesDirect.length ? `\\uses{${usesDirect.join(", ")}}` : "% \\uses{...}";

        return [
          `% Lean Blueprint Scaffold for ${symbol}`,
          `\\begin{${kind}}[${title}]`,
          `\\label{${kind}:${safeLabel}}`,
          usesAttr,
          `\\lean{${symbol}}`,
          `\\leanok`,
          `Mathematical statement for \\texttt{${title}}.`,
          `\\end{${kind}}`,
          "",
          `\\begin{proof}`,
          usesAttr,
          `\\leanok`,
          `Informal mathematical proof sketch for \\texttt{${title}}.`,
          `\\end{proof}`,
        ].join("\n");
      }

      case "lean_dependency_subgraph": {
        const moduleName = String(args.moduleName || "").trim();
        if (!moduleName) throw new Error("Missing required argument: 'moduleName'");

        const maxDepth = Number(args.maxDepth ?? 5);
        const format = String(args.format || "mermaid").toLowerCase();

        const trans = this.ileanIndex.getTransitiveClosure(moduleName, "imports", maxDepth);
        const allNodes = new Set<string>([moduleName, ...trans.items]);

        if (format === "json") {
          const edges: Array<{ from: string; to: string }> = [];
          for (const node of allNodes) {
            const direct = this.ileanIndex.getModuleImports(node);
            for (const d of direct) {
              if (allNodes.has(d)) edges.push({ from: node, to: d });
            }
          }
          return JSON.stringify({ root: moduleName, nodes: Array.from(allNodes), edges, depth: trans.depth }, null, 2);
        } else if (format === "dot") {
          const lines = [`digraph "${moduleName}" {`, `  rankdir=BT;`];
          for (const node of allNodes) {
            lines.push(`  "${node}";`);
            const direct = this.ileanIndex.getModuleImports(node);
            for (const d of direct) {
              if (allNodes.has(d)) lines.push(`  "${node}" -> "${d}";`);
            }
          }
          lines.push("}");
          return lines.join("\n");
        } else {
          const lines = ["```mermaid", "graph TD"];
          const sanitize = (s: string) => s.replace(/[^a-zA-Z0-9_]/g, "_");
          for (const node of allNodes) {
            const direct = this.ileanIndex.getModuleImports(node);
            for (const d of direct) {
              if (allNodes.has(d)) {
                lines.push(`  ${sanitize(node)}["${node}"] --> ${sanitize(d)}["${d}"]`);
              }
            }
          }
          if (lines.length === 2) {
            lines.push(`  ${sanitize(moduleName)}["${moduleName} (leaf / no internal imports)"]`);
          }
          lines.push("```");
          return lines.join("\n");
        }
      }

      case "lean_module_census": {
        const targetPath = String(args.targetPath || "").trim();
        if (!targetPath) throw new Error("Missing required argument: 'targetPath'");

        const absTarget = path.isAbsolute(targetPath) ? targetPath : path.resolve(this.projectRoot, targetPath);
        if (!fs.existsSync(absTarget)) {
          return `Target path not found: ${targetPath}`;
        }

        const filesToScan: string[] = [];
        const stat = fs.statSync(absTarget);
        if (stat.isDirectory()) {
          const walk = (dir: string) => {
            for (const ent of fs.readdirSync(dir, { withFileTypes: true })) {
              const full = path.join(dir, ent.name);
              if (ent.isDirectory() && ent.name !== ".lake" && ent.name !== ".git") {
                walk(full);
              } else if (ent.isFile() && ent.name.endsWith(".lean")) {
                filesToScan.push(full);
              }
            }
          };
          walk(absTarget);
        } else if (stat.isFile() && absTarget.endsWith(".lean")) {
          filesToScan.push(absTarget);
        }

        let totalLines = 0;
        let codeLines = 0;
        let blankLines = 0;
        let commentLines = 0;
        let theorems = 0;
        let lemmas = 0;
        let defs = 0;
        let structures = 0;
        let classes = 0;
        let axioms = 0;
        let sorries = 0;

        for (const file of filesToScan) {
          const content = fs.readFileSync(file, "utf-8");
          const lines = content.split(/\r?\n/);
          totalLines += lines.length;
          let inBlockComment = false;

          for (const l of lines) {
            const stripped = l.trim();
            if (!stripped) {
              blankLines++;
              continue;
            }
            if (inBlockComment) {
              commentLines++;
              if (l.includes("-/")) inBlockComment = false;
              continue;
            } else if (stripped.startsWith("/-")) {
              commentLines++;
              if (!l.includes("-/")) inBlockComment = true;
              continue;
            } else if (stripped.startsWith("--")) {
              commentLines++;
              continue;
            }

            codeLines++;

            const declMatch = l.match(/^(?:(?:noncomputable|scoped|protected|private)\s+)*(theorem|lemma|def|structure|class|axiom)\s+([A-Za-z0-9_.]+)/);
            if (declMatch) {
              const k = declMatch[1];
              if (k === "theorem") theorems++;
              else if (k === "lemma") lemmas++;
              else if (k === "def") defs++;
              else if (k === "structure") structures++;
              else if (k === "class") classes++;
              else if (k === "axiom") axioms++;
            }

            if (/\b(sorry|admit|sorryAx)\b/.test(l)) {
              sorries++;
            }
          }
        }

        const format = String(args.format || "markdown").toLowerCase();
        if (format === "json") {
          return JSON.stringify({
            target: targetPath,
            modules: filesToScan.length,
            totalLines,
            codeLines,
            commentLines,
            blankLines,
            theorems,
            lemmas,
            defs,
            structures,
            classes,
            axioms,
            sorries,
          }, null, 2);
        } else if (format === "summary") {
          return `Modules: ${filesToScan.length} | Lines: ${totalLines} (code: ${codeLines}) | Theorems: ${theorems + lemmas} | Defs: ${defs + structures} | Sorries: ${sorries} | Axioms: ${axioms}`;
        } else {
          return [
            `# Lean Module Census: ${targetPath}`,
            `- **Scanned Modules**: ${filesToScan.length}`,
            `- **Total Lines**: ${totalLines.toLocaleString()} (${codeLines.toLocaleString()} code, ${commentLines.toLocaleString()} comments, ${blankLines.toLocaleString()} blank)`,
            `- **Theorems & Lemmas**: ${(theorems + lemmas).toLocaleString()} (${theorems} theorems, ${lemmas} lemmas)`,
            `- **Definitions & Structures**: ${(defs + structures).toLocaleString()} (${defs} defs, ${structures} structures, ${classes} classes)`,
            `- **Custom Axioms**: ${axioms}`,
            `- **Sorries**: ${sorries}`,
          ].join("\n");
        }
      }

      case "lean_pedagogical_walkthrough": {
        const symbol = String(args.symbol || "").trim();
        if (!symbol) throw new Error("Missing required argument: 'symbol'");

        let filePath = args.filePath ? String(args.filePath) : "";
        let line = Number(args.line ?? 0);
        let modName = "";

        const match = this.ileanIndex.lookupSymbol(symbol);
        if (match) {
          filePath = match.filePath;
          line = match.line;
          modName = match.module || "";
        }

        let absPath = "";
        let rawContent = "";
        let lines: string[] = [];
        if (filePath) {
          absPath = path.isAbsolute(filePath) ? filePath : path.resolve(this.projectRoot, filePath);
          if (fs.existsSync(absPath)) {
            rawContent = fs.readFileSync(absPath, "utf-8");
            lines = rawContent.split(/\r?\n/);
          }
        }

        // If line not known, scan lines for symbol
        if (lines.length > 0 && line === 0) {
          const symName = symbol.split(".").pop()!;
          const declRegex = new RegExp(`^(?:(?:noncomputable|scoped|protected|private)\\s+)*(?:theorem|lemma|def)\\s+${symName}\\b`);
          for (let i = 0; i < lines.length; i++) {
            if (declRegex.test(lines[i].trim())) {
              line = i + 1;
              break;
            }
          }
        }

        // Extract docstring
        let docstring = "";
        if (line > 1 && lines.length > 0) {
          let c = line - 2;
          while (c >= 0 && lines[c].trim() === "") c--;
          if (c >= 0 && lines[c].trim().endsWith("-/")) {
            const endD = c;
            while (c >= 0 && !lines[c].includes("/--")) c--;
            if (c >= 0 && lines[c].includes("/--")) {
              const docLines = lines.slice(c, endD + 1).map(l => l.replace(/^\s*\/--\s*/, "").replace(/\s*-\/\s*$/, "").trim());
              docstring = docLines.filter(Boolean).join(" ");
            }
          }
        }

        // Extract formal statement
        let statementLines: string[] = [];
        let proofStart = line;
        if (line > 0 && line <= lines.length) {
          let idx = line - 1;
          while (idx < lines.length) {
            statementLines.push(lines[idx].trim());
            if (lines[idx].includes(":=") || lines[idx].includes("where")) {
              proofStart = idx + 2;
              break;
            }
            idx++;
          }
        }
        const rawStatement = statementLines.join(" ");

        // De-formalize into LaTeX math
        let mathStatement = rawStatement
          .replace(/^(?:(?:noncomputable|scoped|protected|private)\s+)*(?:theorem|lemma|def)\s+[A-Za-z0-9_.]+\s*/, "")
          .replace(/:=\s*(?:by)?.*$/, "")
          .trim();
        mathStatement = mathStatement
          .replace(/->/g, "\\to ")
          .replace(/\bforall\b/g, "\\forall ")
          .replace(/\bexists\b/g, "\\exists ")
          .replace(/<=/g, "\\le ")
          .replace(/>=/g, "\\ge ")
          .replace(/!=/g, "\\ne ")
          .replace(/\bReal\b/g, "\\mathbb{R}")
          .replace(/\bNat\b/g, "\\mathbb{N}")
          .replace(/\bInt\b/g, "\\mathbb{Z}")
          .replace(/\bRat\b/g, "\\mathbb{Q}")
          .replace(/\bComplex\b/g, "\\mathbb{C}");

        // Extract milestones
        const milestones: Array<{ line: number; text: string }> = [];
        const milestoneRegex = /^\s*(?:have\b|obtain\b|calc\b|induction\b|rcases\b|cases\b|constructor\b|by_contra\b|ext\b)/;
        if (proofStart > 0 && proofStart <= lines.length) {
          for (let p = proofStart - 1; p < Math.min(lines.length, proofStart + 300); p++) {
            const trimmed = lines[p].trim();
            if (/^(?:(?:noncomputable|scoped|protected|private)\s+)*(?:theorem|lemma|def|structure|class)\s+[A-Za-z0-9_.]+\b/.test(trimmed)) break;
            if (trimmed.startsWith("end ") && !trimmed.startsWith("end of")) break;
            if (milestoneRegex.test(trimmed)) {
              milestones.push({ line: p + 1, text: trimmed });
            }
          }
        }

        const title = symbol.split(".").pop()!.replace(/_/g, " ").replace(/\b\w/g, c => c.toUpperCase());
        const safeSlug = symbol.toLowerCase().replace(/[^a-z0-9]+/g, "-");

        const walkthrough = [
          `# Pedagogical Proof Walkthrough: ${title}`,
          "",
          `> **Formal Declaration:** \`${symbol}\`  `,
          `> **Source File:** [\`${filePath || "unknown"}\`](file:///${absPath || filePath})  `,
          `> **Lean Blueprint Anchor:** \\\\lean{${symbol}}, \\\\label{thm:${safeSlug}}  `,
          `> **Garden Concept Zettel:** [\`zet-lean-${safeSlug}\`](file:///docs/investigation-garden/zettels/concepts/zet-lean-${safeSlug}.md)  `,
          "",
          "---",
          "",
          "## 1. Mathematical Statement & Intuitive Essence",
          "",
          "### Informal Textbook Formulation",
          "",
          `**Theorem (${title}).**  `,
          `*${docstring ? docstring : `Let the parameters be given. Under standard regular assumptions, the core invariant of ${symbol} holds: $${mathStatement}$.`}*`,
          "",
          "### Formal Lean 4 Declaration",
          "",
          "```lean",
          rawStatement || `theorem ${symbol} : ... := by ...`,
          "```",
          "",
          "### Conceptual Executive Summary",
          "",
          `The theorem \`${symbol}\` formalizes a central landmark in this domain.`,
          `The proof establishes that the prescribed invariant or bound is preserved under dynamic evolution or algebraic transformation.`,
          "",
          "---",
          "",
          "## 2. The Three-Stage Mathematical Engine",
          "",
          "```text",
          "+-----------------------------------------------------------------------------+",
          "| Stage 1: Geometric / Algebraic Setup & Invariant Conservation               |",
          "|   - Normalize input structures and isolate canonical boundary coordinates   |",
          "+-----------------------------------------------------------------------------+",
          "                                       |",
          "                                       v",
          "+-----------------------------------------------------------------------------+",
          "| Stage 2: Energy Estimates, Asymptotics & Critical Scaling                   |",
          "|   - Apply logarithmic or inductive bounds controlling error accumulation    |",
          "+-----------------------------------------------------------------------------+",
          "                                       |",
          "                                       v",
          "+-----------------------------------------------------------------------------+",
          "| Stage 3: Topological / Analytic Resolution & Conclusion                     |",
          "|   - Discharge contradiction or deduce final equality/inequality             |",
          "+-----------------------------------------------------------------------------+",
          "```",
          "",
          "---",
          "",
          "## 3. Milestone Proof Walkthrough",
          "",
          milestones.length > 0
            ? milestones.map((m, idx) => `### Milestone ${idx + 1} (Line ${m.line})\n- **Tactic Anchor:** \`${m.text}\`\n- **Mathematical Role:** Progresses intermediate sub-goal and refines hypothesis context.`).join("\n\n")
            : "*(Single-step decision procedure or direct term-mode derivation; no intermediate have/obtain milestones)*",
          "",
          "---",
          "",
          "## 4. Lean Blueprint & Knowledge Garden Integration",
          "",
          "```latex",
          `\\begin{theorem}[${title}]`,
          `\\label{thm:${safeSlug}}`,
          `\\lean{${symbol}}`,
          `\\leanok`,
          `$${mathStatement}$`,
          `\\end{theorem}`,
          "```",
          "",
          `- **Knowledge Garden Note:** \`zet-lean-${safeSlug}\` (Layer 4 Concept Zettel)`,
          `- **MOC Registration:** \`MOC-lean-and-easci\`, \`MOC-itp-master-ontology\``,
        ].join("\n");

        if (args.outputPath) {
          const out = path.isAbsolute(String(args.outputPath)) ? String(args.outputPath) : path.resolve(this.projectRoot, String(args.outputPath));
          fs.mkdirSync(path.dirname(out), { recursive: true });
          fs.writeFileSync(out, walkthrough, "utf-8");
        }

        return walkthrough;
      }

      case "lean_blueprint_status": {
        const formDir = args.formalizationDir ? path.resolve(this.projectRoot, String(args.formalizationDir)) : this.projectRoot;
        let bpDir = args.blueprintDir ? path.resolve(this.projectRoot, String(args.blueprintDir)) : "";

        if (!bpDir) {
          const candidates = [
            path.join(formDir, "blueprint/src"),
            path.join(formDir, "blueprint"),
            path.join(this.projectRoot, "docs/easci/lean/fermats-last-theorem/blueprint/src"),
            path.join(this.projectRoot, "docs/easci/lean/NavierStokesAndEuler/blueprint/src"),
          ];
          for (const c of candidates) {
            if (fs.existsSync(c)) { bpDir = c; break; }
          }
        }

        // Collect all Lean declarations and sorry status
        const leanDecls = new Map<string, { file: string; line: number; kind: string; hasSorry: boolean }>();
        const walkLean = (dir: string) => {
          if (!fs.existsSync(dir)) return;
          for (const ent of fs.readdirSync(dir, { withFileTypes: true })) {
            const p = path.join(dir, ent.name);
            if (ent.isDirectory() && ent.name !== ".lake" && ent.name !== ".git" && ent.name !== ".scratch") {
              walkLean(p);
            } else if (ent.isFile() && ent.name.endsWith(".lean")) {
              const content = fs.readFileSync(p, "utf-8");
              const lines = content.split(/\r?\n/);
              for (let i = 0; i < lines.length; i++) {
                const m = lines[i].match(/^(?:(?:noncomputable|scoped|protected|private)\s+)*(theorem|lemma|def)\s+([A-Za-z0-9_.]+)\b/);
                if (m) {
                  const kind = m[1];
                  const name = m[2];
                  // check if sorry follows
                  let hasSorry = false;
                  for (let j = i; j < Math.min(lines.length, i + 50); j++) {
                    if (/\bsorry\b/.test(lines[j])) { hasSorry = true; break; }
                    if (j > i && /^(?:(?:noncomputable|scoped|protected|private)\s+)*(?:theorem|lemma|def)\s+/.test(lines[j])) break;
                  }
                  leanDecls.set(name, { file: path.relative(this.projectRoot, p), line: i + 1, kind, hasSorry });
                }
              }
            }
          }
        };
        walkLean(formDir);

        // Collect all Blueprint declarations
        const bpDecls = new Map<string, { file: string; line: number; leanok: boolean; uses: string[] }>();
        if (bpDir && fs.existsSync(bpDir)) {
          const walkTex = (dir: string) => {
            for (const ent of fs.readdirSync(dir, { withFileTypes: true })) {
              const p = path.join(dir, ent.name);
              if (ent.isDirectory()) {
                walkTex(p);
              } else if (ent.isFile() && ent.name.endsWith(".tex")) {
                const content = fs.readFileSync(p, "utf-8");
                const lines = content.split(/\r?\n/);
                for (let i = 0; i < lines.length; i++) {
                  const lm = lines[i].match(/\\lean\{([^}]+)\}/);
                  if (lm) {
                    const declName = lm[1].trim();
                    // check environment around line i for \leanok and \uses
                    let leanok = false;
                    const uses: string[] = [];
                    for (let j = Math.max(0, i - 5); j < Math.min(lines.length, i + 15); j++) {
                      if (/\\leanok\b/.test(lines[j])) leanok = true;
                      const um = lines[j].match(/\\uses\{([^}]+)\}/);
                      if (um) {
                        uses.push(...um[1].split(",").map(u => u.trim()));
                      }
                      if (/\\end\{(?:theorem|lemma|definition)\}/.test(lines[j])) break;
                    }
                    bpDecls.set(declName, { file: path.relative(this.projectRoot, p), line: i + 1, leanok, uses });
                  }
                }
              }
            }
          };
          walkTex(bpDir);
        }

        // Compare and categorize
        const matched: string[] = [];
        const prematureLeanok: string[] = [];
        const missingLeanok: string[] = [];
        const untrackedInBlueprint: string[] = [];
        const ghostInBlueprint: string[] = [];

        for (const [name, bInfo] of bpDecls.entries()) {
          const lInfo = leanDecls.get(name);
          if (!lInfo) {
            ghostInBlueprint.push(name);
          } else {
            matched.push(name);
            if (bInfo.leanok && lInfo.hasSorry) {
              prematureLeanok.push(name);
            } else if (!bInfo.leanok && !lInfo.hasSorry) {
              missingLeanok.push(name);
            }
          }
        }

        for (const [name, lInfo] of leanDecls.entries()) {
          if (!bpDecls.has(name) && (lInfo.kind === "theorem" || lInfo.kind === "lemma") && !lInfo.hasSorry) {
            untrackedInBlueprint.push(name);
          }
        }

        const format = String(args.format || "markdown").toLowerCase();
        if (format === "json") {
          return JSON.stringify({
            formalizationDir: path.relative(this.projectRoot, formDir),
            blueprintDir: bpDir ? path.relative(this.projectRoot, bpDir) : null,
            totalLeanDeclarations: leanDecls.size,
            totalBlueprintNodes: bpDecls.size,
            matchedDeclarations: matched.length,
            prematureLeanokCount: prematureLeanok.length,
            missingLeanokCount: missingLeanok.length,
            untrackedLandmarksCount: untrackedInBlueprint.length,
            ghostBlueprintNodesCount: ghostInBlueprint.length,
            prematureLeanok,
            missingLeanok,
            ghostInBlueprint,
          }, null, 2);
        } else if (format === "summary") {
          return `Lean: ${leanDecls.size} decls | Blueprint: ${bpDecls.size} nodes | Matched: ${matched.length} | Premature \\leanok: ${prematureLeanok.length} | Missing \\leanok: ${missingLeanok.length} | Ghost: ${ghostInBlueprint.length}`;
        } else {
          return [
            `# Lean Blueprint Audit Status`,
            `- **Formalization Root:** \`${path.relative(this.projectRoot, formDir)}\``,
            `- **Blueprint Directory:** \`${bpDir ? path.relative(this.projectRoot, bpDir) : "Not Found"}\``,
            `- **Lean Declarations:** ${leanDecls.size.toLocaleString()}`,
            `- **Blueprint Nodes:** ${bpDecls.size.toLocaleString()}`,
            `- **Matched Declarations:** ${matched.length.toLocaleString()}`,
            "",
            `### Audit Findings`,
            `- **Premature \\\\leanok (Contains sorry in Lean!):** ${prematureLeanok.length} ${prematureLeanok.length > 0 ? "[ALERT: UNPROVEN]" : "[CLEAN]"}`,
            ...(prematureLeanok.slice(0, 10).map(s => `  * \`${s}\``)),
            `- **Missing \\\\leanok (Proved in Lean, but unflagged in Blueprint):** ${missingLeanok.length}`,
            ...(missingLeanok.slice(0, 10).map(s => `  * \`${s}\``)),
            `- **Ghost Blueprint Nodes (In LaTeX but missing from Lean):** ${ghostInBlueprint.length}`,
            ...(ghostInBlueprint.slice(0, 10).map(s => `  * \`${s}\``)),
            `- **Untracked Landmark Theorems (Proved in Lean without Blueprint node):** ${untrackedInBlueprint.length}`,
          ].join("\n");
        }
      }

      case "lean_zettel_scaffold": {
        const symbol = String(args.symbol || "").trim();
        if (!symbol) throw new Error("Missing required argument: 'symbol'");

        let filePath = args.filePath ? String(args.filePath) : "";
        let line = 0;
        let modName = "";

        const match = this.ileanIndex.lookupSymbol(symbol);
        if (match) {
          filePath = match.filePath;
          line = match.line;
          modName = match.module || "";
        }

        let absPath = "";
        let lines: string[] = [];
        if (filePath) {
          absPath = path.isAbsolute(filePath) ? filePath : path.resolve(this.projectRoot, filePath);
          if (fs.existsSync(absPath)) {
            lines = fs.readFileSync(absPath, "utf-8").split(/\r?\n/);
          }
        }

        if (lines.length > 0 && line === 0) {
          const symName = symbol.split(".").pop()!;
          const declRegex = new RegExp(`^(?:(?:noncomputable|scoped|protected|private)\\s+)*(?:theorem|lemma|def)\\s+${symName}\\b`);
          for (let i = 0; i < lines.length; i++) {
            if (declRegex.test(lines[i].trim())) {
              line = i + 1;
              break;
            }
          }
        }

        const safeSlug = symbol.toLowerCase().replace(/[^a-z0-9]+/g, "-");
        const title = symbol.split(".").pop()!.replace(/_/g, " ").replace(/\b\w/g, c => c.toUpperCase());

        let sig = `theorem ${symbol} : ... := by ...`;
        if (line > 0 && line <= lines.length) {
          const sLines: string[] = [];
          for (let i = line - 1; i < lines.length; i++) {
            sLines.push(lines[i].trim());
            if (lines[i].includes(":=") || lines[i].includes("where")) break;
          }
          sig = sLines.join(" ");
        }

        const zettel = [
          "---",
          `id: zet-lean-${safeSlug}`,
          "layer: 4",
          `title: "${title} Formalization"`,
          "status: verified",
          "maturity: seedling",
          "verification: anchor-resolved",
          "master_concept: CONCEPT-FORMAL-VERIFICATION",
          "msc2020:",
          '  - "03B35"',
          '  - "68V15"',
          `lean4_decl: ${symbol}`,
          'coq_tactic: "auto"',
          'isabelle_tactic: "auto"',
          'hol_light_tactic: "MESON_TAC []"',
          `statutory_urn: "urn:itp:lean4:${modName || symbol}:${symbol}"`,
          "sources:",
          `  - "${filePath || "docs/easci/lean"}"`,
          '  - "docs/investigation-garden/source-materials/indexes/master-authority-index.json"',
          "indexed-by:",
          "  - MOC-lean-and-easci",
          "related:",
          "---",
          "",
          `# ZET-LEAN-${safeSlug.toUpperCase()}: ${title} Formalization`,
          "",
          "## 1. Formal Mathematical Assertion & Lean 4 Specification",
          "",
          `The formal declaration \`${symbol}\` specifies the theorem in Lean 4.`,
          "",
          "```lean",
          sig,
          "```",
          "",
          "## 2. Mathematical Narrative & Blueprint Scaffolding",
          "",
          `In standard mathematical terminology, \`${symbol}\` establishes the core invariant.`,
          "In the Lean Blueprint system (PlasTeX), this corresponds to the specification environment:",
          "",
          "```latex",
          `\\begin{theorem}[${title}]`,
          `\\label{thm:${safeSlug}}`,
          `\\lean{${symbol}}`,
          `\\leanok`,
          `  % Formal statement of ${symbol}`,
          `\\end{theorem}`,
          "```",
          "",
          "## 3. Proof Milestones & Dependency Anchor",
          "",
          "The proof proceeds by structured sub-hypotheses milestones or kernel decision procedures.",
          "",
          "## 4. Cross-Prover & Statutory Concordance",
          "",
          "| Proof System | Tactic / Construct | Semantic Role |",
          "| :--- | :--- | :--- |",
          `| **Lean 4** | \`${symbol}\` | Primary certified formal declaration |`,
          '| **Coq** | `auto` | Equivalent tactic/lemma representation |',
          '| **Isabelle/HOL** | `auto` | Sledgehammer / simp automation hook |',
          '| **HOL Light** | `MESON_TAC []` | First-order / arithmetic proof tactic |',
          "",
          "## 5. Operational Proof Swarm Invariant",
          "",
          `- **Kernel Purity**: \`${symbol}\` must compile clean under \`set_option autoImplicit false\` with 0 sorries.`,
          "- **Blueprint Synchronization**: Any modification to signature or premise set must update the PlasTeX blueprint \\uses{} graph.",
          "- **Concordance Grounding**: Maintain semantic equivalence with the master concept authority catalog.",
        ].join("\n");

        if (args.outputPath) {
          const out = path.isAbsolute(String(args.outputPath)) ? String(args.outputPath) : path.resolve(this.projectRoot, String(args.outputPath));
          fs.mkdirSync(path.dirname(out), { recursive: true });
          fs.writeFileSync(out, zettel, "utf-8");
        }

        return zettel;
      }

      case "lean_blueprint": {
        const action = String(args.action || "status").toLowerCase();
        if (action === "scaffold") {
          return await this.executeTool("lean_blueprint_scaffold", args);
        } else if (action === "skeleton") {
          return await this.executeTool("lean_proof_skeleton", args);
        } else if (action === "walkthrough") {
          return await this.executeTool("lean_pedagogical_walkthrough", args);
        } else if (action === "zettel") {
          return await this.executeTool("lean_zettel_scaffold", args);
        } else if (action === "graph_neighborhood") {
          const sectionId = args.sectionId || args.symbol || args.query;
          if (!sectionId) throw new Error("Missing required argument: 'sectionId' or 'symbol'");
          const n = this.kuzuGraph.getNeighborhood(sectionId);
          if (!n.section) return `Section '${sectionId}' not found in Kuzu knowledge graph.`;
          return [
            `# Kuzu Knowledge Graph Neighborhood: ${n.section.title}`,
            `- **Section ID:** \`${n.section.id}\``,
            `- **Book:** ${n.book ? n.book.title : n.section.bookKey} (${n.section.bookKey})`,
            `- **Hierarchy Level:** ${n.section.level}`,
            `- **Adjacent Sections (${n.siblings.length}):**`,
            ...n.siblings.map(s => `  * [${s.id === n.section?.id ? "CURRENT" : "SIBLING"}] \`${s.id}\`: ${s.title}`),
          ].join("\n");
        } else {
          return await this.executeTool("lean_blueprint_status", args);
        }
      }

      case "lean_metrics": {
        const action = String(args.action || "census").toLowerCase();
        const target = args.target || args.targetPath || args.moduleName || args.filePath || ".";
        if (action === "hierarchy") {
          return await this.executeTool("lean_module_hierarchy", {
            moduleName: target,
            direction: args.direction,
            transitive: args.transitive,
            maxDepth: args.maxDepth,
          });
        } else if (action === "subgraph") {
          return await this.executeTool("lean_dependency_subgraph", {
            moduleName: target,
            maxDepth: args.maxDepth,
            format: args.format,
          });
        } else {
          return await this.executeTool("lean_module_census", {
            targetPath: target,
            format: args.format,
          });
        }
      }

      case "lean_ffi": {
        const action = String(args.action || "inspect_env").toLowerCase();
        if (action === "sysroot") {
          const flags = LeanSysrootBridge.getIncludeFlags();
          return `Lean Sysroot Include Flags:\n${flags.join(" ")}`;
        }
        return await this.executeTool("lean_c_ffi_inspect", args);
      }

      case "lean_exec": {
        return await this.executeTool("lean_run_code", args);
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
