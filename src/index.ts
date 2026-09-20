// tools/lean_lsp_mcp/src/index.ts
// Standalone Model Context Protocol (MCP) server for Lean 4 & C FFI.
// Strict 7-bit ASCII only (INV-001).

import * as fs from "node:fs";
import * as path from "node:path";
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
        moduleName: { type: "string", description: "Full module name (e.g. EASCI.ReinforcementLearning.Core)" },
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
];

export class Lean4IleanIndex {
  private projectRoot: string;
  private cache: Map<string, IleanFile> = new Map();
  private symbolIndex: Map<string, IleanSymbolEntry> = new Map();
  private moduleImportsMap: Map<string, string[]> = new Map();
  private moduleImportedByMap: Map<string, string[]> = new Map();

  constructor(projectRoot: string) {
    this.projectRoot = projectRoot;
  }

  public refresh(): void {
    this.cache.clear();
    this.symbolIndex.clear();
    this.moduleImportsMap.clear();
    this.moduleImportedByMap.clear();

    const candidateRoots = [
      path.join(this.projectRoot, ".lake", "build", "lib", "lean"),
      path.join(this.projectRoot, ".lake", "build", "ir"),
      path.join(this.projectRoot, "docs", "easci", "lean", ".lake", "build", "lib", "lean"),
      path.join(this.projectRoot, "docs", "easci", "lean", ".lake", "build", "ir"),
    ];

    // Discover .lake/packages for Mathlib and external libraries
    const packageDirs = [
      path.join(this.projectRoot, ".lake", "packages"),
      path.join(this.projectRoot, "docs", "easci", "lean", ".lake", "packages"),
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

    // Build reverse importedBy graph
    for (const [mod, imps] of this.moduleImportsMap.entries()) {
      for (const imp of imps) {
        let list = this.moduleImportedByMap.get(imp);
        if (!list) {
          list = [];
          this.moduleImportedByMap.set(imp, list);
        }
        if (!list.includes(mod)) {
          list.push(mod);
        }
      }
    }
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
        const candidate1 = path.join(this.projectRoot, "docs", "easci", "lean", relLean);
        const candidate2 = path.join(this.projectRoot, relLean);
        if (fs.existsSync(candidate1)) {
          sourceFile = path.relative(this.projectRoot, candidate1);
        } else if (fs.existsSync(candidate2)) {
          sourceFile = path.relative(this.projectRoot, candidate2);
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
    if (this.moduleImportsMap.size === 0) {
      this.refresh();
    }
    return this.moduleImportsMap.get(moduleName) || [];
  }

  public getModuleImportedBy(moduleName: string): string[] {
    if (this.moduleImportedByMap.size === 0) {
      this.refresh();
    }
    return this.moduleImportedByMap.get(moduleName) || [];
  }

  public getTransitiveClosure(
    rootModule: string,
    direction: "imports" | "importedBy",
    maxDepth: number = 20
  ): TransitiveClosureResult {
    const neighborFn = direction === "imports"
      ? (m: string) => this.getModuleImports(m)
      : (m: string) => this.getModuleImportedBy(m);

    const visited = new Set<string>();
    const queue: Array<{ name: string; depth: number; path: string[] }> = [
      { name: rootModule, depth: 0, path: [rootModule] },
    ];
    let maxDepthReached = 0;
    let detectedCycle: string[] | undefined;

    while (queue.length > 0) {
      const curr = queue.shift()!;
      if (curr.depth >= maxDepth) continue;

      const neighbors = neighborFn(curr.name);
      for (const n of neighbors) {
        if (curr.path.includes(n)) {
          if (!detectedCycle) {
            detectedCycle = [...curr.path, n];
          }
          continue;
        }
        if (!visited.has(n)) {
          visited.add(n);
          maxDepthReached = Math.max(maxDepthReached, curr.depth + 1);
          queue.push({ name: n, depth: curr.depth + 1, path: [...curr.path, n] });
        }
      }
    }

    return {
      items: Array.from(visited),
      depth: maxDepthReached,
      hasCycle: detectedCycle !== undefined,
      cyclePath: detectedCycle,
    };
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
      scanLeanDir(path.join(projectRoot, "docs", "easci", "lean"));
      scanLeanDir(path.join(projectRoot, "src"));

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
  source: "lockfile" | "process_table" | "none";
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

export class LakeServerManager {
  private projectRoot: string;
  private activeSession: {
    child: ChildProcess;
    leanRoot: string;
    nextId: number;
    pendingRequests: Map<number, { resolve: (val: any) => void; reject: (err: any) => void }>;
    openedFiles: Set<string>;
    buffer: Buffer;
  } | null = null;

  constructor(projectRoot: string) {
    this.projectRoot = projectRoot;
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
    const easciLean = path.join(this.projectRoot, "docs", "easci", "lean");
    if (fs.existsSync(path.join(easciLean, "lakefile.lean"))) {
      return easciLean;
    }
    return this.projectRoot;
  }

  private async ensureSession(targetFile: string): Promise<NonNullable<LakeServerManager["activeSession"]>> {
    const leanRoot = this.findLeanRoot(targetFile);
    if (this.activeSession && this.activeSession.leanRoot === leanRoot) {
      return this.activeSession;
    }
    this.dispose();

    const session: NonNullable<LakeServerManager["activeSession"]> = {
      child: spawn("lake", ["serve"], {
        cwd: leanRoot,
        stdio: ["pipe", "pipe", "ignore"],
      }),
      leanRoot,
      nextId: 1,
      pendingRequests: new Map(),
      openedFiles: new Set(),
      buffer: Buffer.alloc(0),
    };

    session.child.stdout?.on("data", (chunk: Buffer) => {
      session.buffer = Buffer.concat([session.buffer, chunk]);
      while (true) {
        const idx = session.buffer.indexOf("\r\n\r\n");
        if (idx === -1) break;
        const header = session.buffer.subarray(0, idx).toString("utf-8");
        const match = header.match(/Content-Length:\s*(\d+)/i);
        if (!match) {
          session.buffer = session.buffer.subarray(idx + 4);
          continue;
        }
        const len = parseInt(match[1], 10);
        if (session.buffer.length < idx + 4 + len) break;
        const body = session.buffer.subarray(idx + 4, idx + 4 + len).toString("utf-8");
        session.buffer = session.buffer.subarray(idx + 4 + len);
        try {
          const parsed = JSON.parse(body);
          if (parsed.id !== undefined && session.pendingRequests.has(parsed.id)) {
            const handler = session.pendingRequests.get(parsed.id)!;
            session.pendingRequests.delete(parsed.id);
            if (parsed.error) {
              handler.reject(new Error(parsed.error.message || JSON.stringify(parsed.error)));
            } else {
              handler.resolve(parsed.result);
            }
          }
        } catch {
          // Ignore corrupted frames
        }
      }
    });

    session.child.on("error", (err) => {
      process.stderr.write(`[lean-lsp-mcp] lake serve process error: ${err.message}\n`);
    });

    session.child.on("exit", (code) => {
      process.stderr.write(`[lean-lsp-mcp] lake serve exited with code ${code}\n`);
      this.activeSession = null;
    });

    this.activeSession = session;

    await this.sendRequest(session, "initialize", {
      processId: process.pid,
      rootUri: pathToFileURL(leanRoot).href,
      capabilities: {},
    });

    this.sendNotification(session, "initialized", {});

    return session;
  }

  private sendRequest(
    session: NonNullable<LakeServerManager["activeSession"]>,
    method: string,
    params: any
  ): Promise<any> {
    return new Promise((resolve, reject) => {
      const id = session.nextId++;
      const timer = setTimeout(() => {
        session.pendingRequests.delete(id);
        reject(new Error(`Timeout waiting for LSP response to ${method} (id: ${id})`));
      }, 25000); // 25s timeout for heavy Mathlib / scheme elaborations

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

  private sendNotification(
    session: NonNullable<LakeServerManager["activeSession"]>,
    method: string,
    params: any
  ): void {
    const msg = JSON.stringify({ jsonrpc: "2.0", method, params });
    const header = `Content-Length: ${Buffer.byteLength(msg, "utf-8")}\r\n\r\n`;
    session.child.stdin?.write(header + msg);
  }

  public async getGoal(
    filePath: string,
    line: number,
    col: number,
    filterOpts?: GoalFilterOptions
  ): Promise<string> {
    const absPath = path.isAbsolute(filePath) ? filePath : path.resolve(this.projectRoot, filePath);
    if (!fs.existsSync(absPath)) {
      return `File not found: ${filePath}`;
    }

    try {
      const leanRoot = this.findLeanRoot(absPath);
      const buildStatus = LakeBuildGuard.inspectBuildActivity(leanRoot);
      if (buildStatus.isLocked) {
        return `[Lake Build Active] Compilation is currently active in ${leanRoot} (${buildStatus.detail || buildStatus.source}). Interactive goal query throttled to prevent .olean cache collision.`;
      }

      const session = await this.ensureSession(absPath);
      const uri = pathToFileURL(absPath).href;

      if (!session.openedFiles.has(absPath)) {
        const text = fs.readFileSync(absPath, "utf-8");
        this.sendNotification(session, "textDocument/didOpen", {
          textDocument: {
            uri,
            languageId: "lean4",
            version: 1,
            text,
          },
        });
        session.openedFiles.add(absPath);
      }

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

    try {
      const session = await this.ensureSession(absPath);
      const uri = pathToFileURL(absPath).href;

      if (!session.openedFiles.has(absPath)) {
        const text = fs.readFileSync(absPath, "utf-8");
        this.sendNotification(session, "textDocument/didOpen", {
          textDocument: {
            uri,
            languageId: "lean4",
            version: 1,
            text,
          },
        });
        session.openedFiles.add(absPath);
      }

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

  public dispose(): void {
    if (this.activeSession) {
      try {
        this.activeSession.child.kill();
      } catch {
        // Ignore terminated process errors
      }
      this.activeSession = null;
    }
  }
}

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

        case "tools/list":
          return {
            jsonrpc: "2.0",
            id,
            result: {
              tools: TOOL_DEFINITIONS,
            },
          };

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
