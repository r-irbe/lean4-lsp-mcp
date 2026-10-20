/**
 * src/kuzu_graph.ts
 *
 * Embedded Kuzu Knowledge Graph Engine for lean4-lsp-mcp.
 * Directly indexes and queries the canonical 29-book, 1,759-section
 * ITP / Lean formalization knowledge base (`easci-knowledge.kz` / `prover_knowledge.kz`).
 *
 * Strict 7-bit ASCII only (INV-001).
 */

import * as fs from "node:fs";
import * as path from "node:path";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

export interface BookRecord {
  key: string;
  title: string;
  license: string;
  sourceFormat: string;
}

export interface SectionRecord {
  id: string;
  bookKey: string;
  level: number;
  title: string;
}

export interface ConceptRecord {
  id: string;
  name: string;
  msc2020: string;
  domainTheory: string;
}

export interface ZettelRecord {
  id: string;
  title: string;
  layer: number;
  status: string;
  sourceBook: string;
  sourceAnchor: string;
  masterConcept: string;
  filePath: string;
}

export interface KuzuDatabaseConfig {
  id: string;
  name: string;
  path: string;
  archivePath?: string;
  scope: string;
  readOnly: boolean;
  enabled: boolean;
  priority: number;
  description?: string;
}

export interface KuzuFederationConfig {
  version: string;
  projectName?: string;
  databases: KuzuDatabaseConfig[];
  federation?: {
    parallelQueries?: boolean;
    maxWorkers?: number;
    timeoutMs?: number;
    mergeStrategy?: string;
  };
}

export interface KuzuSearchResult {
  sectionId: string;
  bookKey: string;
  bookTitle: string;
  sectionTitle: string;
  score: number;
}

export interface KuzuGraphOptions {
  kzPath?: string;
  dbPath?: string;
  configPath?: string;
  workspaceRoot?: string;
  pythonBin?: string;
}

function collectCandidateRoots(workspaceRoot?: string): string[] {
  const roots: string[] = [];
  const seen = new Set<string>();
  const addRoot = (dir: string | undefined) => {
    if (!dir) return;
    const resolved = path.resolve(dir);
    if (!seen.has(resolved)) {
      seen.add(resolved);
      roots.push(resolved);
    }
  };

  const seeds = [
    workspaceRoot,
    process.env.TACIT_ROOT,
    process.env.LEAN_PROJECT_ROOT,
    process.cwd(),
    __dirname,
  ];

  for (const seed of seeds) {
    if (!seed) continue;
    let curr = path.resolve(seed);
    for (let depth = 0; depth < 8; depth++) {
      addRoot(curr);
      const siblingTacit = path.join(curr, "tacit-mui");
      if (fs.existsSync(siblingTacit)) {
        addRoot(siblingTacit);
      }
      const parent = path.dirname(curr);
      if (parent === curr) break;
      curr = parent;
    }
  }
  return roots;
}

export class KuzuKnowledgeGraph {
  public kzPath: string;
  public dbPath: string = "";
  public configPath: string = "";
  public federationConfig: KuzuFederationConfig | null = null;
  public books: Map<string, BookRecord> = new Map();
  public sections: Map<string, SectionRecord> = new Map();
  public concepts: Map<string, ConceptRecord> = new Map();
  public zettels: Map<string, ZettelRecord> = new Map();
  public bookSections: Map<string, string[]> = new Map();
  private loaded: boolean = false;
  private pythonBin?: string;

  constructor(kzPathOrOptions?: string | KuzuGraphOptions, options?: KuzuGraphOptions) {
    const opts: KuzuGraphOptions =
      typeof kzPathOrOptions === "string"
        ? { ...options, kzPath: kzPathOrOptions }
        : { ...(kzPathOrOptions || {}), ...(options || {}) };

    this.pythonBin = opts.pythonBin;
    const candidateRoots = collectCandidateRoots(opts.workspaceRoot);

    // 1. Resolve .kuzu-config.json if available
    const configCandidates: string[] = [
      opts.configPath || "",
      process.env.KUZU_CONFIG || "",
    ];
    for (const root of candidateRoots) {
      configCandidates.push(path.join(root, ".kuzu-config.json"));
      configCandidates.push(path.join(root, "docs", "investigation-garden", ".kuzu-config.json"));
    }

    for (const cp of configCandidates) {
      if (cp && fs.existsSync(cp)) {
        try {
          const raw = fs.readFileSync(cp, "utf-8");
          const parsed = JSON.parse(raw);
          if (parsed && Array.isArray(parsed.databases)) {
            this.configPath = cp;
            this.federationConfig = {
              version: parsed.version || "1.0",
              projectName: parsed.project_name || parsed.projectName,
              databases: (parsed.databases || []).map((d: any) => ({
                id: d.id,
                name: d.name,
                path: d.path,
                archivePath: d.archive_path || d.archivePath,
                scope: d.scope,
                readOnly: Boolean(d.read_only ?? d.readOnly ?? false),
                enabled: Boolean(d.enabled ?? true),
                priority: Number(d.priority ?? 0),
                description: d.description,
              })),
              federation: parsed.federation,
            };
            break;
          }
        } catch {
          // Ignore malformed config, continue search
        }
      }
    }

    // 2. Resolve kuzu_db directory / path (parameterized or env-configured via KUZU_DB_PATH)
    const explicitDbPath = opts.dbPath || process.env.KUZU_DB_PATH || "";
    if (explicitDbPath) {
      this.dbPath = path.resolve(explicitDbPath);
    } else if (this.federationConfig && this.configPath) {
      const cfgRoot = path.dirname(this.configPath);
      const primaryDb = this.federationConfig.databases.find((d) => d.enabled && d.path);
      if (primaryDb) {
        this.dbPath = path.resolve(cfgRoot, primaryDb.path);
      }
    }
    if (!this.dbPath) {
      for (const root of candidateRoots) {
        const candDb = path.join(root, "docs", "investigation-garden", "kuzu_db");
        if (fs.existsSync(candDb)) {
          this.dbPath = candDb;
          break;
        }
      }
    }

    // 3. Resolve .kz archive path
    const explicitKz =
      opts.kzPath ||
      process.env.KUZU_ARCHIVE_PATH ||
      process.env.LEAN_KNOWLEDGE_KZ ||
      process.env.PROVER_KNOWLEDGE_KZ ||
      process.env.EASCI_KNOWLEDGE_KZ ||
      (explicitDbPath.endsWith(".kz") ? explicitDbPath : "");

    if (explicitKz && fs.existsSync(explicitKz)) {
      this.kzPath = path.resolve(explicitKz);
    } else {
      let configArchive = "";
      if (this.federationConfig && this.configPath) {
        const root = path.dirname(this.configPath);
        for (const db of this.federationConfig.databases) {
          if (db.archivePath) {
            const resolved = path.resolve(root, db.archivePath);
            if (fs.existsSync(resolved)) {
              configArchive = resolved;
              break;
            }
          }
        }
      }

      const candidates: string[] = [configArchive];
      if (this.dbPath && !this.dbPath.endsWith(".kz")) {
        candidates.push(path.join(path.dirname(this.dbPath), "kuzu", "prover_knowledge.kz"));
        candidates.push(path.join(path.dirname(this.dbPath), "kuzu", "easci-knowledge.kz"));
      }
      for (const root of candidateRoots) {
        candidates.push(path.join(root, "kuzu", "prover_knowledge.kz"));
        candidates.push(path.join(root, "docs", "easci", "lean", "skills", "kuzu", "prover_knowledge.kz"));
        candidates.push(path.join(root, "docs", "investigation-garden", "kuzu", "prover_knowledge.kz"));
        candidates.push(path.join(root, "docs", "investigation-garden", "kuzu", "easci-knowledge.kz"));
        candidates.push(path.join(root, "docs", "easci", "lean", "skills", "kuzu", "easci-knowledge.kz"));
        candidates.push(path.join(root, "kuzu", "easci-knowledge.kz"));
      }
      this.kzPath = candidates.find((p) => p && fs.existsSync(p)) || "";
    }
  }

  /**
   * Initializes and indexes the graph from the .kz archive.
   */
  public load(): boolean {
    if (this.loaded || !this.kzPath || !fs.existsSync(this.kzPath)) {
      return this.loaded;
    }

    try {
      // Read Book.csv from zip
      const bookCsv = execFileSync("unzip", ["-p", this.kzPath, "Book.csv"], {
        encoding: "utf-8",
        maxBuffer: 10 * 1024 * 1024,
      });
      for (const line of bookCsv.split("\n")) {
        const trimmed = line.trim();
        if (!trimmed) continue;
        const parts = this.parseCsvLine(trimmed);
        if (parts.length >= 2 && parts[0] !== "id" && parts[0] !== "key") {
          const key = parts[0].trim();
          this.books.set(key, {
            key,
            title: parts[1].trim(),
            license: parts[2] ? parts[2].trim() : "Unknown",
            sourceFormat: parts[3] ? parts[3].trim() : "Markdown",
          });
          this.bookSections.set(key, []);
        }
      }

      // Read Section.csv from zip
      const sectionCsv = execFileSync("unzip", ["-p", this.kzPath, "Section.csv"], {
        encoding: "utf-8",
        maxBuffer: 25 * 1024 * 1024,
      });
      for (const line of sectionCsv.split("\n")) {
        const trimmed = line.trim();
        if (!trimmed) continue;
        const parts = this.parseCsvLine(trimmed);
        if (parts.length >= 4 && parts[0] !== "id") {
          const id = parts[0].trim();
          const bookKey = parts[1].trim();
          const level = parseInt(parts[2].trim(), 10) || 0;
          const title = parts[3].trim();
          this.sections.set(id, { id, bookKey, level, title });
          if (!this.bookSections.has(bookKey)) {
            this.bookSections.set(bookKey, []);
          }
          this.bookSections.get(bookKey)!.push(id);
        }
      }

      // Try reading Concept.csv from zip if present
      try {
        const conceptCsv = execFileSync("unzip", ["-p", this.kzPath, "Concept.csv"], {
          encoding: "utf-8",
          maxBuffer: 10 * 1024 * 1024,
          stdio: ["ignore", "pipe", "ignore"],
        });
        for (const line of conceptCsv.split("\n")) {
          const trimmed = line.trim();
          if (!trimmed) continue;
          const parts = this.parseCsvLine(trimmed);
          if (parts.length >= 2 && parts[0] !== "id") {
            const id = parts[0].trim();
            this.concepts.set(id, {
              id,
              name: parts[1].trim(),
              msc2020: parts[2] ? parts[2].trim() : "",
              domainTheory: parts[3] ? parts[3].trim() : "",
            });
          }
        }
      } catch {
        // Concept.csv optional
      }

      // Try reading Zettel.csv from zip if present
      try {
        const zettelCsv = execFileSync("unzip", ["-p", this.kzPath, "Zettel.csv"], {
          encoding: "utf-8",
          maxBuffer: 20 * 1024 * 1024,
          stdio: ["ignore", "pipe", "ignore"],
        });
        for (const line of zettelCsv.split("\n")) {
          const trimmed = line.trim();
          if (!trimmed) continue;
          const parts = this.parseCsvLine(trimmed);
          if (parts.length >= 2 && parts[0] !== "id") {
            const id = parts[0].trim();
            this.zettels.set(id, {
              id,
              title: parts[1].trim(),
              layer: parseInt(parts[2] ? parts[2].trim() : "4", 10) || 4,
              status: parts[3] ? parts[3].trim() : "verified",
              sourceBook: parts[6] ? parts[6].trim() : "",
              sourceAnchor: parts[7] ? parts[7].trim() : "",
              masterConcept: parts[8] ? parts[8].trim() : "",
              filePath: parts[9] ? parts[9].trim() : "",
            });
          }
        }
      } catch {
        // Zettel.csv optional
      }

      this.loaded = true;
      return true;
    } catch {
      return false;
    }
  }

  /**
   * Sub-millisecond keyword search across all 1,759 book sections.
   */
  public search(query: string, limit: number = 10): KuzuSearchResult[] {
    if (!this.loaded) {
      this.load();
    }
    const terms = query
      .toLowerCase()
      .split(/\s+/)
      .filter((t) => t.length > 2);
    if (terms.length === 0) return [];

    const results: KuzuSearchResult[] = [];

    for (const [id, section] of this.sections.entries()) {
      const text = `${id} ${section.bookKey} ${section.title}`.toLowerCase();
      let matchCount = 0;
      for (const term of terms) {
        if (text.includes(term)) {
          matchCount++;
        }
      }

      if (matchCount > 0) {
        const book = this.books.get(section.bookKey);
        results.push({
          sectionId: id,
          bookKey: section.bookKey,
          bookTitle: book ? book.title : section.bookKey,
          sectionTitle: section.title,
          score: matchCount / terms.length,
        });
      }
    }

    results.sort((a, b) => b.score - a.score);
    return results.slice(0, limit);
  }

  /**
   * Retrieves adjacent section context within the parent book.
   */
  public getNeighborhood(sectionId: string): {
    section: SectionRecord | null;
    book: BookRecord | null;
    siblings: SectionRecord[];
  } {
    if (!this.loaded) this.load();
    const section = this.sections.get(sectionId) || null;
    if (!section) {
      return { section: null, book: null, siblings: [] };
    }
    const book = this.books.get(section.bookKey) || null;
    const siblingIds = this.bookSections.get(section.bookKey) || [];
    const idx = siblingIds.indexOf(sectionId);
    const start = Math.max(0, idx - 2);
    const end = Math.min(siblingIds.length, idx + 3);
    const siblings = siblingIds
      .slice(start, end)
      .map((sid) => this.sections.get(sid)!)
      .filter(Boolean);

    return { section, book, siblings };
  }

  /**
   * Returns parsed .kuzu-config.json federation configuration if present.
   */
  public getFederatedConfig(): KuzuFederationConfig | null {
    return this.federationConfig;
  }

  /**
   * Search across master concepts loaded from the knowledge graph.
   */
  public searchConcepts(query: string, limit: number = 10): ConceptRecord[] {
    if (!this.loaded) this.load();
    const terms = query.toLowerCase().split(/\s+/).filter((t) => t.length > 2);
    if (terms.length === 0) return [];

    const matches: { concept: ConceptRecord; score: number }[] = [];
    for (const concept of this.concepts.values()) {
      const text = `${concept.id} ${concept.name} ${concept.domainTheory}`.toLowerCase();
      let matchCount = 0;
      for (const t of terms) {
        if (text.includes(t)) matchCount++;
      }
      if (matchCount > 0) {
        matches.push({ concept, score: matchCount / terms.length });
      }
    }
    matches.sort((a, b) => b.score - a.score);
    return matches.slice(0, limit).map((m) => m.concept);
  }

  /**
   * Search across atomic evidence zettels loaded from the knowledge graph.
   */
  public searchZettels(query: string, limit: number = 10): ZettelRecord[] {
    if (!this.loaded) this.load();
    const terms = query.toLowerCase().split(/\s+/).filter((t) => t.length > 2);
    if (terms.length === 0) return [];

    const matches: { zettel: ZettelRecord; score: number }[] = [];
    for (const zettel of this.zettels.values()) {
      const text = `${zettel.id} ${zettel.title} ${zettel.masterConcept}`.toLowerCase();
      let matchCount = 0;
      for (const t of terms) {
        if (text.includes(t)) matchCount++;
      }
      if (matchCount > 0) {
        matches.push({ zettel, score: matchCount / terms.length });
      }
    }
    matches.sort((a, b) => b.score - a.score);
    return matches.slice(0, limit).map((m) => m.zettel);
  }

  /**
   * Cache elaborated symbol to local lsp_cache.kuzu if configured.
   */
  public cacheSymbol(moduleName: string, symbolName: string, typeSig: string): boolean {
    if (!this.federationConfig || !this.configPath) return false;
    const cacheDb = this.federationConfig.databases.find((d) => d.id === "lsp_cache" && d.enabled);
    if (!cacheDb) return false;

    try {
      const cfgDir = path.dirname(this.configPath);
      const pyScript = path.resolve(cfgDir, "tools/gardener/kuzu_query.py");
      const pyCandidates = [
        this.pythonBin || "",
        process.env.KUZU_PYTHON_BIN || "",
        process.env.PYTHON_BIN || "",
        "python3",
      ].filter(Boolean);
      const pyBin = pyCandidates.find((p) => {
        try {
          execFileSync(p, ["--version"], { stdio: "ignore" });
          return true;
        } catch {
          return false;
        }
      });
      if (pyBin && fs.existsSync(pyScript)) {
        const inlineCode =
          "import sys; from tools.gardener.kuzu_federation import FederatedKuzuEngine; " +
          "e = FederatedKuzuEngine(); e.cache_symbol(sys.argv[1], sys.argv[2], sys.argv[3])";
        execFileSync(pyBin, ["-c", inlineCode, moduleName, symbolName, typeSig], {
          cwd: cfgDir,
          stdio: "ignore",
          timeout: 3000,
        });
        return true;
      }
      return false;
    } catch {
      return false;
    }
  }

  private parseCsvLine(line: string): string[] {
    const result: string[] = [];
    let current = "";
    let inQuotes = false;
    for (let i = 0; i < line.length; i++) {
      const char = line[i];
      if (char === '"') {
        inQuotes = !inQuotes;
      } else if (char === "," && !inQuotes) {
        result.push(current);
        current = "";
      } else {
        current += char;
      }
    }
    result.push(current);
    return result;
  }
}
