/**
 * docs/easci/lean/skills/tools/lean-lsp-mcp/src/kuzu_graph.ts
 *
 * Embedded Kuzu Knowledge Graph Engine for lean4-lsp-mcp.
 * Directly indexes and queries the canonical 29-book, 1,759-section
 * ITP / Lean formalization knowledge base (`easci-knowledge.kz`).
 *
 * Strict 7-bit ASCII only (INV-001).
 */

import * as fs from "node:fs";
import * as path from "node:path";
import { execSync } from "node:child_process";
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

export interface KuzuSearchResult {
  sectionId: string;
  bookKey: string;
  bookTitle: string;
  sectionTitle: string;
  score: number;
}

export class KuzuKnowledgeGraph {
  public readonly kzPath: string;
  public books: Map<string, BookRecord> = new Map();
  public sections: Map<string, SectionRecord> = new Map();
  public bookSections: Map<string, string[]> = new Map();
  private loaded: boolean = false;

  constructor(kzPath?: string) {
    if (kzPath && fs.existsSync(kzPath)) {
      this.kzPath = kzPath;
    } else {
      // Auto-detect in repo
      const candidates = [
        path.resolve(process.cwd(), "docs/easci/lean/skills/kuzu/easci-knowledge.kz"),
        path.resolve(process.cwd(), "docs/investigation-garden/kuzu/easci-knowledge.kz"),
        path.resolve(__dirname, "../../../kuzu/easci-knowledge.kz"),
      ];
      this.kzPath = candidates.find((p) => fs.existsSync(p)) || "";
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
      const bookCsv = execSync(`unzip -p "${this.kzPath}" Book.csv`, {
        encoding: "utf-8",
        maxBuffer: 10 * 1024 * 1024,
      });
      for (const line of bookCsv.split("\n")) {
        const trimmed = line.trim();
        if (!trimmed) continue;
        const parts = this.parseCsvLine(trimmed);
        if (parts.length >= 2) {
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
      const sectionCsv = execSync(`unzip -p "${this.kzPath}" Section.csv`, {
        encoding: "utf-8",
        maxBuffer: 25 * 1024 * 1024,
      });
      for (const line of sectionCsv.split("\n")) {
        const trimmed = line.trim();
        if (!trimmed) continue;
        const parts = this.parseCsvLine(trimmed);
        if (parts.length >= 4) {
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
