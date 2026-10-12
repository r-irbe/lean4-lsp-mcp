/**
 * content_limits.ts - the one byte/line bound on document content this
 * server hands a language server.
 *
 * Ported from the pi-lens fork's clients/lsp/content-limits.ts (issue
 * #3405 class): the bound must live in ONE place rather than be a
 * convention each new writer must remember, because a second writer
 * that touches with `includeText` serializes the same unbounded string
 * into another JSON-RPC frame.
 *
 * Lean-appropriate defaults: the byte bound matches pi-lens (2 MiB);
 * the line bound is looser than pi-lens's 5,000 because generated Lean
 * modules legitimately exceed it (EASCI's generated namespaces).
 * Override with LSP_CONTENT_LIMIT_BYTES / LSP_CONTENT_LIMIT_LINES.
 *
 * Strict 7-bit ASCII only (INV-001).
 */

import { Buffer } from "node:buffer";
import { env } from "node:process";

const DEFAULT_BYTES = 2 * 1024 * 1024;
const DEFAULT_LINES = 100_000;

function positiveIntEnv(name: string, fallback: number): number {
  const raw = env[name];
  if (!raw) return fallback;
  const n = Number(raw);
  return Number.isFinite(n) && n > 0 ? Math.floor(n) : fallback;
}

export interface LspContentLimitVerdict {
  exceeded: boolean;
  bytes: number;
  lines: number;
  limitBytes: number;
  limitLines: number;
}

/** Thrown by the document-sync seam when a file exceeds the bounds. */
export class ContentLimitError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "ContentLimitError";
  }
}

export function contentLimitBounds(): { limitBytes: number; limitLines: number } {
  return {
    limitBytes: positiveIntEnv("LSP_CONTENT_LIMIT_BYTES", DEFAULT_BYTES),
    limitLines: positiveIntEnv("LSP_CONTENT_LIMIT_LINES", DEFAULT_LINES),
  };
}

export function exceedsLspContentLimits(content: string): LspContentLimitVerdict {
  const { limitBytes, limitLines } = contentLimitBounds();
  const bytes = Buffer.byteLength(content, "utf-8");
  const lines = content.length === 0 ? 0 : content.split("\n").length;
  return {
    exceeded: bytes > limitBytes || lines > limitLines,
    bytes,
    lines,
    limitBytes,
    limitLines,
  };
}
