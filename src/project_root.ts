// src/project_root.ts
// Project-root resolution and Lean invocation planning.
//
// Why this module exists: every tool that shells out to Lean (lean_run_code,
// lean_axiom_closure, the counterexample harness) needs (a) the right project
// root and (b) `lake env lean` instead of a bare `lean`, otherwise project
// modules are not on LEAN_PATH and Lean reports `unknown module prefix 'X'`.
// A Lake project is recognised by any of the markers below - `lakefile.toml`
// is as valid as `lakefile.lean` (upstream `lake new` writes either).

import * as fs from "node:fs";
import * as path from "node:path";

/** Files/dirs that mark a directory as a Lake project root. */
export const LAKE_ROOT_MARKERS = [
  "lakefile.lean",
  "lakefile.toml",
  "lake-manifest.json",
  "packages",
] as const;

/** Toolchain pins alone identify a Lean root when no lakefile is present. */
export const TOOLCHAIN_MARKERS = ["lean-toolchain"] as const;

export type ProjectRootSource = "env" | "cwd" | "ancestor" | "toolchain-ancestor" | "none";

export interface ProjectRootResolution {
  /** Absolute project root to serve. */
  root: string;
  /** How the root was chosen; surfaced by lean_server_status for diagnosis. */
  source: ProjectRootSource;
  /** Marker file name that identified the root, or "" when none did. */
  marker: string;
}

export function findMarker(dir: string, markers: readonly string[]): string {
  for (const marker of markers) {
    try {
      if (fs.existsSync(path.join(dir, marker))) return marker;
    } catch {
      // unreadable directory: treat as no marker
    }
  }
  return "";
}

/** True when `dir` is a Lake project root (lakefile / manifest / packages). */
export function isLakeRoot(dir: string): boolean {
  return findMarker(dir, LAKE_ROOT_MARKERS) !== "";
}

function walkUp(start: string, markers: readonly string[]): { dir: string; marker: string } | null {
  let curr = path.resolve(start);
  while (true) {
    const marker = findMarker(curr, markers);
    if (marker) return { dir: curr, marker };
    const parent = path.dirname(curr);
    if (parent === curr) return null;
    curr = parent;
  }
}

/**
 * Resolve the project root to serve.
 *
 * Precedence: `LEAN_PROJECT_ROOT` (absolutised, must exist) -> cwd when it is a
 * Lake root -> nearest Lake root above cwd -> nearest `lean-toolchain` above cwd
 * -> cwd unchanged. The last case is deliberately *not* redirected to any other
 * directory: a wrong root silently points every tool at another project's build
 * tree, which is harder to debug than an honest empty project.
 */
export function resolveProjectRoot(
  cwd: string,
  env: NodeJS.ProcessEnv = process.env
): ProjectRootResolution {
  const configured = (env.LEAN_PROJECT_ROOT || "").trim();
  if (configured) {
    const abs = path.resolve(cwd, configured);
    if (fs.existsSync(abs)) {
      return { root: abs, source: "env", marker: findMarker(abs, LAKE_ROOT_MARKERS) || findMarker(abs, TOOLCHAIN_MARKERS) };
    }
  }

  const start = path.resolve(cwd);
  const ownMarker = findMarker(start, LAKE_ROOT_MARKERS);
  if (ownMarker) return { root: start, source: "cwd", marker: ownMarker };

  const lakeAncestor = walkUp(start, LAKE_ROOT_MARKERS);
  if (lakeAncestor) return { root: lakeAncestor.dir, source: "ancestor", marker: lakeAncestor.marker };

  const toolchainAncestor = walkUp(start, TOOLCHAIN_MARKERS);
  if (toolchainAncestor) {
    return { root: toolchainAncestor.dir, source: "toolchain-ancestor", marker: toolchainAncestor.marker };
  }

  return { root: start, source: "none", marker: "" };
}

export interface LeanInvocation {
  command: string;
  args: string[];
  cwd: string;
  /** "lake": `lake env lean ...` inside a Lake root; "bare": project-less `lean`. */
  via: "lake" | "bare";
}

/**
 * Plan a Lean command line for `root`.
 *
 * `lake env lean` is mandatory inside a Lake root: it supplies LEAN_PATH, the
 * pinned toolchain, and project `leanOptions`. A bare `lean` only sees the
 * toolchain's own library, so `import Spec` fails with `unknown module prefix`.
 */
export function planLeanInvocation(root: string, leanArgs: string[]): LeanInvocation {
  const cwd = path.resolve(root);
  if (isLakeRoot(cwd)) {
    return { command: "lake", args: ["env", "lean", ...leanArgs], cwd, via: "lake" };
  }
  return { command: "lean", args: leanArgs, cwd, via: "bare" };
}

const MODULE_PREFIX_RE = /unknown module prefix '([^']+)'/;
const UNKNOWN_PACKAGE_RE = /unknown package '([^']+)'/;

/**
 * Append the fix to a Lean failure that is really an environment failure.
 *
 * Returns "" when the output carries no environment-shaped error, so callers can
 * append unconditionally. UNVERIFIED-by-design: these are hints, never rewrites
 * of Lean's own message.
 */
export function explainLeanFailure(output: string, invocation: LeanInvocation): string {
  const prefixed = MODULE_PREFIX_RE.exec(output);
  if (prefixed) {
    return [
      "",
      `[hint] module '${prefixed[1]}' is not on the search path of this invocation.`,
      `       ran: ${invocation.command} ${invocation.args.join(" ")} (cwd ${invocation.cwd}, via ${invocation.via}).`,
      invocation.via === "lake"
        ? "       The root is a Lake project, so check the module name and that `lake build` has produced its .olean."
        : "       No lakefile.lean / lakefile.toml / lake-manifest.json found in the root: project modules cannot be imported.",
      "       Set LEAN_PROJECT_ROOT to the Lake project root (the dir holding lakefile.lean or lakefile.toml).",
    ].join("\n");
  }
  const pkg = UNKNOWN_PACKAGE_RE.exec(output);
  if (pkg) {
    return [
      "",
      `[hint] package '${pkg[1]}' is not in the Lake workspace of ${invocation.cwd}.`,
      "       Run `lake update` there, or set LEAN_PROJECT_ROOT to the workspace root that declares it.",
    ].join("\n");
  }
  return "";
}
