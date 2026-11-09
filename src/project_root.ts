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
import { createHash } from "node:crypto";

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

function walkUp(start: string, markers: readonly string[], ceiling?: string): { dir: string; marker: string } | null {
  let curr = path.resolve(start);
  while (true) {
    const marker = findMarker(curr, markers);
    if (marker) return { dir: curr, marker };
    if (ceiling && curr === path.resolve(ceiling)) return null;
    const parent = path.dirname(curr);
    if (parent === curr) return null;
    curr = parent;
  }
}

/**
 * Resolve the project root to serve.
 *
 * Precedence: `LEAN_PROJECT_ROOT` (absolutised, must exist) -> nearest Lean
 * boundary (Lake marker or toolchain pin) -> cwd unchanged. A nested pin is a
 * boundary: an outer Lake environment must not silently select its compiler. The last case is deliberately *not* redirected to any other
 * directory: a wrong root silently points every tool at another project's build
 * tree, which is harder to debug than an honest empty project.
 */
export function resolveProjectRoot(
  cwd: string,
  env: NodeJS.ProcessEnv = process.env,
  ceiling?: string
): ProjectRootResolution {
  const configured = (env.LEAN_PROJECT_ROOT || "").trim();
  if (configured) {
    const abs = path.resolve(cwd, configured);
    if (fs.existsSync(abs)) {
      return { root: abs, source: "env", marker: findMarker(abs, LAKE_ROOT_MARKERS) || findMarker(abs, TOOLCHAIN_MARKERS) };
    }
  }

  const start = path.resolve(cwd);
  const nearest = walkUp(start, [...LAKE_ROOT_MARKERS, ...TOOLCHAIN_MARKERS], ceiling);
  if (nearest) {
    const source = nearest.marker === "lean-toolchain" ? "toolchain-ancestor"
      : nearest.dir === start ? "cwd" : "ancestor";
    return { root: nearest.dir, source, marker: nearest.marker };
  }

  return { root: start, source: "none", marker: "" };
}

/** Stat identity of an admitted compiler; in-place replacement changes ino/size/ctime. */
export interface LeanCompilerIdentity {
  readonly realpath: string;
  readonly symlink: boolean;
  readonly dev: string;
  readonly ino: string;
  readonly size: string;
  readonly mtimeNs: string;
  readonly ctimeNs: string;
}

export function captureLeanCompilerIdentity(compilerPath: string): LeanCompilerIdentity {
  const lst = fs.lstatSync(compilerPath, { bigint: true });
  const st = fs.statSync(compilerPath, { bigint: true });
  return {
    realpath: fs.realpathSync(compilerPath),
    symlink: lst.isSymbolicLink(),
    dev: st.dev.toString(), ino: st.ino.toString(), size: st.size.toString(),
    mtimeNs: st.mtimeNs.toString(), ctimeNs: st.ctimeNs.toString(),
  };
}

/** True only when the compiler is still the same non-symlink file that was admitted. */
export function isLeanCompilerIdentityCurrent(compilerPath: string, expected: LeanCompilerIdentity): boolean {
  try {
    const now = captureLeanCompilerIdentity(compilerPath);
    return !now.symlink && JSON.stringify(now) === JSON.stringify(expected);
  } catch { return false; }
}

/** Worker identity includes the pin's contents, not just its directory/name. */
export function leanEnvironmentFingerprint(
  root: string,
  command: string,
  args: readonly string[],
  env: NodeJS.ProcessEnv = process.env,
  context?: LeanContext
): string {
  const pin = walkUp(root, TOOLCHAIN_MARKERS);
  let toolchain = "";
  try { toolchain = pin ? fs.readFileSync(path.join(pin.dir, pin.marker), "utf8") : ""; }
  catch { toolchain = "unreadable"; }
  let manifest = "";
  try {
    manifest = createHash("sha256").update(fs.readFileSync(path.join(path.resolve(root), "lake-manifest.json"))).digest("hex");
  } catch { manifest = ""; }
  return createHash("sha256").update(JSON.stringify({
    root: path.resolve(root), command, args, pin: pin?.dir, toolchain, context, manifest,
    compiler: context ? captureLeanCompilerIdentity(context.compilerPath) : undefined,
    // Implicit invocations still depend on these inherited selection inputs.
    path: context ? undefined : env.PATH,
    elan: context ? undefined : env.ELAN_TOOLCHAIN,
    modules: context ? context.moduleRoots : env.LEAN_PATH,
  })).digest("hex");
}

/**
 * Elan shim support. `~/.elan/bin/lean` is a symlink to the `elan` multiplexer,
 * which picks a toolchain from argv0/env/the nearest lean-toolchain, so it can
 * never be admitted as-is. Instead of trusting that dispatch, resolve the shim
 * to the exact direct binary for the declared `targetVersion`:
 *   <elanHome>/toolchains/leanprover--lean4---v<targetVersion>/bin/lean
 * The result is then admitted like any direct compiler (non-symlink, version
 * checked at use). Only a symlink whose real target is a file named `elan`
 * qualifies; any other symlink stays refused. Returns undefined otherwise.
 */
export function elanShimBinDir(compilerPath: string): string | undefined {
  try {
    const abs = path.resolve(compilerPath);
    // A shim is either a symlink to a file named `elan`, or (what elan itself
    // installs on Linux) a hardlink/copy sharing dev+ino with the sibling `elan`.
    if (fs.lstatSync(abs).isSymbolicLink()) {
      const shimTarget = fs.realpathSync(abs);
      return path.basename(shimTarget).replace(/\.exe$/i, "") === "elan" ? path.dirname(shimTarget) : undefined;
    }
    if (path.basename(abs).replace(/\.exe$/i, "") === "elan") return undefined;
    const sibling = path.join(path.dirname(abs), path.basename(abs).toLowerCase().endsWith(".exe") ? "elan.exe" : "elan");
    const a = fs.statSync(abs, { bigint: true });
    const b = fs.statSync(sibling, { bigint: true });
    return a.dev === b.dev && a.ino === b.ino ? path.dirname(abs) : undefined;
  } catch {
    return undefined;
  }
}

export function resolveElanShim(compilerPath: string, targetVersion: string): string | undefined {
  try {
    const abs = path.resolve(compilerPath);
    const binDir = elanShimBinDir(abs);
    if (!binDir) return undefined;
    const elanHome = path.dirname(binDir);
    const toolchains = path.join(elanHome, "toolchains");
    const direct = path.join(toolchains, `leanprover--lean4---v${targetVersion}`, "bin", path.basename(abs));
    if (fs.lstatSync(direct).isSymbolicLink()) return undefined;
    const real = fs.realpathSync(direct);
    return real === path.resolve(direct) && real.startsWith(fs.realpathSync(toolchains) + path.sep) ? real : undefined;
  } catch {
    return undefined;
  }
}

/** Explicit host/exec-caller admission, never loaded implicitly from a project. */
export interface LeanContext {
  readonly compilerPath: string;
  readonly targetVersion: string;
  readonly moduleRoots: readonly string[];
}

export const LEAN_CONTEXT_SCHEMA = {
  type: "object",
  additionalProperties: false,
  properties: {
    compilerPath: { type: "string", description: "Trusted absolute path to an installed lean executable" },
    targetVersion: { type: "string", description: "Exact Lean version, e.g. 4.35.0 or 4.36.0-rc1" },
    moduleRoots: { type: "array", maxItems: 32, items: { type: "string" }, description: "Explicitly admitted absolute module directories; replaces inherited LEAN_PATH" },
  },
  required: ["compilerPath", "targetVersion", "moduleRoots"],
} as const;

export function validateLeanContext(value: unknown): LeanContext {
  const fail = (reason: string): never => { throw new Error(`Invalid Lean context: ${reason}`); };
  if (!value || typeof value !== "object" || Array.isArray(value)) return fail("expected an object");
  const record = value as Record<string, unknown>;
  if (Object.keys(record).some((key) => !["compilerPath", "targetVersion", "moduleRoots"].includes(key))) {
    return fail("only compilerPath, targetVersion and moduleRoots are admitted");
  }
  const absolutePath = (input: unknown): input is string =>
    typeof input === "string" && input.length <= 4096 && !/[\0\r\n]/.test(input) && path.isAbsolute(input);
  if (!absolutePath(record.compilerPath) || !/^lean(?:\.exe)?$/i.test(path.basename(record.compilerPath))) {
    return fail("compilerPath must name an absolute lean executable");
  }
  if (typeof record.targetVersion !== "string" || !/^4\.\d+\.\d+(?:-[a-z]+\d+)?$/.test(record.targetVersion) || record.targetVersion.length > 64) {
    return fail("targetVersion must be an exact Lean 4 version");
  }
  if (!Array.isArray(record.moduleRoots) || record.moduleRoots.length > 32 ||
      record.moduleRoots.some((root) => !absolutePath(root) || root.includes(path.delimiter))) {
    return fail("moduleRoots must be at most 32 absolute search-path-safe directories");
  }
  try {
    const resolvedShim = resolveElanShim(record.compilerPath, record.targetVersion);
    if (!resolvedShim && elanShimBinDir(record.compilerPath)) {
      return fail(`elan shim cannot be admitted: toolchain leanprover--lean4---v${record.targetVersion} is not installed as a direct binary; install it or admit the toolchain's own bin/lean`);
    }
    const requested = resolvedShim ?? record.compilerPath;
    if (!fs.statSync(requested).isFile()) return fail("compilerPath is not a file");
    fs.accessSync(requested, fs.constants.X_OK);
    const compilerPath = fs.realpathSync(requested);
    if (compilerPath !== path.resolve(requested)) return fail("compiler symlink paths unsupported; admit a direct installed lean binary without argv0-dependent indirection");
    const moduleRoots = record.moduleRoots.map((root: string) => {
      if (!fs.statSync(root).isDirectory()) return fail("module root is not a directory");
      const resolved = fs.realpathSync(root);
      if (resolved.includes(path.delimiter)) return fail("canonical module root contains a search-path delimiter");
      return resolved;
    });
    return Object.freeze({
      compilerPath,
      targetVersion: record.targetVersion,
      moduleRoots: Object.freeze(moduleRoots),
    });
  } catch (error) {
    if (error instanceof Error && error.message.startsWith("Invalid Lean context:")) throw error;
    return fail("compiler or module root is unavailable; admit existing installed paths");
  }
}

export interface LeanInvocation {
  command: string;
  args: string[];
  cwd: string;
  /** Explicit contexts use only the admitted compiler and module roots. */
  via: "lake" | "bare" | "explicit";
  context?: LeanContext;
  env?: { LEAN_PATH: string };
}

/**
 * Plan a Lean command line for `root`.
 *
 * `lake env lean` is mandatory inside a Lake root: it supplies LEAN_PATH, the
 * pinned toolchain, and project `leanOptions`. A bare `lean` only sees the
 * toolchain's own library, so `import Spec` fails with `unknown module prefix`.
 */
export function planLeanInvocation(root: string, leanArgs: string[], trustedContext?: LeanContext): LeanInvocation {
  const cwd = path.resolve(root);
  if (trustedContext) {
    const context = validateLeanContext(trustedContext);
    return { command: context.compilerPath, args: leanArgs, cwd, via: "explicit", context,
      env: { LEAN_PATH: context.moduleRoots.join(path.delimiter) } };
  }
  if (isLakeRoot(cwd)) {
    return { command: "lake", args: ["env", "lean", ...leanArgs], cwd, via: "lake" };
  }
  return { command: "lean", args: leanArgs, cwd, via: "bare" };
}

/** Fixed selection overrides only; no caller-supplied arbitrary environment. */
export function leanInvocationEnv(invocation: LeanInvocation, inherited: NodeJS.ProcessEnv = process.env): NodeJS.ProcessEnv {
  if (!invocation.context) return inherited;
  const env: NodeJS.ProcessEnv = { ...inherited, ...invocation.env };
  delete env.LEAN_SYSROOT;
  delete env.LEAN_SRC_PATH;
  delete env.ELAN_TOOLCHAIN;
  return env;
}

/** Version evidence is a separate environment verdict, never a source verdict. */
export function explainLeanVersion(output: string, context: LeanContext): string {
  const observed = /\bversion\s+(4\.\d+\.\d+(?:-[a-z]+\d+)?)(?=[,\s)]|$)/.exec(output)?.[1];
  return observed === context.targetVersion ? ""
    : `environment_unavailable: declared Lean ${context.targetVersion}, observed ${observed || "unrecognized version"}; select the exact installed compiler before checking source`;
}

const MODULE_PREFIX_RE = /unknown module prefix '([^']+)'/;
const UNKNOWN_PACKAGE_RE = /unknown package '([^']+)'/;
const UNKNOWN_TACTIC_RE = /unknown tactic '(ring_nf|ring|nlinarith|linarith|norm_num|positivity|aesop|tauto|field_simp|zify|push_cast)'/;

const CORE_ONLY_TACTIC_HINTS: Record<string, string> = {
  ring: "Use `omega` for linear Nat/Int equalities, `ac_rfl` for associative-commutative monoids, `grind`, or explicit `simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm]` in Core-only environments.",
  ring_nf: "Use `omega` for linear Nat/Int arithmetic, `grind`, or `simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm]` in Core-only environments.",
  linarith: "Use `omega` for linear Nat/Int inequalities and equalities in Core-only Lean 4 without Mathlib.",
  nlinarith: "Introduce intermediate nonlinear bounds with `have` (e.g. `Nat.mul_le_mul`), then discharge the linear obligation with `omega`.",
  norm_num: "Use `decide` (or `decide +kernel`) for closed decidable propositions or `rfl` for definitional reduction; avoid `native_decide` on contest-gated paths.",
  positivity: "Use `omega`, `Nat.zero_le`, or `Nat.succ_pos` in Core-only environments.",
  aesop: "Use `grind`, `simp_all`, `decide`, or explicit `cases`/`constructor` splits in Core-only environments.",
  tauto: "Use `decide` on decidable propositions, `by_cases`, or `grind` in Core-only environments.",
  field_simp: "Clear denominators manually with multiplication lemmas before applying `omega` or `grind` in Core-only environments.",
  zify: "Lift `Nat` subtraction guards explicitly using `Int.ofNat` lemmas followed by `omega`.",
  push_cast: "Use `simp` with `Int.ofNat_add` / `Int.ofNat_mul` followed by `omega` in Core-only environments.",
};

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
      invocation.via === "explicit"
        ? `       Check the module name and compatible .olean files in the explicitly admitted module roots: ${invocation.context!.moduleRoots.join(", ") || "(none)"}.`
        : invocation.via === "lake"
        ? "       The root is a Lake project, so check the module name and that `lake build` has produced its .olean."
        : "       No lakefile.lean / lakefile.toml / lake-manifest.json found in the root: project modules cannot be imported without an explicit admitted context.",
      invocation.via === "explicit"
        ? "       This is a search-path/artifact failure, not proof that the source is invalid for another target."
        : "       Set LEAN_PROJECT_ROOT to the Lake project root (the dir holding lakefile.lean or lakefile.toml), or supply a trusted exact Lean context.",
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
  const tac = UNKNOWN_TACTIC_RE.exec(output);
  if (tac) {
    const tacName = tac[1];
    const replacement = CORE_ONLY_TACTIC_HINTS[tacName] || "Use Core/Init tactics (`omega`, `grind`, `simp`, `decide`) or import the declaring Mathlib tactic module.";
    return [
      "",
      `[hint] tactic '${tacName}' is a Mathlib tactic not imported in this environment.`,
      `       Core-only alternative: ${replacement}`,
    ].join("\n");
  }
  return "";
}
