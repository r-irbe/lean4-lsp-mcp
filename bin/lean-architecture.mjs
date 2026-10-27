// Config-driven architecture checks (tiers, layers, monolith imports, numeric
// discipline) driven by lean-project.toml. Resolution uses file path,
// header markers (-- [tier N] / -- module X), namespace and import lines on RAW
// text, so "-- [tier N]" comments are never masked away.
import fs from "node:fs";
import path from "node:path";

export function parseToml(text) {
  const root = {};
  let cur = root;
  const lines = text.split("\n");
  const strip = (s) => {
    let q = false, out = "";
    for (let i = 0; i < s.length; i++) {
      const c = s[i];
      if (c === "\\" && q) { out += c + s[++i]; continue; }
      if (c === "\"") q = !q;
      if (c === "#" && !q) break;
      out += c;
    }
    return out.trim();
  };
  const depth = (s) => {
    let d = 0, q = false;
    for (let i = 0; i < s.length; i++) {
      const c = s[i];
      if (c === "\\" && q) { i++; continue; }
      if (c === "\"") q = !q;
      else if (!q && c === "[") d++;
      else if (!q && c === "]") d--;
    }
    return d;
  };
  for (let i = 0; i < lines.length; i++) {
    let l = strip(lines[i]);
    if (!l) continue;
    let m = l.match(/^\[\[([^\]]+)\]\]$/);
    if (m) {
      const keys = m[1].trim().split(".");
      let o = root;
      keys.slice(0, -1).forEach((k) => { o = o[k] ??= {}; });
      const last = keys[keys.length - 1];
      (o[last] ??= []).push((cur = {}));
      continue;
    }
    m = l.match(/^\[([^\]]+)\]$/);
    if (m) {
      cur = root;
      m[1].trim().split(".").forEach((k) => { cur = cur[k] ??= {}; });
      continue;
    }
    m = l.match(/^("?[^=]+?"?)\s*=\s*(.*)$/);
    if (!m) continue;
    const key = m[1].trim().replace(/^"|"$/g, "");
    let val = m[2];
    while (depth(val) > 0 && i + 1 < lines.length) val += " " + strip(lines[++i]);
    try { cur[key] = JSON.parse(val.replace(/,\s*]/g, "]")); } catch { cur[key] = val; }
  }
  return root;
}

export function findConfig(startDir) {
  let d = path.resolve(startDir);
  if (fs.existsSync(d) && !fs.statSync(d).isDirectory()) d = path.dirname(d);
  for (;;) {
    for (const n of ["lean-project.toml", ".lean-analyzer.toml"]) {
      const p = path.join(d, n);
      if (fs.existsSync(p)) return p;
    }
    for (const sub of ["lean/lean-project.toml", "lean_rules/lean-project.toml"]) {
      const p = path.join(d, sub);
      if (fs.existsSync(p)) return p;
    }
    const docsDir = path.join(d, "docs");
    if (fs.existsSync(docsDir) && fs.statSync(docsDir).isDirectory()) {
      for (const e of fs.readdirSync(docsDir)) {
        const p = path.join(docsDir, e, "lean", "lean-project.toml");
        if (fs.existsSync(p)) return p;
      }
    }
    const up = path.dirname(d);
    if (up === d) return null;
    d = up;
  }
}

const FLOAT_CACHE = new Map();

export function checkArchitecture(file, raw, masked, cfg, cfgDir) {
  const out = [];
  const arch = cfg.architecture ?? {};
  const tiers = arch.tiers ?? {};
  const tierOf = new Map();
  for (const [k, mods] of Object.entries(tiers)) {
    const n = Number(k.replace(/\D/g, ""));
    if (Array.isArray(mods)) for (const m of mods) tierOf.set(m, n);
  }
  const layerOf = new Map();
  const layers = arch.layers?.order ?? [];
  if (Array.isArray(layers)) {
    layers.forEach((group, idx) => {
      if (Array.isArray(group)) for (const m of group) layerOf.set(m, idx);
    });
  }
  const absFile = path.resolve(file);
  const repoRoot = path.resolve(cfgDir, cfg.workspace?.repo_root ?? ".");
  const pkDir = cfg.workspace?.packages_dir ? path.resolve(repoRoot, cfg.workspace.packages_dir) : null;
  const rel = path.relative(repoRoot, absFile).split(path.sep);
  const inSub = pkDir ? absFile.startsWith(pkDir + path.sep) : rel.includes("packages");
  const imports = [...raw.matchAll(/^import\s+([\w.]+)/gm)].map((m) => [m[1], raw.slice(0, m.index).split("\n").length]);
  const mono = arch.monolith_module;
  const modTag = raw.match(/^[ \t]*--[ \t]*module[ \t]+([A-Z]\w*)[ \t]*$/m);
  const tierTag = raw.match(/^[ \t]*--[ \t]*\[?(?:tier|Tier)[ \t]*(\d+)\]?[ \t]*$/m);
  const hasExplicitMarker = Boolean(tierTag || (modTag && tierOf.has(modTag[1])));

  const self = (() => {
    const modComment = raw.match(/^[ \t]*--[ \t]*module[ \t]+([A-Z]\w*)/m);
    if (modComment && tierOf.has(modComment[1])) return modComment[1];
    const tierComment = raw.match(/^[ \t]*--[ \t]*\[?(?:tier|Tier)[ \t]*(\d+)\]?/m);
    if (tierComment) {
      const tn = Number(tierComment[1]);
      for (const [m, t] of tierOf.entries()) if (t === tn) return m;
    }
    for (const seg of rel) { const s = seg.replace(/\.lean$/, ""); if (tierOf.has(s)) return s; }
    const ns = masked.match(/^namespace\s+([\w.]+)/m);
    if (ns) for (const s of ns[1].split(".")) if (tierOf.has(s)) return s;
    return null;
  })();

  const projPrefix = cfg.project?.name ? cfg.project.name + "." : "";
  const selfLayerMod = (() => {
    const leanDir = path.resolve(cfgDir, cfg.project?.lean_dir ?? ".");
    if (absFile.startsWith(leanDir + path.sep)) {
      const modRel = path.relative(leanDir, absFile).replace(/\.lean$/, "").split(path.sep).join(".");
      if (layerOf.has(modRel)) return modRel;
    }
    return null;
  })();

  if (arch.forbid_monolith_in_subpackages && inSub && mono) {
    for (const [imp, line] of imports) {
      if (imp === mono || (hasExplicitMarker && imp.startsWith(mono + ".")))
        out.push({ line, ruleId: "arch-subpackage-no-monolith-import", severity: "error",
          message: `subpackage imports monolith ${mono}` });
    }
  }
  if (self) {
    const st = tierOf.get(self);
    for (const [imp, line] of imports) {
      if (mono && imp.startsWith(mono + ".") && !hasExplicitMarker) continue;
      for (const seg of imp.split(".")) {
        if (seg === self) continue;
        const t = tierOf.get(seg);
        if (t !== undefined && t > st)
          out.push({ line, ruleId: "arch-tier-backward-dependency", severity: "error",
            message: `${self} (tier ${st}) imports ${seg} (tier ${t})` });
        else if (t !== undefined && t === st && arch.enforce_horizontal_isolation &&
                 (arch.peer_groups?.[seg] ?? seg) !== (arch.peer_groups?.[self] ?? self))
          out.push({ line, ruleId: "arch-tier-horizontal-isolation", severity: "error",
            message: `${self} imports same-tier peer ${seg}` });
      }
    }
  }
  if (selfLayerMod !== null) {
    const sl = layerOf.get(selfLayerMod);
    for (const [imp, line] of imports) {
      const stripped = projPrefix && imp.startsWith(projPrefix) ? imp.slice(projPrefix.length) : imp;
      const tl = layerOf.get(stripped);
      if (tl !== undefined && tl > sl)
        out.push({ line, ruleId: "arch-layer-backward-dependency", severity: "error",
          message: `${selfLayerMod} (layer ${sl}) imports ${stripped} (layer ${tl})` });
    }
  }
  const nd = cfg.numeric_discipline;
  if (nd && (nd.scope !== "subpackages" || inSub)) {
    const names = nd.forbid_float_types ?? [];
    if (!FLOAT_CACHE.has(names.join())) FLOAT_CACHE.set(names.join(), new RegExp(`\\b(${names.join("|")})\\b`));
    const re = FLOAT_CACHE.get(names.join());
    masked.split("\n").forEach((l, i) => {
      if (names.length && re.test(l))
        out.push({ line: i + 1, ruleId: "arch-numeric-discipline", severity: nd.severity ?? "warning",
          message: `forbidden float type; prefer ${nd.preferred_alternative ?? "scaled integers"}` });
    });
  }
  return out;
}
