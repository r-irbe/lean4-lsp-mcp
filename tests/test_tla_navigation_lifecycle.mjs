// 100% offline exhaustive BFS verifier for formal/navigation-lifecycle/NavigationLifecycle.tla
// and its 5 .cfg ratchets (NavLifecycleAsBuilt + 4 mutants including MutNavSpawnBeforeAdmission).
import assert from "node:assert/strict";
import { test } from "node:test";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
const formalDir = path.join(here, "..", "formal", "navigation-lifecycle");
const tlaPath = path.join(formalDir, "NavigationLifecycle.tla");

const DEFAULT_SWITCHES = Object.freeze({
  NavGateBeforeSpawn: true,
  NavGateBeforeSpawnOff: false,
  NavEntryCapture: true,
  NavEntryCaptureOff: false,
  NavBeforeReset: true,
  NavBeforeResetOff: false,
  NavNoDropSurvivor: true,
  NavNoDropSurvivorOff: false,
});

const MAX_STEPS = 2;

function parseCfg(cfgPath) {
  const raw = fs.readFileSync(cfgPath, "utf-8");
  const modMatch = raw.match(/^\\\*\s*module:\s*([A-Za-z_]\w*)\s*$/m);
  const expMatch = raw.match(/^\\\*\s*expect:\s*(.+?)\s*$/m);
  const invMatch = raw.match(/^INVARIANTS\s+(.+)$/m);
  assert.ok(modMatch, `missing module header in ${cfgPath}`);
  assert.ok(expMatch, `missing expect header in ${cfgPath}`);
  assert.ok(invMatch, `missing INVARIANTS in ${cfgPath}`);

  const switches = { ...DEFAULT_SWITCHES };
  for (const m of raw.matchAll(/^\s*([A-Za-z_]\w*)\s*<-\s*([A-Za-z_]\w*)\s*$/gm)) {
    const [, lhs, rhs] = m;
    assert.ok(lhs in switches, `unknown LHS constant ${lhs} in ${cfgPath}`);
    assert.ok(rhs in switches, `unknown RHS constant ${rhs} in ${cfgPath}`);
    switches[lhs] = switches[rhs];
  }
  return {
    file: path.basename(cfgPath),
    module: modMatch[1],
    expect: expMatch[1].trim(),
    invariants: invMatch[1].trim().split(/\s+/),
    switches,
  };
}

function initialStates() {
  const out = [];
  for (const admValid of [true, false]) {
    for (const navRouteKind of ["live", "offline"]) {
      out.push({
        admValid,
        admGen: 1,
        mgrGen: 1,
        ileanGen: 1,
        navPhase: "Idle",
        navRouteKind,
        navAdm: 1,
        navMgrGen: 1,
        navIleanGen: 1,
        navBoundarySeen: false,
        spawnedBeforeGate: false,
        survPhase: "Idle",
        survDropped: false,
      });
    }
  }
  return out;
}

const INFLIGHT_PHASES = new Set(["AdmissionChecked", "RouteBound", "SessionEnsured", "Requested"]);

function nextStates(s, sw) {
  const next = [];

  // CheckAdmission
  if (s.navPhase === "Idle") {
    if (s.admValid) {
      next.push({
        ...s,
        navPhase: "AdmissionChecked",
        navAdm: s.admGen,
        navIleanGen: s.ileanGen,
        navBoundarySeen: false,
      });
    } else {
      next.push({ ...s, navPhase: "Refused" });
    }
  }

  // MutSpawnBeforeAdmission
  if (!sw.NavGateBeforeSpawn && s.navPhase === "Idle") {
    next.push({
      ...s,
      navPhase: "SessionEnsured",
      spawnedBeforeGate: true,
      navAdm: s.admGen,
      navMgrGen: s.mgrGen,
      navIleanGen: s.ileanGen,
      navBoundarySeen: false,
    });
  }

  // BindWarmRoute
  if (s.navPhase === "AdmissionChecked") {
    if (s.admValid && s.navAdm === s.admGen) {
      next.push({ ...s, navPhase: "RouteBound", navMgrGen: s.mgrGen });
    } else {
      next.push({ ...s, navPhase: "Refused" });
    }
  }

  // EnsureSession
  if (s.navPhase === "RouteBound") {
    if (s.admValid && s.navAdm === s.admGen && s.navMgrGen === s.mgrGen) {
      next.push({ ...s, navPhase: "SessionEnsured" });
    } else {
      next.push({ ...s, navPhase: "Refused" });
    }
  }

  // SendRequest
  if (s.navPhase === "SessionEnsured") {
    next.push({ ...s, navPhase: "Requested" });
  }

  // ReAdmitContext
  if (s.admGen <= MAX_STEPS) {
    for (const admValid of [true, false]) {
      next.push({
        ...s,
        admGen: s.admGen + 1,
        mgrGen: s.mgrGen <= MAX_STEPS ? s.mgrGen + 1 : s.mgrGen,
        ileanGen: s.ileanGen + 1,
        admValid,
        navBoundarySeen: INFLIGHT_PHASES.has(s.navPhase) ? true : s.navBoundarySeen,
      });
    }
  }

  // ManagerReset
  if (s.mgrGen <= MAX_STEPS) {
    next.push({
      ...s,
      mgrGen: s.mgrGen + 1,
      ileanGen: sw.NavBeforeReset ? s.ileanGen + 1 : s.ileanGen,
      navBoundarySeen: INFLIGHT_PHASES.has(s.navPhase) ? true : s.navBoundarySeen,
    });
  }

  // ResolveRequest
  if (s.navPhase === "Requested") {
    const effAdm = sw.NavEntryCapture ? s.navAdm : s.admGen;
    const effMgrGen = sw.NavEntryCapture ? s.navMgrGen : s.mgrGen;
    const effIleanGen = sw.NavEntryCapture ? s.navIleanGen : s.ileanGen;
    const routeCurrent =
      s.navRouteKind === "live"
        ? effMgrGen === s.mgrGen && effIleanGen === s.ileanGen
        : effIleanGen === s.ileanGen;
    const isCurrent = s.admValid && effAdm === s.admGen && routeCurrent;
    next.push({ ...s, navPhase: isCurrent ? "Served" : "Refused" });
  }

  // SurvivorNavigate
  if (s.survPhase === "Idle" && s.admValid) {
    if (sw.NavNoDropSurvivor) {
      next.push({ ...s, survPhase: "Served", survDropped: false });
    } else {
      next.push({ ...s, survPhase: "Refused", survDropped: true });
    }
  }

  return next;
}

const INVARIANTS = {
  NoSpawnBeforeAdmission: (s) => !s.spawnedBeforeGate,
  NoStaleNavigationServe: (s) => !(s.navBoundarySeen && s.navPhase === "Served"),
  NoDropSurvivorNavigation: (s) => !s.survDropped,
};

function stateKey(s) {
  return `${s.admValid ? 1 : 0}|${s.admGen}|${s.mgrGen}|${s.ileanGen}|${s.navPhase}|${s.navRouteKind}|${s.navAdm}|${s.navMgrGen}|${s.navIleanGen}|${s.navBoundarySeen ? 1 : 0}|${s.spawnedBeforeGate ? 1 : 0}|${s.survPhase}|${s.survDropped ? 1 : 0}`;
}

function runBfsModelCheck(cfg) {
  const visited = new Set();
  const queue = [];
  for (const init of initialStates()) {
    const k = stateKey(init);
    if (!visited.has(k)) {
      visited.add(k);
      queue.push(init);
    }
  }

  let head = 0;
  while (head < queue.length) {
    const s = queue[head++];
    for (const invName of cfg.invariants) {
      const pred = INVARIANTS[invName];
      assert.ok(pred, `unknown invariant ${invName}`);
      if (!pred(s)) {
        return { verdict: `violated ${invName}`, explored: visited.size, witness: s };
      }
    }
    for (const ns of nextStates(s, cfg.switches)) {
      const k = stateKey(ns);
      if (!visited.has(k)) {
        visited.add(k);
        queue.push(ns);
      }
    }
  }
  return { verdict: "pass", explored: visited.size, witness: null };
}

await test("NavigationLifecycle.tla declares MCP state machine, invariants, switches, and recorded pi-lens delta", () => {
  const tla = fs.readFileSync(tlaPath, "utf-8");
  for (const token of [
    "MODULE NavigationLifecycle",
    "Recorded architectural delta from `pi-lens`",
    "pending bootstrap reset",
    "Idle -> AdmissionChecked -> RouteBound -> SessionEnsured",
    "NavGateBeforeSpawn",
    "NavEntryCapture",
    "NavBeforeReset",
    "NavNoDropSurvivor",
    "NoSpawnBeforeAdmission",
    "NoStaleNavigationServe",
    "NoDropSurvivorNavigation",
  ]) {
    assert.ok(tla.includes(token), `NavigationLifecycle.tla missing expected token: ${token}`);
  }
});

await test("all 5 NavigationLifecycle .cfg ratchets match exhaustive BFS model checking (pass + 4 killed mutants)", () => {
  const cfgFiles = fs
    .readdirSync(formalDir)
    .filter((f) => f.endsWith(".cfg"))
    .sort();
  assert.deepEqual(cfgFiles, [
    "MutNavDropSurvivor.cfg",
    "MutNavLateCapture.cfg",
    "MutNavNoBeforeReset.cfg",
    "MutNavSpawnBeforeAdmission.cfg",
    "NavLifecycleAsBuilt.cfg",
  ]);

  for (const file of cfgFiles) {
    const cfg = parseCfg(path.join(formalDir, file));
    assert.equal(cfg.module, "NavigationLifecycle");
    const res = runBfsModelCheck(cfg);
    assert.equal(
      res.verdict,
      cfg.expect,
      `${file}: expected '${cfg.expect}', got '${res.verdict}' after ${res.explored} states`,
    );
    if (cfg.expect === "pass") {
      assert.ok(res.explored >= 100, `expected non-trivial state graph, explored ${res.explored}`);
    }
  }
});
