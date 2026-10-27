import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { runScan } from "../bin/lean-rules.js";

test("config-driven tier, monolith and float checks (no comment markers needed)", () => {
  const d = fs.mkdtempSync(path.join(os.tmpdir(), "arch-"));
  fs.writeFileSync(path.join(d, "lean-project.toml"), `
[workspace]
packages_dir = "packages"
[architecture]
monolith_module = "Mono"
forbid_monolith_in_subpackages = true
[architecture.tiers]
tier_0 = ["Base"]
tier_1 = ["Top"]
[numeric_discipline]
forbid_float_types = ["Float"]
severity = "warning"
scope = "subpackages"
`);
  const f = path.join(d, "packages", "Base");
  fs.mkdirSync(f, { recursive: true });
  fs.writeFileSync(path.join(f, "A.lean"), "import Mono\nimport Top.X\ndef x : Float := 1.0\n");
  const r = runScan({ rulesDirs: [], targets: [d] });
  const ids = r.findings.map((x) => x.ruleId);
  for (const id of ["arch-subpackage-no-monolith-import", "arch-tier-backward-dependency", "arch-numeric-discipline"])
    assert.ok(ids.includes(id), id);
});
