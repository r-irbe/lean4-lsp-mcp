import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { test } from "node:test";
import { McpServer } from "../src/index.ts";

test("file-scoped cone resolves homonymous declarations within their Lake root", async (t) => {
  const workspace = fs.mkdtempSync(path.join(os.tmpdir(), "cone-project-scope-"));
  t.after(() => fs.rmSync(workspace, { recursive: true, force: true }));
  function fixture(project, dependency) {
    const root = path.join(workspace, project);
    const build = path.join(root, ".lake", "build", "lib", "lean");
    fs.mkdirSync(build, { recursive: true });
    const source = path.join(root, "Submission.lean");
    fs.writeFileSync(source, "namespace Submission\ndef impl := 0\nend Submission\n");
    fs.writeFileSync(path.join(root, "lakefile.toml"), 'name = "fixture"\n');
    fs.writeFileSync(path.join(build, "Submission.ilean"), JSON.stringify({
      version: 5,
      module: "Submission",
      decls: { "Submission.impl": [1, 0, 1, 13] },
      references: {
        [JSON.stringify({ c: { m: "Submission", n: dependency } })]: {
          usages: [[1, 1, 1, 2, "Submission.impl"]],
        },
      },
    }));
    return source;
  }
  const partition = fixture("partition", "Submission.sdLoop");
  const fib = fixture("fib", "Submission.gC");
  const server = new McpServer(workspace);
  server.ileanIndex.refresh();
  for (const [filePath, expected, foreign] of [
    [partition, "Submission.sdLoop", "Submission.gC"],
    [fib, "Submission.gC", "Submission.sdLoop"],
  ]) {
    const output = JSON.parse(await server.executeTool("lean_cone_query", {
      runtimeRoot: "Submission.impl", filePath,
    }));
    const names = output.runtimeCone.declarations.map(({ name }) => name);
    assert.ok(names.includes(expected), "local compiled reference must survive");
    assert.ok(!names.includes(foreign), "sibling root leaked into file-scoped query");
  }
});
