// Restart and grouping contracts exercise the real analyzer and editing boundary.
import assert from "node:assert/strict";
import { test } from "node:test";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { runKernelVerifiedAutoSlim } from "../src/autoslim.ts";
import { parseAutoSlimCliArgs } from "../bin/lean-autoslim.js";
import { McpServer, FileWorkerManager, TOOL_DEFINITIONS } from "../src/index.ts";
import { AutoSlimJournal, contentHash } from "../src/autoslim_checkpoint.ts";
import { verifyProofGroups } from "../src/autoslim_engine.ts";

test("inconclusive verifier evidence stays pending and never publishes a subset", async () => {
  const f = fixture(); let calls = 0;
  try {
    const partial = await runKernelVerifiedAutoSlim(f.root, { ...opts(f), apply: true, groupSize: 1,
      lspVerifier: async () => ++calls === 1 ? clean() : ({ok:false,errorCount:1,warningCount:0, firstIssue:"LSP fileProgress did not complete within 10ms"}) });
    assert.equal(partial.completed, false);
    assert.equal(partial.stopReason, "verification-inconclusive");
    assert.equal(partial.rejectedCount, 0);
    assert.equal(partial.applied, false);
    assert.equal(fs.readFileSync(f.file, "utf8"), f.source);
    const resumed = await runKernelVerifiedAutoSlim(f.root, opts(f));
    assert.equal(resumed.completed, true);
    assert.equal(resumed.verifiedCount, 4);
  } finally { fs.rmSync(f.root, {recursive:true,force:true}); }
});

test("checkpoint refuses symlink ancestors and recovers an unfinished UTF-8 tail", () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "autoslim-journal-"));
  try {
    const id = contentHash("identity");
    fs.mkdirSync(path.join(root,"real")); fs.symlinkSync(path.join(root,"real"),path.join(root,"alias"));
    assert.throws(() => new AutoSlimJournal(path.join(root,"alias","nested"),id), /symlink/i);
    const journal = new AutoSlimJournal(path.join(root,"progress"),id);
    journal.accept("candidate", "by grind");
    fs.appendFileSync(journal.filePath, Buffer.from([123,34,120,34,58,34,0xce]));
    assert.equal(new AutoSlimJournal(path.join(root,"progress"),id).accepted.size,1);
    fs.appendFileSync(journal.filePath,"broken\n");
    assert.throws(() => new AutoSlimJournal(path.join(root,"progress"),id),/Corrupt/);
    assert.equal(new AutoSlimJournal(path.join(root,"progress"),id,true).accepted.size,0);
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test("successful group decisions survive interruption before individual receipts", async () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "autoslim-group-"));
  const journal = new AutoSlimJournal(root,contentHash("group-identity"));
  let calls=0;
  journal.accept = () => { throw new Error("interrupt before individual receipt"); };
  try {
    try { await verifyProofGroups({proposals:["a","b","c","d"].map(id=>({id,tactics:["by grind"]})),
      render: choices=>JSON.stringify([...choices]),verify:async()=>{calls++;return clean();},journal,groupSize:4,maxAttempts:1}); } catch (e) {assert.match(e.message,/interrupt/);}
    const restored = new AutoSlimJournal(root,contentHash("group-identity"));
    assert.equal(restored.accepted.size,4);
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test("multi-file manager shares one total verification attempt budget", async () => {
  const f=fixture(); const manager=new FileWorkerManager(f.root); const received=[];
  manager.autoSlimFile=async options=>{received.push(options.maxVerificationAttempts);return JSON.stringify({completed:true,applied:false,verifiedCount:0,rejectedCount:0,verificationTimeMs:0,verificationAttempts:2});};
  try {await manager.autoSlimFiles({filePaths:[f.file,path.join(f.root,"Other.lean")],maxVerificationAttempts:2});assert.deepEqual(received,[2,0]);}
  finally {manager.dispose();fs.rmSync(f.root,{recursive:true,force:true});}
});

test("a lost per-file receipt cannot grant the next file extra batch attempts", async () => {
  const f=fixture(); const manager=new FileWorkerManager(f.root); const received=[];
  manager.autoSlimFile=async options=>{received.push(options.maxVerificationAttempts);if(received.length===1) throw new Error("receipt interrupted");return JSON.stringify({completed:false,applied:false,verifiedCount:0,rejectedCount:0,verificationTimeMs:0,verificationAttempts:0});};
  try {await manager.autoSlimFiles({filePaths:[f.file,path.join(f.root,"Other.lean")],maxVerificationAttempts:2});assert.deepEqual(received,[2,0]);}
  finally {manager.dispose();fs.rmSync(f.root,{recursive:true,force:true});}
});

test("external LEAN_PATH and symlinked compiled dependencies invalidate checkpoints", async () => {
  const before = process.env.LEAN_PATH;
  try {
    for (const kind of ["environment", "symlink"]) {
      const f=fixture(); const external=fs.mkdtempSync(path.join(os.tmpdir(),"autoslim-external-"));
      const artifact=path.join(external,"External.olean"); fs.writeFileSync(artifact,"old compiled dependency");
      try {
        if(kind==="environment") process.env.LEAN_PATH=external;
        else { delete process.env.LEAN_PATH; const built=path.join(f.root,".lake/build/lib/lean");fs.mkdirSync(built,{recursive:true});fs.symlinkSync(external,path.join(built,"External")); }
        const partial=await runKernelVerifiedAutoSlim(f.root,{...opts(f),maxVerificationAttempts:1});
        fs.writeFileSync(artifact,"new compiled dependency");
        const resumed=await runKernelVerifiedAutoSlim(f.root,opts(f));
        assert.notEqual(resumed.checkpointPath,partial.checkpointPath,kind);
        assert.equal(resumed.resumedCandidates,0,kind);
      }finally{fs.rmSync(f.root,{recursive:true,force:true});fs.rmSync(external,{recursive:true,force:true});}
    }
  }finally{if(before===undefined) delete process.env.LEAN_PATH;else process.env.LEAN_PATH=before;}
});

test("CLI and MCP forward checkpoint, fresh, group and attempt controls", async () => {
  const args = parseAutoSlimCliArgs(["Sample.lean", "--checkpoint-dir", "/tmp/checkpoints", "--fresh", "--group-size", "3", "--max-attempts", "0"]);
  assert.equal(args.checkpointDir, "/tmp/checkpoints");
  assert.equal(args.resume, false);
  const ranked = parseAutoSlimCliArgs(["Sample.lean", "--ranking-history", "/tmp/history.json", "--source-order"]);
  assert.equal(ranked.rankingHistoryPath,"/tmp/history.json");
  assert.equal(ranked.rankBySize,false);
  assert.equal(args.groupSize, 3);
  assert.equal(args.maxVerificationAttempts, 0);
  for (const value of ["-1", "2x", "1.5", "33"]) assert.throws(() => parseAutoSlimCliArgs(["Sample.lean", "--group-size", value]));
  const f = fixture();
  const server = new McpServer(f.root);
  let received;
  server.lakeManager.autoSlimFile = async options => { received = options; return "{}"; };
  try {
    await server.executeTool("lean_autoslim", { filePath: f.file, checkpointDir: f.checkpointDir, resume: false, groupSize: 3, maxVerificationAttempts: 0, rankingHistoryPath:"/tmp/history.json",rankBySize:false });
    assert.equal(received.rankingHistoryPath,"/tmp/history.json");
    assert.equal(received.rankBySize,false);
    for (const key of ["checkpointDir", "resume", "groupSize", "maxVerificationAttempts"]) {
      assert.equal(received[key], {checkpointDir:f.checkpointDir,resume:false,groupSize:3,maxVerificationAttempts:0}[key]);
      assert.ok(TOOL_DEFINITIONS.find(t => t.name === "lean_autoslim").inputSchema.properties[key]);
    }
    const manager = new FileWorkerManager(f.root);
    manager.autoSlimFile = async () => JSON.stringify({ completed: false, applied: false, verifiedCount: 0, rejectedCount: 0, verificationTimeMs: 0 });
    try { assert.equal(JSON.parse(await manager.autoSlimFiles({ filePaths: [f.file] })).completed, false); }
    finally { manager.dispose(); }
  } finally { server.lakeManager.dispose(); fs.rmSync(f.root, { recursive: true, force: true }); }
});

test("CLI emits an incomplete single-file receipt and exits nonzero at zero budget", () => {
  const f = fixture();
  try {
    const result = spawnSync(process.execPath, [fileURLToPath(new URL("../bin/lean-autoslim.js", import.meta.url)), f.file, "--mode", "batch", "--max-attempts", "0", "--json"], { encoding: "utf8" });
    assert.equal(result.status, 1, result.stderr);
    const receipt = JSON.parse(result.stdout);
    assert.equal(receipt.completed, false);
    assert.equal(receipt.stopReason, "attempt-budget");
    assert.equal(fs.readFileSync(f.file, "utf8"), f.source);
  } finally { fs.rmSync(f.root, { recursive: true, force: true }); }
});

function fixture() {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "autoslim-resume-"));
  fs.writeFileSync(path.join(root, "lakefile.toml"), 'name = "demo"\n');
  const file = path.join(root, "Sample.lean");
  const source = ["first", "second", "third", "fourth"].map(name =>
    `theorem ${name} (a b c d : Nat) (ha : a = b) (hb : b = c) (hc : c = d) (hd : d = d) : a = d := by\n` +
    "  rw [ha]\n  rw [hb]\n  rw [hc]\n  rw [hd]\n").join("\n");
  fs.writeFileSync(file, source);
  return { root, file, source, checkpointDir: path.join(root, "progress") };
}
const clean = async () => ({ ok: true, errorCount: 0, warningCount: 0 });
const opts = f => ({ filePath: f.file, mode: "lsp", checkpointDir: f.checkpointDir, groupSize: 4, lspVerifier: clean });

test("real compiler resumes a budgeted group and independently checks the final file", { skip: !process.env.LEAN_AUTOSLIM_RESUME_COMPILER }, async () => {
  const f = fixture();
  // The intentionally redundant hypothesis is named as unused in this real fixture.
  f.source = f.source.replaceAll("hd", "_hd");
  fs.writeFileSync(f.file, f.source);
  try {
    const options = { filePath: f.file, mode: "batch", checkpointDir: f.checkpointDir, groupSize: 4, apply: true,
      leanContext: { compilerPath: process.env.LEAN_AUTOSLIM_RESUME_COMPILER, targetVersion: "4.34.1", moduleRoots: [] } };
    const partial = await runKernelVerifiedAutoSlim(f.root, { ...options, maxVerificationAttempts: 1 });
    assert.equal(partial.completed, false);
    assert.equal(partial.provisionalCount, 4, fs.readFileSync(partial.checkpointPath, "utf8"));
    assert.equal(fs.readFileSync(f.file, "utf8"), f.source);
    const runner = fileURLToPath(new URL("../src/autoslim.ts", import.meta.url));
    const script = path.join(f.root, "resume.mjs");
    fs.writeFileSync(script, `import {runKernelVerifiedAutoSlim} from ${JSON.stringify(runner)}; console.log(JSON.stringify(await runKernelVerifiedAutoSlim(${JSON.stringify(f.root)},${JSON.stringify(options)})));`);
    const child = spawnSync(process.execPath, ["--experimental-strip-types", script], { encoding: "utf8" });
    assert.equal(child.status, 0, child.stderr);
    const resumed = JSON.parse(child.stdout);
    assert.equal(resumed.resumedCandidates, 4);
    assert.equal(resumed.verificationAttempts, 1);
    assert.equal(resumed.finalCheckPassed, true);
    assert.equal(resumed.applied, true);
    const named = fs.readFileSync(f.file, "utf8") + "\nexample : 1 = 1 := first (a := 1) (b := 1) (c := 1) (d := 1) rfl rfl rfl rfl\n";
    const probe = path.join(f.root, "Check.lean"); fs.writeFileSync(probe, named);
    const compiled = spawnSync(options.leanContext.compilerPath, ["-DwarningAsError=true", probe], { encoding: "utf8" });
    assert.equal(compiled.status, 0, compiled.stdout + compiled.stderr);
  } finally { fs.rmSync(f.root, { recursive: true, force: true }); }
});

test("a successful four-proof group takes one group check and one fresh final check", async () => {
  const f = fixture();
  try {
    const r = await runKernelVerifiedAutoSlim(f.root, { ...opts(f), apply: true });
    assert.equal(r.verifiedCount, 4);
    assert.equal(r.verificationAttempts, 2);
    assert.equal(r.groupChecks, 1);
    assert.equal(r.finalCheckPassed, true);
    assert.equal(fs.readFileSync(f.file, "utf8").match(/:= by grind/g).length, 4);
    assert.ok(fs.readFileSync(r.checkpointPath, "utf8").includes('"attempt"'));
  } finally { fs.rmSync(f.root, { recursive: true, force: true }); }
});

test("attempt budget saves resumable progress and never publishes without a final check", async () => {
  const f = fixture();
  try {
    const partial = await runKernelVerifiedAutoSlim(f.root, { ...opts(f), apply: true, maxVerificationAttempts: 1 });
    assert.equal(partial.completed, false);
    assert.equal(partial.stopReason, "attempt-budget");
    assert.equal(partial.applied, false);
    assert.equal(fs.readFileSync(f.file, "utf8"), f.source);
    const resumed = await runKernelVerifiedAutoSlim(f.root, { ...opts(f), apply: true });
    assert.equal(resumed.resumedCandidates, 4);
    assert.equal(resumed.verificationAttempts, 1);
    assert.equal(resumed.finalCheckPassed, true);
    assert.equal(resumed.applied, true);
  } finally { fs.rmSync(f.root, { recursive: true, force: true }); }
});

test("a real process exit preserves completed groups and resumes remaining work", async () => {
  const f = fixture();
  try {
    const runner = fileURLToPath(new URL("../src/autoslim.ts", import.meta.url));
    const script = path.join(f.root, "interrupt.mjs");
    fs.writeFileSync(script, `import {runKernelVerifiedAutoSlim} from ${JSON.stringify(runner)};\n` +
      `let calls=0; await runKernelVerifiedAutoSlim(${JSON.stringify(f.root)}, {filePath:${JSON.stringify(f.file)}, ` +
      `checkpointDir:${JSON.stringify(f.checkpointDir)},mode:"lsp",groupSize:2,apply:true, ` +
      `lspVerifier:async()=>{if(++calls===2)process.exit(73);return {ok:true,errorCount:0,warningCount:0}}});\n`);
    const interrupted = spawnSync(process.execPath, ["--experimental-strip-types", script], { encoding: "utf8" });
    assert.equal(interrupted.status, 73, interrupted.stderr);
    assert.equal(fs.readFileSync(f.file, "utf8"), f.source);
    const r = await runKernelVerifiedAutoSlim(f.root, { ...opts(f), groupSize: 2, apply: true });
    assert.equal(r.resumedCandidates, 2);
    assert.equal(r.verifiedCount, 4);
    assert.equal(r.verificationAttempts, 2);
    assert.equal(r.applied, true);
  } finally { fs.rmSync(f.root, { recursive: true, force: true }); }
});

test("failed groups bisect and reject interacting edits against the cumulative file", async () => {
  const f = fixture();
  try {
    const verifier = async content => {
      const first = /theorem first[^\n]*:= by grind/.test(content);
      const second = /theorem second[^\n]*:= by (?:grind|simp)/.test(content);
      return { ok: !(first && second), errorCount: first && second ? 1 : 0, warningCount: 0 };
    };
    const r = await runKernelVerifiedAutoSlim(f.root, { ...opts(f), apply: true, lspVerifier: verifier });
    assert.equal(r.verifiedCount, 3);
    assert.equal(r.rejectedCount, 1);
    assert.ok(r.bisections > 0);
    assert.equal(r.finalCheckPassed, true);
    const text = fs.readFileSync(f.file, "utf8");
    assert.match(text, /theorem first[^\n]*:= by grind/);
    assert.match(text, /theorem second[^\n]*:= by\n  rw \[ha\]/);
  } finally { fs.rmSync(f.root, { recursive: true, force: true }); }
});

test("cached positive verdicts never bypass a fresh failing final compilation", async () => {
  const f = fixture();
  let allow = true;
  const verifier = async () => ({ ok: allow, errorCount: allow ? 0 : 1, warningCount: 0 });
  try {
    await runKernelVerifiedAutoSlim(f.root, { ...opts(f), lspVerifier: verifier, maxVerificationAttempts: 1 });
    allow = false;
    const r = await runKernelVerifiedAutoSlim(f.root, { ...opts(f), lspVerifier: verifier, apply: true });
    assert.equal(r.resumedCandidates, 4);
    assert.equal(r.completed, false);
    assert.equal(r.stopReason, "final-check-failed");
    assert.equal(r.verifiedCount, 0);
    assert.equal(r.applied, false);
    assert.equal(fs.readFileSync(f.file, "utf8"), f.source);
  } finally { fs.rmSync(f.root, { recursive: true, force: true }); }
});

test("source and compiled dependency changes invalidate matching progress", async () => {
  const f = fixture();
  try {
    const partial = await runKernelVerifiedAutoSlim(f.root, { ...opts(f), maxVerificationAttempts: 1 });
    assert.equal(partial.completed, false);
    const lib = path.join(f.root, ".lake", "build", "lib", "lean");
    fs.mkdirSync(lib, { recursive: true }); fs.writeFileSync(path.join(lib, "Dependency.olean"), "changed");
    const changed = await runKernelVerifiedAutoSlim(f.root, opts(f));
    assert.equal(changed.resumedCandidates, 0);
    assert.notEqual(changed.checkpointPath, partial.checkpointPath);
    fs.appendFileSync(f.file, "-- source changed\n");
    const sourceChanged = await runKernelVerifiedAutoSlim(f.root, opts(f));
    assert.equal(sourceChanged.resumedCandidates, 0);
    assert.notEqual(sourceChanged.checkpointPath, changed.checkpointPath);
  } finally { fs.rmSync(f.root, { recursive: true, force: true }); }
});

test("journal refuses symlinks and corrupt middle records but recovers a torn last append", async () => {
  const f = fixture();
  try {
    const r = await runKernelVerifiedAutoSlim(f.root, { ...opts(f), maxVerificationAttempts: 1 });
    assert.equal(typeof r.checkpointPath, "string");
    fs.appendFileSync(r.checkpointPath, '{"torn":');
    const resumed = await runKernelVerifiedAutoSlim(f.root, opts(f));
    assert.equal(resumed.resumedCandidates, 4);
    fs.appendFileSync(r.checkpointPath, "invalid middle\n{}\n");
    await assert.rejects(runKernelVerifiedAutoSlim(f.root, opts(f)), /journal|checkpoint|record/i);
    const symlink = path.join(f.root, "symlink-progress");
    fs.symlinkSync(f.checkpointDir, symlink);
    await assert.rejects(runKernelVerifiedAutoSlim(f.root, { ...opts(f), checkpointDir: symlink }), /symlink/i);
  } finally { fs.rmSync(f.root, { recursive: true, force: true }); }
});


test("advisory history prioritizes successful cheap tactics without removing fallbacks", async () => {
  const { rankTactics, candidatePriority } = await import("../src/autoslim_ranking.ts");
  const history = [{route:"arithmetic",tactic:"by omega",ok:true,elapsedMs:10},
    {route:"arithmetic",tactic:"by grind",ok:false,elapsedMs:1000}];
  assert.deepEqual(rankTactics("arithmetic",["by grind","by omega","by simp"],history),["by omega","by simp","by grind"]);
  assert.deepEqual(rankTactics("unknown",["by grind","by omega"],history),["by grind","by omega"]);
  assert.ok(candidatePriority("arithmetic",100,history)>0);
  assert.equal(candidatePriority("unknown",100,history),100);
});

test("history loader bounds and validates advisory input", async () => {
  const { readRankingHistory } = await import("../src/autoslim_ranking.ts");
  const f=fixture(); const file=path.join(f.root,"ranking.json");
  try {
    fs.writeFileSync(file,JSON.stringify({schemaVersion:1,observations:[{route:"r",tactic:"by omega",ok:true,elapsedMs:2}]}));
    assert.equal(readRankingHistory(file).length,1);
    for(const elapsedMs of [-1,null,"2"]) {
      fs.writeFileSync(file,JSON.stringify({schemaVersion:1,observations:[{route:"r",tactic:"by omega",ok:true,elapsedMs}]}));
      assert.throws(()=>readRankingHistory(file),/ranking history/i);
    }
    assert.deepEqual(readRankingHistory(undefined),[]);
  } finally {fs.rmSync(f.root,{recursive:true,force:true});}
});


test("history only reorders allowed recipes and changed history still needs a fresh final check", async () => {
  const f=fixture();const history=path.join(f.root,"history.json");
  fs.writeFileSync(history,JSON.stringify({schemaVersion:1,observations:[{route:"eqsat-congruence-closure",tactic:"by simp",ok:true,elapsedMs:1}]}));
  try {
    const ranked=await runKernelVerifiedAutoSlim(f.root,{...opts(f),rankingHistoryPath:history});
    assert.equal(ranked.completed,true);
    assert.equal(ranked.verifiedCount,4);
    assert.ok(ranked.edits.every(e=>e.newText==="by simp"));
    const fallback=await runKernelVerifiedAutoSlim(f.root,opts(f));
    assert.equal(fallback.completed,true);
    assert.equal(fallback.verifiedCount,4);
    assert.equal(fallback.finalCheckPassed,true);
    assert.ok(fallback.verificationAttempts>=1);
    assert.equal(fallback.resumedCandidates,4);
    assert.ok(fallback.edits.every(e=>e.newText==="by simp"));
  } finally {fs.rmSync(f.root,{recursive:true,force:true});}
});


test("ranking history refuses nonregular streams without blocking", {skip:process.platform==="win32"}, () => {
  const f=fixture();const fifo=path.join(f.root,"history.fifo");
  try {
    assert.equal(spawnSync("mkfifo",[fifo]).status,0);
    const module=fileURLToPath(new URL("../src/autoslim_ranking.ts",import.meta.url));
    const script=`import {readRankingHistory} from ${JSON.stringify(module)}; try {readRankingHistory(${JSON.stringify(fifo)}); process.exit(2);} catch(e) {if(!/ranking history/i.test(e.message)) throw e;}`;
    const result=spawnSync(process.execPath,["--experimental-strip-types","--input-type=module","-e",script],{timeout:3000,encoding:"utf8"});
    assert.equal(result.error,undefined);
    assert.equal(result.status,0,result.stderr);
  } finally {fs.rmSync(f.root,{recursive:true,force:true});}
});


test("ranking observations exclude group, final, cache and inconclusive evidence", async () => {
  const root=fs.mkdtempSync(path.join(os.tmpdir(),"ranking-observations-"));
  const proposals=[{id:"a",tactics:["by grind"]},{id:"b",tactics:["by grind"]}];
  const render=choices=>JSON.stringify([...choices]);
  try {
    const grouped=await verifyProofGroups({proposals,render,verify:clean,journal:new AutoSlimJournal(root,contentHash("group")),groupSize:2});
    assert.equal(grouped.observations.length,0);
    const journal=new AutoSlimJournal(root,contentHash("single"));
    const single=await verifyProofGroups({proposals,render,verify:clean,journal,groupSize:1});
    assert.equal(single.observations.length,2);
    assert.ok(single.observations.every(o=>o.ok && o.elapsedMs>=0));
    const cached=await verifyProofGroups({proposals,render,verify:clean,journal,groupSize:1});
    assert.equal(cached.observations.length,0);
    assert.equal(cached.attempts,1);
    const incomplete=await verifyProofGroups({proposals,render,verify:async()=>({ok:false,errorCount:1,warningCount:0,inconclusive:true}),journal:new AutoSlimJournal(root,contentHash("incomplete")),groupSize:1});
    assert.equal(incomplete.observations.length,0);
    assert.equal(incomplete.completed,false);
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test("source order remains available with history supplied", async () => {
  const f=fixture(); const history=path.join(f.root,"history.json");
  fs.writeFileSync(history,JSON.stringify({schemaVersion:1,observations:[{route:"eqsat-congruence-closure",tactic:"by simp",ok:true,elapsedMs:1}]}));
  try {
    const report=await runKernelVerifiedAutoSlim(f.root,{...opts(f),maxCandidates:1,rankBySize:false,rankingHistoryPath:history});
    assert.equal(report.verifiedCount,1);
    assert.equal(report.edits[0].theoremName,"first");
  } finally {fs.rmSync(f.root,{recursive:true,force:true});}
});
