import assert from 'node:assert/strict';
import { test } from 'node:test';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { McpServer, TOOL_DEFINITIONS } from '../src/index.ts';

function fixture() {
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'mcp-kernel-census-'));
  fs.writeFileSync(path.join(root,'lean-toolchain'),'leanprover/lean4:v0.0.0\n');
  fs.writeFileSync(path.join(root,'lakefile.toml'),'name="fixture"\n');
  fs.writeFileSync(path.join(root,'Fixture.lean'),'set_option autoImplicit false\n');
  const adapter=path.join(root,'skills','scripts','lean');fs.mkdirSync(adapter,{recursive:true});
  fs.writeFileSync(path.join(adapter,'kernel_census.py'),`import argparse,json\np=argparse.ArgumentParser()\np.add_argument('--project-root');p.add_argument('--prefix');p.add_argument('--receipt');p.add_argument('--mode');a=p.parse_args()\nprint(json.dumps(dict(status='missing',gateEligible=False,evidenceKind='compiled-kernel-replay',receiptPath=a.receipt,reasons=[])))\n`);
  process.env.LEAN_PROOF_SKILLS_ROOT=path.join(root,'skills');
  return root;
}

test('kernel census is explicit, missing evidence is not a static count, and check writes nothing', async()=>{
 const root=fixture(); const server=new McpServer(root);
 try {
  const result=JSON.parse(await server.executeTool('lean_metrics',{action:'kernel_census',target:'.',prefix:'Fixture',format:'json'}));
  assert.equal(result.status,'missing');assert.equal(result.gateEligible,false);assert.equal(result.evidenceKind,'compiled-kernel-replay');
  assert.equal(fs.existsSync(path.join(root,'.lake')),false);
  const tool=TOOL_DEFINITIONS.find(t=>t.name==='lean_metrics');
  assert.ok(tool.inputSchema.properties.action.enum.includes('kernel_census'));
  assert.equal(tool.inputSchema.properties.mode.default,'check');assert.equal(tool.annotations.readOnlyHint,false);
  assert.equal(tool.inputSchema.properties.receiptPath.type,'string');
 }finally{server.lakeManager.dispose();fs.rmSync(root,{recursive:true,force:true});}
});

test('kernel census rejects project and receipt escapes and invalid mode before invoking adapter', async()=>{
 const root=fixture(); const server=new McpServer(root);
 try{
  for(const args of [{target:'..'},{receiptPath:'../outside.json'},{mode:'implicit'},{prefix:'../Bad'},{receiptPath:'Fixture.lean'}]){
   await assert.rejects(()=>server.executeTool('lean_metrics',{action:'kernel_census',target:'.',prefix:'Fixture',...args}),/invalid|outside|escape|mode|prefix|receipt/i);
  }
  fs.symlinkSync(os.tmpdir(),path.join(root,'alias'));
  await assert.rejects(()=>server.executeTool('lean_metrics',{action:'kernel_census',target:'.',prefix:'Fixture',receiptPath:'alias/escape.json'}),/outside|escape|symlink/i);
 }finally{server.lakeManager.dispose();fs.rmSync(root,{recursive:true,force:true});}
});

test('missing optional toolkit gives structured unavailable and static census remains separate',async()=>{
 const root=fixture();const before=process.env.LEAN_PROOF_SKILLS_ROOT;process.env.LEAN_PROOF_SKILLS_ROOT=path.join(root,'absent');const server=new McpServer(root);
 try{
  const r=JSON.parse(await server.executeTool('lean_metrics',{action:'kernel_census',target:'.',prefix:'Fixture',format:'json'}));
  assert.equal(r.status,'unavailable');assert.equal(r.gateEligible,false);
  const staticResult=await server.executeTool('lean_metrics',{action:'census',target:'.',format:'json'});
  assert.doesNotMatch(staticResult,/compiled-kernel-replay/);
 }finally{if(before===undefined)delete process.env.LEAN_PROOF_SKILLS_ROOT;else process.env.LEAN_PROOF_SKILLS_ROOT=before;server.lakeManager.dispose();fs.rmSync(root,{recursive:true,force:true});}
});

test('explicit rebuild forwards mode and failed backend cannot grant verified',async()=>{
 const root=fixture();const server=new McpServer(root);const adapter=path.join(root,'skills/scripts/lean/kernel_census.py');
 try{
  fs.writeFileSync(adapter,`import argparse,json,pathlib,sys\np=argparse.ArgumentParser();p.add_argument('--project-root');p.add_argument('--prefix');p.add_argument('--receipt');p.add_argument('--mode');a=p.parse_args()\npathlib.Path(a.project_root,'called-mode').write_text(a.mode)\nprint(json.dumps(dict(status='verified',gateEligible=True,evidenceKind='compiled-kernel-replay',receiptPath=a.receipt)));sys.exit(1)\n`);
  const result=JSON.parse(await server.executeTool('lean_metrics',{action:'kernel_census',target:'.',prefix:'Fixture',mode:'rebuild',format:'json'}));
  assert.equal(fs.readFileSync(path.join(root,'called-mode'),'utf8'),'rebuild');assert.equal(result.status,'unverified');assert.equal(result.gateEligible,false);
  fs.writeFileSync(adapter,fs.readFileSync(adapter,'utf8').replace('sys.exit(1)','sys.exit(0)'));
  const incomplete=JSON.parse(await server.executeTool('lean_metrics',{action:'kernel_census',target:'.',prefix:'Fixture',format:'json'}));
  assert.equal(incomplete.status,'unverified');assert.match(incomplete.reasons.join(' '),/Incomplete verified/);
 }finally{server.lakeManager.dispose();fs.rmSync(root,{recursive:true,force:true});}
});

test('adapter timeout terminates descendant build processes',async()=>{
 const root=fixture();const server=new McpServer(root);const marker=path.join(root,'orphan-marker');
 try{
  const childCode=`import time,pathlib;time.sleep(1.5);pathlib.Path(${JSON.stringify(marker)}).write_text('orphan')`;
  fs.writeFileSync(path.join(root,'skills/scripts/lean/kernel_census.py'),`import subprocess,sys,time\nsubprocess.Popen([sys.executable,'-c',${JSON.stringify(childCode)}])\ntime.sleep(30)\n`);
  const result=JSON.parse(await server.executeTool('lean_metrics',{action:'kernel_census',target:'.',prefix:'Fixture',timeoutMs:1000,format:'json'}));
  assert.equal(result.status,'unverified');assert.match(result.reasons.join(' '),/timeout/i);
  await new Promise(resolve=>setTimeout(resolve,1000));assert.equal(fs.existsSync(marker),false,'Descendant survived adapter timeout');
 }finally{server.lakeManager.dispose();fs.rmSync(root,{recursive:true,force:true});}
});

test('workspace adapter is not trusted without operator configuration',async()=>{
 const root=fixture();delete process.env.LEAN_PROOF_SKILLS_ROOT;const server=new McpServer(root);
 try{
  const r=JSON.parse(await server.executeTool('lean_metrics',{action:'kernel_census',target:'.',prefix:'Fixture',format:'json'}));
  assert.equal(r.status,'unavailable');assert.equal(r.gateEligible,false);
 }finally{server.dispose();fs.rmSync(root,{recursive:true,force:true});}
});

test('server disposal terminates detached adapters and descendants',async()=>{
 const root=fixture();const server=new McpServer(root);const marker=path.join(root,'shutdown-orphan');
 try{
  fs.writeFileSync(path.join(root,'skills/scripts/lean/kernel_census.py'),`import time,pathlib\ntime.sleep(1)\npathlib.Path(${JSON.stringify(marker)}).write_text('survived')\n`);
  const task=server.executeTool('lean_metrics',{action:'kernel_census',target:'.',prefix:'Fixture',format:'json'});
  await new Promise(resolve=>setTimeout(resolve,100));server.dispose();
  const r=JSON.parse(await task);assert.equal(r.gateEligible,false);
  await new Promise(resolve=>setTimeout(resolve,1100));assert.equal(fs.existsSync(marker),false);
 }finally{server.dispose();fs.rmSync(root,{recursive:true,force:true});}
});

test('strict import rehash is explicitly forwarded to the trusted adapter',async()=>{
 const root=fixture();const server=new McpServer(root);const adapter=path.join(root,'skills/scripts/lean/kernel_census.py');
 try{
  let source=fs.readFileSync(adapter,'utf8');source=source.replace("p.add_argument('--mode');a=", "p.add_argument('--mode');p.add_argument('--rehash-imports',action='store_true');a=").replace('reasons=[]','reasons=[str(a.rehash_imports)]');fs.writeFileSync(adapter,source);
  const r=JSON.parse(await server.executeTool('lean_metrics',{action:'kernel_census',target:'.',prefix:'Fixture',rehashImports:true,format:'json'}));
  assert.deepEqual(r.reasons,['True']);
 }finally{server.dispose();fs.rmSync(root,{recursive:true,force:true});}
});
