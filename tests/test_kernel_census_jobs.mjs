import assert from 'node:assert/strict';
import {test} from 'node:test';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {kernelControllerTimeout} from '../src/kernel_census.ts';
import {McpServer,TOOL_DEFINITIONS} from '../src/index.ts';

function fixture(){
 const root=fs.mkdtempSync(path.join(os.tmpdir(),'mcp-census-jobs-'));
 fs.writeFileSync(path.join(root,'lean-toolchain'),'fixture');fs.writeFileSync(path.join(root,'lakefile.toml'),'name="fixture"');
 const scripts=path.join(root,'toolkit/scripts/lean');fs.mkdirSync(scripts,{recursive:true});
 fs.writeFileSync(path.join(scripts,'kernel_census.py'),'# trusted installed adapter marker\n');
 fs.writeFileSync(path.join(scripts,'kernel_census_jobs.py'),`import argparse,json,pathlib,subprocess,sys\np=argparse.ArgumentParser();p.add_argument('--project-root');p.add_argument('--prefix');p.add_argument('--receipt');p.add_argument('--mode');p.add_argument('--job-id');p.add_argument('--timeout-ms');p.add_argument('--rehash-imports',action='store_true');a=p.parse_args()\nroot=pathlib.Path(a.project_root)\n(root/'last-controller.json').write_text(json.dumps(vars(a)))\nif a.mode=='start':\n subprocess.Popen([sys.executable,'-c',"import time,pathlib;time.sleep(.3);pathlib.Path(%r).write_text('done')" % str(root/'worker-done')],start_new_session=True,stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)\nstate='cancelled' if a.mode=='cancel' else 'running'\nprint(json.dumps(dict(status=state,gateEligible=False,evidenceKind='compiled-kernel-replay',receiptPath=str(root/'receipt.json'),job=dict(id=a.job_id or 'a'*32,state=state,phase='building'),reasons=[])))\n`);
 process.env.LEAN_PROOF_SKILLS_ROOT=path.join(root,'toolkit');return root;
}

test('async modes return an ID promptly and status works after server replacement',async()=>{
 const root=fixture();let server=new McpServer(root);
 try{
  const started=Date.now();const first=JSON.parse(await server.executeTool('lean_metrics',{action:'kernel_census',target:'.',prefix:'Fixture',mode:'start',format:'json'}));
  assert.ok(Date.now()-started<2000);assert.match(first.job.id,/^[a-f0-9]{32}$/);assert.equal(first.gateEligible,false);
  server.dispose();server=new McpServer(root);
  await new Promise(resolve=>setTimeout(resolve,500));assert.equal(fs.readFileSync(path.join(root,'worker-done'),'utf8'),'done');
  const status=JSON.parse(await server.executeTool('lean_metrics',{action:'kernel_census',target:'.',prefix:'Fixture',mode:'status',jobId:first.job.id,format:'json'}));assert.equal(status.job.id,first.job.id);
  const cancelled=JSON.parse(await server.executeTool('lean_metrics',{action:'kernel_census',target:'.',prefix:'Fixture',mode:'cancel',jobId:first.job.id,format:'json'}));assert.equal(cancelled.job.state,'cancelled');assert.equal(cancelled.gateEligible,false);
  const schema=TOOL_DEFINITIONS.find(t=>t.name==='lean_metrics').inputSchema.properties;assert.ok(schema.mode.enum.includes('start'));assert.ok(schema.mode.enum.includes('status'));assert.ok(schema.mode.enum.includes('cancel'));assert.equal(schema.jobId.type,'string');
 }finally{server.dispose();fs.rmSync(root,{recursive:true,force:true});}
});

test('job identifiers and overrides are validated before launch',async()=>{
 const root=fixture();const server=new McpServer(root);
 try{
  for(const args of [{mode:'status'},{mode:'cancel',jobId:'../escape'},{mode:'start',jobId:'a'.repeat(32)},{mode:'check',jobId:'a'.repeat(32)}])
   await assert.rejects(()=>server.executeTool('lean_metrics',{action:'kernel_census',target:'.',prefix:'Fixture',...args}),/job|identifier/i);
  assert.equal(fs.existsSync(path.join(root,'last-controller.json')),false);
 }finally{server.dispose();fs.rmSync(root,{recursive:true,force:true});}
});

test('status controller stays below the measured transport deadline',()=>{assert.ok(kernelControllerTimeout('status',3600000)<300000);assert.equal(kernelControllerTimeout('status',1000),1000);assert.equal(kernelControllerTimeout('start',3600000),15000);});
