/** Shared proof-skills kernel receipt adapter. Check is the default; rebuild is explicit. */
import fs from 'node:fs';
import path from 'node:path';
import { spawn, spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { isLakeRoot } from './project_root.ts';

function inside(root: string, candidate: string): boolean {
  const relative=path.relative(root,candidate);
  return relative!== '..' && !relative.startsWith('..'+path.sep) && !path.isAbsolute(relative);
}

function validatePaths(workspace: string, args: any) {
  if(typeof args.target!=='string' || !args.target.trim()) throw new Error('Invalid project target');
  const base=fs.realpathSync(workspace);
  let project: string;
  try {project=fs.realpathSync(path.resolve(base,args.target));} catch {throw new Error('Invalid project target');}
  if(!inside(base,project) || !fs.statSync(project).isDirectory() || !isLakeRoot(project)) throw new Error('Invalid project target: outside workspace or not a Lake project');
  if(typeof args.prefix!=='string' || !/^[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*$/.test(args.prefix)) throw new Error('Invalid module prefix');
  const mode=args.mode===undefined?'check':args.mode;
  if(mode!=='check' && mode!=='rebuild') throw new Error('Invalid census mode');
  if(args.receiptPath!==undefined && (typeof args.receiptPath!=='string' || !args.receiptPath.trim())) throw new Error('Invalid receipt path');
  const receipt=path.resolve(project,args.receiptPath??path.join('.lake','kernel-census',args.prefix+'.json'));
  if(!inside(project,receipt) || !receipt.endsWith('.json') || ['lake-manifest.json','package.json','package-lock.json'].includes(path.basename(receipt))) throw new Error('Invalid receipt path: must be a census JSON inside project');
  let current=project;
  for(const part of path.relative(project,receipt).split(path.sep)) {
    current=path.join(current,part);
    try {if(fs.lstatSync(current).isSymbolicLink()) throw new Error('Invalid receipt path: symlink');}
    catch(error: any) {if(error.code!=='ENOENT') throw error;}
  }
  const timeoutMs=args.timeoutMs??(mode==='check'?120000:1200000);
  if(!Number.isInteger(timeoutMs) || timeoutMs<1000 || timeoutMs>3600000) throw new Error('Invalid census timeoutMs');
  return {project,receipt,mode,timeoutMs};
}

export function resolveKernelCensusAdapter(_project: string): string|undefined {
  const configured=process.env.LEAN_PROOF_SKILLS_ROOT;
  // Only operator configuration or the MCP installation's enclosing toolkit
  // is trusted. Never discover executable adapters from the requested project.
  const file=configured!==undefined?path.resolve(configured,'scripts','lean','kernel_census.py'):
    fileURLToPath(new URL('../../../scripts/lean/kernel_census.py',import.meta.url));
  try {if(fs.statSync(file).isFile())return file;} catch {}
  return undefined;
}

function failed(receipt: string, reason: string, status='unverified') {
  return {status,evidenceKind:'compiled-kernel-replay',gateEligible:false,receiptPath:receipt,reasons:[reason]};
}

function invoke(adapter: string, project: string, receipt: string, prefix: string, mode: string, timeoutMs: number, abort?: AbortSignal): Promise<any> {
  return new Promise(resolve=>{
    const child=spawn('python3',[adapter,'--project-root',project,'--prefix',prefix,'--receipt',receipt,'--mode',mode],{cwd:project,detached:process.platform!=='win32',stdio:['ignore','pipe','pipe']});
    let stdout='';let stderr='';let failure='';let done=false;
    let killTimer: ReturnType<typeof setTimeout>|undefined;
    const kill=(signal: NodeJS.Signals)=>{try {if(process.platform!=='win32' && child.pid)process.kill(-child.pid,signal);else if(child.pid)spawnSync('taskkill',['/PID',String(child.pid),'/T','/F'],{stdio:'ignore'});}catch {child.kill(signal);}};
    const stop=(reason: string)=>{if(failure)return;failure=reason;kill('SIGTERM');killTimer=setTimeout(()=>kill('SIGKILL'),250);killTimer.unref();};
    const onAbort=()=>{failure='Kernel census cancelled by server shutdown';kill('SIGKILL');};
    abort?.addEventListener('abort',onAbort,{once:true});
    if(abort?.aborted)onAbort();
    const timer=setTimeout(()=>stop(`Kernel census timeout after ${timeoutMs}ms`),timeoutMs);
    const finish=(value: any)=>{if(done)return;done=true;abort?.removeEventListener('abort',onAbort);clearTimeout(timer);if(killTimer && !failure)clearTimeout(killTimer);resolve(value);};
    child.stdout.on('data',(data: Buffer)=>{if(stdout.length+data.length>1024*1024) stop('Kernel adapter output limit exceeded');else stdout+=data.toString('utf8');});
    child.stderr.on('data',(data: Buffer)=>{stderr=(stderr+data.toString('utf8')).slice(-8192);});
    child.on('error',error=>finish(failed(receipt,`Kernel adapter unavailable: ${error.message}`)));
    child.on('close',(code,signal)=>{
      if(failure || signal) return finish(failed(receipt,failure||`Kernel adapter interrupted: ${signal}`));
      try {
        const report=JSON.parse(stdout);
        if(report.evidenceKind!=='compiled-kernel-replay' || !['verified','stale','missing','unverified','unavailable'].includes(report.status) || report.gateEligible!==(report.status==='verified') || (report.gateEligible && code!==0)) throw new Error('Invalid adapter receipt status');
        if(report.gateEligible) {
          const fields=['modules','constants','theorems','definitions','declaredAxioms','eligible','replayed','axiomAudited','skippedUnsafe','skippedPartial','privateTheorems','loadedParts','disallowedAxiomUses'];
          if(!fields.every(k=>Number.isSafeInteger(report.counts?.[k]) && report.counts[k]>=0) || !/^[a-f0-9]{64}$/.test(report.receiptSha256??'') || !/^[a-f0-9]{64}$/.test(report.contextFingerprint??'') || !report.scope || Object.values(report.scope).some(v=>v!==false)) throw new Error('Incomplete verified adapter result');
        }
        finish(report);
      } catch(error: any) {finish(failed(receipt,`Kernel adapter did not return valid evidence: ${error.message}; ${stderr}`));}
    });
  });
}

export async function runKernelCensus(workspace: string,args: any,abort?: AbortSignal): Promise<string> {
  const {project,receipt,mode,timeoutMs}=validatePaths(workspace,args);
  const adapter=resolveKernelCensusAdapter(project);
  const report=adapter?await invoke(adapter,project,receipt,args.prefix,mode,timeoutMs,abort):failed(receipt,'Install proof-skills or set LEAN_PROOF_SKILLS_ROOT','unavailable');
  if(args.format==='json')return JSON.stringify(report);
  const lines=[`Kernel census: ${report.status}`,`Evidence: ${report.evidenceKind}`,`gateEligible: ${report.gateEligible}`,`Receipt: ${report.receiptPath}`];
  if(report.counts) lines.push(`Modules: ${report.counts.modules}; constants: ${report.counts.constants}; replayed: ${report.counts.replayed}; theorem constants: ${report.counts.theorems}`,`Excluded unsafe: ${report.counts.skippedUnsafe}; partial: ${report.counts.skippedPartial}`);
  lines.push(...(report.reasons??[]),'Scope: external library bodies and discarded examples are not replayed.');
  return lines.join('\n');
}
