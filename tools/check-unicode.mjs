// Standalone CI adapter. Policy logic lives only in the pinned shared engine.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';
const VENDOR=fileURLToPath(new URL('./vendor/',import.meta.url));
const PACKAGE=fileURLToPath(new URL('../',import.meta.url));
const sha=(data)=>createHash('sha256').update(data).digest('hex');
const FILES=['unicode-policy.source.txt','unicode-policy.mjs','UNICODE-ENGINE-LICENSE.txt'];
const REQUIRED=['src','bin','tests','tools','README.md','USER_GUIDE.md'];
const ELF_PATH='bin/lean-analyzer';
// vendorDirectory is trusted maintainer/test code, never a scanned-input option.
export async function loadPinnedEngine(vendorDirectory=VENDOR) {
 if(!fs.lstatSync(vendorDirectory).isDirectory() || fs.lstatSync(vendorDirectory).isSymbolicLink()) throw new Error('Invalid vendor directory');
 const manifestPath=path.join(vendorDirectory,'unicode-policy.provenance.json');
 if(!fs.lstatSync(manifestPath).isFile()) throw new Error('Invalid provenance file');
 const meta=JSON.parse(fs.readFileSync(manifestPath,'utf8'));
 if(meta.schemaVersion!==1 || !/^[a-f0-9]{40}$/.test(meta.source?.revision??'') || meta.license!=='Apache-2.0') throw new Error('Invalid engine provenance');
 for(const name of FILES) {
  const p=path.join(vendorDirectory,name);
  if(!fs.lstatSync(p).isFile() || !/^[a-f0-9]{64}$/.test(meta.files?.[name]??'') || sha(fs.readFileSync(p))!==meta.files[name]) throw new Error(`Engine integrity failure: ${name}`);
 }
 if(meta.source.sha256!==meta.files['unicode-policy.source.txt']) throw new Error('Source pin mismatch');
 // Verify all bytes before loading the trusted artifact. This assumes one writer;
 // it is not a sandbox against concurrent hostile filesystem replacement.
 const engine=await import(pathToFileURL(path.join(vendorDirectory,'unicode-policy.mjs')).href+'?sha='+meta.files['unicode-policy.mjs']);
 if(typeof engine.scanUnicode!=='function' || typeof engine.modeForPath!=='function' || !engine.DEFAULT_UNICODE_POLICY) throw new Error('Unsupported engine API');
 return {engine,provenance:meta};
}
export async function checkUnicodeTree(root,{maxTextBytes=8*1024*1024,maxBinaryBytes=64*1024*1024}={}) {
 const {engine,provenance}=await loadPinnedEngine();
 const policy=engine.DEFAULT_UNICODE_POLICY;
 const report={ok:false,policy:'pinned public DEFAULT_UNICODE_POLICY (no private host overrides)',sourceRevision:provenance.source.revision,files:[],errors:[],unicodeFindings:0};
 const error=(file,kind,detail)=>report.errors.push({file,kind,detail});
 root=path.resolve(root);
 if(fs.lstatSync(root).isSymbolicLink()) throw new Error('Root may not be a symlink');
 const visit=(rel)=>{
  const p=path.join(root,rel);
  let stat;
  try {stat=fs.lstatSync(p);} catch {error(rel,'coverage','Missing or unreadable required path');return;}
  if(stat.isSymbolicLink()){error(rel,'symlink','Symlinks are not followed');return;}
  if(stat.isDirectory()) {
   const count=report.files.length+report.errors.length;
   let names;try{names=fs.readdirSync(p).sort();}catch{error(rel,'coverage','Unreadable directory');return;}
   for(const name of names) {
    if(name.startsWith('.env') || ['.git','.ssh','node_modules'].includes(name)){error(path.posix.join(rel,name),'excluded-sensitive-path','Not read; unexpected path in source population');continue;}
    visit(path.posix.join(rel,name));
   }
   if(REQUIRED.includes(rel) && report.files.length+report.errors.length===count) error(rel,'coverage','Empty required source subtree');
   return;
  }
  if(!stat.isFile() || !(stat.mode&0o444)){error(rel,'coverage','Not a readable regular file');return;}
  let data;
  try {
   const fd=fs.openSync(p,fs.constants.O_RDONLY|(fs.constants.O_NOFOLLOW??0));
   try {
    const head=Buffer.alloc(64),n=fs.readSync(fd,head,0,64,0);
    const elf=n>=4 && head.subarray(0,4).equals(Buffer.from([0x7f,0x45,0x4c,0x46]));
    if(elf) {
     if(rel!==ELF_PATH || ![1,2].includes(head[4]) || ![1,2].includes(head[5]) || head[6]!==1 || n<(head[4]===2?64:52)) {error(rel,'binary-format','Unexpected or malformed ELF input');return;}
     if(stat.size>maxBinaryBytes){error(rel,'coverage','Binary exceeds explicit read budget; not skipped');return;}
     data=fs.readFileSync(fd);
     report.files.push({path:rel,classification:'expected ELF header (not executable certification)',bytes:data.length,sha256:sha(data)});return;
    }
    if(stat.size>maxTextBytes){error(rel,'coverage','Text exceeds explicit byte budget; not skipped');return;}
    data=fs.readFileSync(fd);
   } finally {fs.closeSync(fd);}
  } catch {error(rel,'coverage','File read failed');return;}
  if(data.includes(0)){error(rel,'binary-format','Unclassified NUL-containing input');return;}
  let text;
  // ignoreBOM=true preserves U+FEFF for the policy scanner instead of dropping it.
  try{text=new TextDecoder('utf-8',{fatal:true,ignoreBOM:true}).decode(data);}catch{error(rel,'encoding','Invalid UTF-8; not skipped');return;}
  const mode=engine.modeForPath(policy,rel,path.matchesGlob);
  const scan=engine.scanUnicode(text,mode,policy);
  report.files.push({path:rel,classification:mode==='unrestricted'?'policy-exempt text (integrity pin separate)':'text',mode,bytes:data.length,sha256:sha(data),findings:scan.total});
  report.unicodeFindings+=scan.total;
  for(const finding of scan.findings) report.errors.push({file:rel,...finding});
 };
 for(const rel of REQUIRED)visit(rel);
 if(fs.lstatSync(path.join(root,'test'),{throwIfNoEntry:false}))visit('test');
 report.ok=report.errors.length===0 && report.unicodeFindings===0;
 return report;
}
export const safeJson=(value)=>JSON.stringify(value,null,2).replace(/[^\x20-\x7e\r\n\t]/g,c=>'\\u'+c.charCodeAt(0).toString(16).padStart(4,'0'));
if(process.argv[1] && path.resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
 const args=process.argv.slice(2);
 if(args.length && (args.length!==2 || args[0]!=='--root')) {console.error('Usage: node tools/check-unicode.mjs [--root <checkout>]');process.exitCode=2;}
 else {
  try {const result=await checkUnicodeTree(args[1]??PACKAGE);console.log(safeJson(result));process.exitCode=result.ok?0:1;}
  catch(e){console.log(safeJson({ok:false,error:String(e.message)}));process.exitCode=1;}
 }
}
