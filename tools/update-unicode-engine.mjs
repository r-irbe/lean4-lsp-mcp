// Maintainer-only, offline regeneration. No package install or network access.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import * as module from 'node:module';
const args=process.argv.slice(2);
if(args.length!==4 || args[0]!=='--source-root' || args[2]!=='--source-revision' || !/^[a-f0-9]{40}$/.test(args[3])) {
 throw new Error('Usage: node tools/update-unicode-engine.mjs --source-root <local checkout> --source-revision <40-hex commit>');
}
if(typeof module.stripTypeScriptTypes!=='function') throw new Error('Regeneration requires Node module.stripTypeScriptTypes; the checker has no such requirement.');
const root=path.resolve(args[1]), revision=args[3];
const env={PATH:process.env.PATH,GIT_OPTIONAL_LOCKS:'0',GIT_TERMINAL_PROMPT:'0'};
const readCommitted=(rel)=>{
 const current=fs.readFileSync(path.join(root,rel));
 const committed=execFileSync('git',['-C',root,'show',`${revision}:${rel}`],{env,maxBuffer:4*1024*1024,timeout:10000});
 if(!current.equals(committed)) throw new Error(`Source differs from selected committed preimage: ${rel}`);
 return current;
};
const source=readCommitted('src/safety/unicode.ts');
const license=readCommitted('LICENSE');
const artifact=Buffer.from(module.stripTypeScriptTypes(source.toString('utf8'),{mode:'strip'}));
const sha=(b)=>createHash('sha256').update(b).digest('hex');
const manifest={schemaVersion:1,source:{repository:'r-irbe/pi-harness-bridge',revision,path:'src/safety/unicode.ts',sha256:sha(source)},generator:{name:'node:module.stripTypeScriptTypes',mode:'strip',node:process.version},files:{'unicode-policy.source.txt':sha(source),'unicode-policy.mjs':sha(artifact),'UNICODE-ENGINE-LICENSE.txt':sha(license)},license:'Apache-2.0'};
const vendor=fileURLToPath(new URL('./vendor/',import.meta.url));
fs.mkdirSync(vendor,{recursive:true});
// Manifest last: interruption causes an integrity failure, never a silent pass.
for(const [name,data] of [['unicode-policy.source.txt',source],['unicode-policy.mjs',artifact],['UNICODE-ENGINE-LICENSE.txt',license],['unicode-policy.provenance.json',Buffer.from(JSON.stringify(manifest,null,2)+'\n')]]) {
 const tmp=path.join(vendor,`.${name}.${process.pid}.tmp`);
 fs.writeFileSync(tmp,data,{flag:'wx'});fs.renameSync(tmp,path.join(vendor,name));
}
console.log(JSON.stringify(manifest));
