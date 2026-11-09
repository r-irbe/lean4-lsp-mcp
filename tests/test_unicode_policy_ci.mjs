import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { pathToFileURL, fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { checkUnicodeTree, loadPinnedEngine, safeJson } from '../tools/check-unicode.mjs';
const vendor=fileURLToPath(new URL('../tools/vendor/',import.meta.url));
function fixture(t) {
 const parent=fs.mkdtempSync(path.join(os.tmpdir(),'unicode-ci-'));
 t.after(()=>fs.rmSync(parent,{recursive:true,force:true}));
 const root=path.join(parent,'root');fs.mkdirSync(root);
 for(const dir of ['src','bin','tests','tools']) {fs.mkdirSync(path.join(root,dir));fs.writeFileSync(path.join(root,dir,'sample.mjs'),'// source\n');}
 for(const name of ['README.md','USER_GUIDE.md'])fs.writeFileSync(path.join(root,name),'Documentation\n');
 return {parent,root,write:(rel,data)=>fs.writeFileSync(path.join(root,rel),data)};
}
test('pinned generated engine matches trusted source across policy fixtures',async(t)=>{
 const {engine,provenance}=await loadPinnedEngine();
 const {parent}=fixture(t);
 // Only execute this trusted, hash-verified source snapshot. Never scanned input.
 fs.writeFileSync(path.join(parent,'package.json'),'{"type":"module"}\n');
 const source=path.join(parent,'source.ts');fs.copyFileSync(path.join(vendor,'unicode-policy.source.txt'),source);
 const upstream=await import(pathToFileURL(source).href);
 const samples=['ASCII\n','Math: '+String.fromCodePoint(0x03b1,0x2200,0x00a7,0x4e2d,0x1f600)+'\n',... [0x202e,0x200b,0xe0061,0xd800,0x2014,0xfeff,0xfe0f].map(c=>'x'+String.fromCodePoint(c)+'\n'),String.fromCodePoint(0x2705,0xfe0f)+'\n',String.fromCodePoint(0x03b1).repeat(600)+'A'.repeat(200)+'\n'];
 for(const name of ['src/example.ts','README.md','package.json','script.sh','tools/vendor/example.txt']) {
  const mode=engine.modeForPath(engine.DEFAULT_UNICODE_POLICY,name,path.matchesGlob);
  assert.equal(mode,upstream.modeForPath(upstream.DEFAULT_UNICODE_POLICY,name,path.matchesGlob));
  for(const text of samples)assert.deepEqual(engine.scanUnicode(text,mode,engine.DEFAULT_UNICODE_POLICY),upstream.scanUnicode(text,mode,upstream.DEFAULT_UNICODE_POLICY));
 }
 assert.match(provenance.source.revision,/^[a-f0-9]{40}$/);
 assert.equal(engine.scanUnicode(samples[1],'typographic-free',engine.DEFAULT_UNICODE_POLICY).total,0);
 assert.ok(engine.scanUnicode(samples[1],'ascii',engine.DEFAULT_UNICODE_POLICY).total>0);
 assert.ok(engine.scanUnicode(samples[2],'typographic-free',engine.DEFAULT_UNICODE_POLICY).total>0);
});
test('legitimate Unicode is permitted in the old source population and optional test directory',async(t)=>{
 const f=fixture(t);const content='Math: '+String.fromCodePoint(0x03b1,0x2200,0x00a7,0x4e2d,0x1f600)+'\n';
 for(const rel of ['src/sample.mjs','README.md','USER_GUIDE.md'])f.write(rel,content);
 fs.mkdirSync(path.join(f.root,'test'));f.write('test/example.mjs',content);
 const r=await checkUnicodeTree(f.root);assert.equal(r.ok,true);assert.ok(r.files.some(x=>x.path==='test/example.mjs'));
});
test('explicit machine-file ASCII scope remains enforced without banning Unicode prose',async(t)=>{
 const f=fixture(t);f.write('tools/package.json','{"name":"'+String.fromCodePoint(0x03b1)+'"}\n');
 let r=await checkUnicodeTree(f.root);assert.equal(r.ok,false);assert.ok(r.errors.some(x=>x.file==='tools/package.json' && x.kind==='outside-allowed-ranges'));
 f.write('tools/package.json','{"name":"\\u03b1"}\n');r=await checkUnicodeTree(f.root);assert.equal(r.ok,true);
});

test('recognizes only the expected ELF path and records the complete artifact hash',async(t)=>{
 const f=fixture(t),elf=Buffer.alloc(128);elf.set([0x7f,0x45,0x4c,0x46,2,1,1]);f.write('bin/lean-analyzer',elf);
 let r=await checkUnicodeTree(f.root);assert.equal(r.ok,true);assert.match(r.files.find(x=>x.path==='bin/lean-analyzer').sha256,/^[a-f0-9]{64}$/);
 f.write('src/hidden.mjs',elf);r=await checkUnicodeTree(f.root);assert.equal(r.ok,false);assert.ok(r.errors.some(x=>x.kind==='binary-format'));
});
test('malformed expected ELF is not silently skipped',async(t)=>{
 const f=fixture(t);f.write('bin/lean-analyzer',Buffer.from([0x7f,0x45,0x4c,0x46]));assert.equal((await checkUnicodeTree(f.root)).ok,false);
});
test('dangerous carriers, substitutions and BOM remain failures',async(t)=>{
 const f=fixture(t);
 for(const c of [0x202e,0x200b,0xe0061,0x2014,0xfeff]) {
  f.write('README.md',String.fromCodePoint(c)+'text\n');const r=await checkUnicodeTree(f.root);assert.equal(r.ok,false);assert.ok(r.errors.some(x=>x.codePoint===c));
 }
});
test('whole-file and per-line density restrictions are not lost',async(t)=>{
 const f=fixture(t);f.write('README.md',String.fromCodePoint(0x03b1).repeat(600)+'A'.repeat(200)+'\n');
 const r=await checkUnicodeTree(f.root);assert.equal(r.ok,false);assert.ok(r.errors.some(x=>x.kind==='ratio-exceeded'));assert.ok(r.errors.some(x=>x.kind==='line-exceeded'));
});
test('invalid UTF-8 and unclassified NUL input fail rather than becoming binary exemptions',async(t)=>{
 const f=fixture(t);
 for(const bytes of [Buffer.from([0xff,0xfe]),Buffer.from([65,0,66])]) {f.write('src/sample.mjs',bytes);assert.equal((await checkUnicodeTree(f.root)).ok,false);}
});
test('missing, empty and unreadable required paths do not pass',async(t)=>{
 const f=fixture(t);fs.unlinkSync(path.join(f.root,'README.md'));assert.equal((await checkUnicodeTree(f.root)).ok,false);
 f.write('README.md','restored');fs.unlinkSync(path.join(f.root,'src/sample.mjs'));assert.equal((await checkUnicodeTree(f.root)).ok,false);
 f.write('src/sample.mjs','restored');fs.chmodSync(path.join(f.root,'README.md'),0);assert.equal((await checkUnicodeTree(f.root)).ok,false);fs.chmodSync(path.join(f.root,'README.md'),0o600);
});
test('symlink and credential-like inputs are refused before content reads',async(t)=>{
 const f=fixture(t);fs.writeFileSync(path.join(f.parent,'sentinel'),'outside sentinel');fs.symlinkSync(path.join(f.parent,'sentinel'),path.join(f.root,'src/link.mjs'));
 let r=await checkUnicodeTree(f.root);assert.equal(r.ok,false);assert.ok(r.errors.some(x=>x.kind==='symlink'));
 fs.unlinkSync(path.join(f.root,'src/link.mjs'));
 // Metadata-only refusal witness: never create/read a credential-path fixture.
 const realReadDir=fs.readdirSync;
 const mock=t.mock.method(fs,'readdirSync',(p,...args)=>{
  const names=realReadDir(p,...args);
  return path.resolve(p)===path.join(f.root,'src')?[...names,'.env']:names;
 });
 try {r=await checkUnicodeTree(f.root);assert.equal(r.ok,false);assert.ok(r.errors.some(x=>x.kind==='excluded-sensitive-path'));}finally{mock.mock.restore();}
});
test('broken optional test-directory symlinks cannot hide source coverage',async(t)=>{
 const f=fixture(t);fs.symlinkSync(path.join(f.parent,'missing'),path.join(f.root,'test'));
 const r=await checkUnicodeTree(f.root);assert.equal(r.ok,false);assert.ok(r.errors.some(x=>x.file==='test' && x.kind==='symlink'));
});

test('read budgets fail closed, not skip to green',async(t)=>{
 const f=fixture(t);f.write('README.md','A'.repeat(100));assert.equal((await checkUnicodeTree(f.root,{maxTextBytes:50})).ok,false);
 const elf=Buffer.alloc(128);elf.set([0x7f,0x45,0x4c,0x46,2,1,1]);f.write('bin/lean-analyzer',elf);assert.equal((await checkUnicodeTree(f.root,{maxBinaryBytes:64})).ok,false);
});
test('integrity is checked before any changed artifact is imported',async(t)=>{
 const {parent}=fixture(t),copy=path.join(parent,'vendor');fs.cpSync(vendor,copy,{recursive:true});fs.appendFileSync(path.join(copy,'unicode-policy.mjs'),'\nthrow new Error("MUST_NOT_EXECUTE");\n');
 await assert.rejects(loadPinnedEngine(copy),/Engine integrity failure/);
});
test('actual legacy CI predicate rejects legitimate Unicode accepted by the pinned engine',async(t)=>{
 const f=fixture(t);f.write('README.md','Allowed section sign: '+String.fromCodePoint(0x00a7)+'\n');
 const old=spawnSync('/usr/bin/bash',['-c','! grep -rPn "[^\\x00-\\x7F]" src/ bin/ tests/ README.md USER_GUIDE.md'],{cwd:f.root,encoding:'utf8',timeout:15000,env:{PATH:process.env.PATH}});
 assert.equal(old.status,1);assert.equal((await checkUnicodeTree(f.root)).ok,true);
});

test('machine output escapes non-ASCII data without banning Unicode inputs',async(t)=>{
 const f=fixture(t),name='src/x'+String.fromCodePoint(0x202e)+'.mjs';f.write(name,String.fromCodePoint(0x202e));
 const p=spawnSync(process.execPath,[fileURLToPath(new URL('../tools/check-unicode.mjs',import.meta.url)),'--root',f.root],{encoding:'utf8',timeout:15000,env:{PATH:process.env.PATH}});
 assert.equal(p.status,1);assert.doesNotMatch(p.stdout,/[^\x00-\x7f]/);assert.equal(JSON.parse(p.stdout).ok,false);
 assert.match(safeJson({text:String.fromCodePoint(0x03b1)}),/\\u03b1/);
});
