// Source masking preserves UTF-16 offsets, including nested comments and strings.
export function stripLeanCommentsAndStrings(src: string): string {
  const out: string[] = [];
  let i = 0;
  let depth = 0;
  while (i < src.length) {
    const pair = src.slice(i, i + 2);
    if (depth > 0) {
      if (pair === "/-" || pair === "-/") {
        depth += pair === "/-" ? 1 : -1;
        out.push("  "); i += 2;
      } else { out.push(src[i] === "\n" ? "\n" : " "); i++; }
    } else if (pair === "/-") {
      depth = 1; out.push("  "); i += 2;
    } else if (pair === "--") {
      while (i < src.length && src[i] !== "\n") { out.push(" "); i++; }
    } else if (src[i] === '"') {
      out.push(" "); i++;
      while (i < src.length && src[i] !== '"') {
        if (src[i] === "\\" && i + 1 < src.length) { out.push("  "); i += 2; }
        else { out.push(src[i] === "\n" ? "\n" : " "); i++; }
      }
      if (i < src.length) { out.push(" "); i++; }
    } else { out.push(src[i]); i++; }
  }
  return out.join("");
}

const COMMAND = /(?:^|\n)\s*(?:@\[[^\n]*\]\s*)*(?:(?:private|protected|public|noncomputable|scoped)\s+)*(?:theorem|lemma|def|abbrev|axiom|example|instance|structure|class|inductive|namespace|section|end|attribute|set_option|import|open|export|syntax|macro|elab|variable|include|omit)\b|(?:^|\n)\s*#/;

/** Conservative: unsupported proof shapes are rejected, never repaired heuristically. */
export function isWholeTheoremProof(source: string, start: number, end: number, name: string): boolean {
  const clean = stripLeanCommentsAndStrings(source);
  const body = clean.slice(start, end);
  if (!/^by\b/.test(body) || COMMAND.test(body)) return false;
  const prefix = clean.slice(0, start);
  if (!/:=\s*$/.test(prefix)) return false;
  const headers = [...prefix.matchAll(/(?:^|\n)([ \t]*)(?:@\[[^\n]*\][ \t]*)*(?:(?:private|protected|public|noncomputable|scoped)[ \t]+)*(?:theorem|lemma)[ \t]+([^\s({[:]+)/g)];
  const header = headers.at(-1);
  if (!header || header[2] !== name) return false;
  const baseIndent = header[1].length;
  const headerStart = header.index + (header[0].startsWith("\n") ? 1 : 0);
  const declarationPrefix = prefix.slice(headerStart);
  // Fail closed for unknown commands too, without maintaining a command denylist.
  if (declarationPrefix.split("\n").slice(1).some(line => line.trim()
    && line.length - line.trimStart().length <= baseIndent)) return false;
  if (body.split("\n").slice(1).some(line => line.trim()
    && line.length - line.trimStart().length <= baseIndent)) return false;
  // Type-level lets contain their own assignments. Leave these uncommon headers
  // untouched rather than guessing which assignment begins the theorem proof.
  if (/\blet\b/.test(declarationPrefix)) return false;
  // A `by` nested in a binder is part of the signature, not the proof body.
  let nesting = 0;
  let outerAssignment = -1;
  for (let i = 0; i < declarationPrefix.length; i++) {
    const c = declarationPrefix[i];
    if ("([{\u27e8".includes(c)) nesting++;
    if (")]}\u27e9".includes(c)) nesting--;
    if (nesting === 0 && c === ":" && declarationPrefix[i + 1] === "=" && outerAssignment < 0) outerAssignment = i;
  }
  if (nesting !== 0) return false;
  if (outerAssignment !== declarationPrefix.search(/:=\s*$/)) return false;
  const suffix = clean.slice(end).trimStart();
  return suffix === "" || COMMAND.test("\n" + suffix) && COMMAND.exec("\n" + suffix)?.index === 0;
}

export function isSafeProofReplacement(text: string): boolean {
  const clean = stripLeanCommentsAndStrings(text);
  return !/[\r\n]/.test(text) && /^by\b/.test(clean) && !COMMAND.test(clean)
    && !/\b(?:sorry|admit|native_decide|run_tac)\b/.test(clean);
}
