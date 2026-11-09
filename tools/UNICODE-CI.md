# Standalone scoped Unicode CI

Run `node tools/check-unicode.mjs`. The checker uses only Node built-ins and the pinned public `DEFAULT_UNICODE_POLICY` from the shared harness engine. It does not guess/merge private host configuration or import the MCP server. Machine-file scopes remain ASCII where configured; ordinary source/prose allow notation, scripts and emoji. No independent Unicode blacklist is maintained here.

## Pin and provenance

`vendor/unicode-policy.provenance.json` records the upstream repository, exact committed source revision/path/SHA-256, native Node type-erasure generator/version, artifact hash and license hash. The exact upstream TypeScript is retained as inert `unicode-policy.source.txt`; the checker executes only its hash-verified JavaScript artifact. The Apache-2.0 license/notice is retained alongside it.

Before loading the artifact, the checker verifies its source/license/artifact hashes. This is a reproducibility/integrity pin, not an external signature or defense against a PR rewriting both code and manifest. One writer/trusted checkout is assumed; no hostile-filesystem race or sandbox guarantee is claimed.

## Coverage and file formats

Required: `src/`, `bin/`, `tests/`, `tools/`, `README.md`, `USER_GUIDE.md`. Also scans `test/` when present. Nothing is silently pruned to make a failure pass. Missing, empty required subtrees, unreadable/symlink/special inputs, invalid UTF-8, unclassified NUL/binary data and exceeded read budgets fail. Credential-like directory entries are refused without content reads.

Only the exact `bin/lean-analyzer` path can be classified as ELF, after magic/class/endian/version/header checks. It is fully hashed and reported, not Unicode-scanned or certified executable/correct. Other ELF files fail. Text retains its BOM for the canonical policy scanner. The fixed read budgets (8MiB text/64MiB ELF) are resource controls that fail rather than skip, not contest/WASM promotion ceilings.

Shared `unrestricted` scopes remain policy exemptions and are reported as such, not counted as character-audited. Vendored engine bytes are separately hash-checked. The JSON report escapes Unicode for safe machine transport; this is not an ASCII restriction on source inputs.

CI checks the clean source population before build/tests can create fixture/cache artifacts. The existing npm test command also runs `tests/test_unicode_policy_ci.mjs`, including native-source parity, independent positive/negative cases and the actual former grep as a RED control.

## Explicit offline update

With a local source checkout whose engine and license match the selected commit:

```sh
node tools/update-unicode-engine.mjs \
  --source-root /path/to/pi-harness-bridge \
  --source-revision <40-hex-commit>
node --experimental-strip-types --test tests/test_unicode_policy_ci.mjs
node tools/check-unicode.mjs
```

Regeneration requires the `node:module.stripTypeScriptTypes` capability; it is not required by the checker. Generation was tested with Node26.5.1, its experimental warning retained. No new compiler/package/download is needed. Review the source pin, generated artifact, license and provenance together before publication. An interrupted update fails integrity checks until completed; do not weaken hashes to recover.

The checker follows the package Node>=22.6 contract; parity tests use its existing experimental type-stripping flag. Local execution evidence is Node26.5.1 only. Actual Node22 CI execution remains required and must not be inferred from version parsing, native Node26 tests or this documentation.
