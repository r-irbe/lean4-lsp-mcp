# bench/ - the counterexample-search verb benchmark (tranche 4)

Protocol and gate, per PLAN-LEAN-LSP-MCP-COUNTEREXAMPLE-VERB.

## Run

    npm run bench            # six statements x 3 runs + budget probe + duplicate pair
    node bench/stdio_probe.mjs   # the acceptance probe: slice survives / dense
                                 # refutes / budget wall ~= budget (needs a
                                 # fixture theorem; see LEAN_LSP_BENCH_FAR below)

Env: `LEAN_LSP_BENCH_PROJECT` overrides the Lean project cwd (default
`/home/radu/code/tacit-mui/docs/easci/lean`). The stdio probe's far
statement lives in a scratch fixture, not this corpus; point
`LEAN_LSP_BENCH_FAR` at a theorem in a file you pass via a small edit or
reuse the suite's fixture (`tests/test_counterexample_verb.mjs` case 8).

## TIMING GATE

Absolute numbers are valid **only in a quiet window** (no concurrent
lake builds or blueprint mass-edit lanes). Under load, timings are
relative-only. Record every run here.

## Recorded runs

- 2026-10-16 (UNDER LOAD, relative-only): main-phase calls 5.7-11.2s
  each (Mathlib deep-import ~5-7s + generation; list gen +4-5s); dense
  acceptance: slice survived, dense refuted via sized-wide probe
  (n := 270) 17.8s; budget wall 1.6s on a 1.5s budget (the
  process-group kill).
- 2026-10-22 first `npm run bench` from the promoted harness (UNDER
  LOAD, relative-only): 18/18 correct states (s1/s4/s5 survived,
  s2/s3 counterexample, s6 unsupported), 5.5-6.3s per call, total wall
  113.8s; budget_expired at 1.58s wall on the 1.5s budget (kill
  verified); duplicate pair identical. Faster than 2026-10-16 (the
  concurrent lane profile differed). Quick-window run: SCHEDULED (the
  one open follow-up; run `npm run bench` when the fleet is idle and
  append the numbers here).
