//! Differential validation of every modelled operator against Lean 4 core.
//! The oracle table is produced by `bash tools/lean_analyzer_oracle/regen.sh`.
//! Point inputs below i64::MAX must be exact; everything else must be sound
//! (never exclude the value Lean computes). 

use lean_analyzer::ast::LeanExpr;
use lean_analyzer::congruence::{reduce_interval_congruence, NatCongruence};
use lean_analyzer::interpreter::LeanAbstractInterpreter;
use lean_analyzer::lattice::{AbstractBool, AbstractSign, AbstractState, IntervalBound};
use std::collections::HashMap;

const INF: i64 = i64::MAX;

struct Oracle {
    nat: HashMap<(String, u128, u128), Option<u128>>,
    unary_nat: HashMap<(String, u128), Option<u128>>,
    rel: HashMap<(String, u128, u128), bool>,
    boolean: Vec<(String, bool, bool, bool)>,
    bnot: Vec<(bool, bool)>,
    cond: Vec<(bool, u128, u128, u128)>,
    version: String,
}

fn load() -> Oracle {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/lean_oracle.tsv");
    let text = std::fs::read_to_string(path).expect("oracle fixture");
    let mut o = Oracle {
        nat: HashMap::new(),
        unary_nat: HashMap::new(),
        rel: HashMap::new(),
        boolean: vec![],
        bnot: vec![],
        cond: vec![],
        version: String::new(),
    };
    let pb = |s: &str| s == "true";
    for line in text.lines() {
        let f: Vec<&str> = line.split('\t').collect();
        if f[0] == "#lean-oracle" {
            o.version = f[1].to_string();
            continue;
        }
        let key = f[0].to_string();
        match key.as_str() {
            "band" | "bor" | "bxor" | "b_eq" | "b_ne" => {
                o.boolean.push((key, pb(f[1]), pb(f[2]), pb(f[3])))
            }
            "bnot" => o.bnot.push((pb(f[1]), pb(f[3]))),
            "succ" | "pred" => {
                o.unary_nat.insert(
                    (key, f[1].parse().unwrap()),
                    f[3].parse::<u128>().ok(),
                );
            }
            "cond" => {
                let (t, e) = f[2].split_once(',').unwrap();
                o.cond.push((
                    pb(f[1]),
                    t.parse().unwrap(),
                    e.parse().unwrap(),
                    f[3].parse().unwrap(),
                ));
            }
            "le" | "lt" | "ge" | "gt" | "eq" | "ne" | "ble" | "blt" | "beq" => {
                o.rel.insert((key, f[1].parse().unwrap(), f[2].parse().unwrap()), pb(f[3]));
            }
            _ => {
                // Results beyond u128 are recorded as None ("huge", >= INF).
                o.nat.insert(
                    (key, f[1].parse().unwrap(), f[2].parse().unwrap()),
                    f[3].parse::<u128>().ok(),
                );
            }
        }
    }
    o
}

/// Every interpreter name that must agree with each oracle key.
fn names(key: &str) -> Vec<&'static str> {
    match key {
        "add" => vec!["Nat.add", "HAdd.hAdd"],
        "sub" => vec!["Nat.sub", "HSub.hSub"],
        "mul" => vec!["Nat.mul", "HMul.hMul"],
        "div" => vec!["Nat.div", "HDiv.hDiv"],
        "mod" => vec!["Nat.mod", "HMod.hMod"],
        "min" => vec!["Nat.min", "min"],
        "max" => vec!["Nat.max", "max"],
        "pow" => vec!["Nat.pow", "HPow.hPow"],
        "land" => vec!["Nat.land", "AndOp.and", "HAnd.hAnd"],
        "lor" => vec!["Nat.lor", "OrOp.or", "HOr.hOr"],
        "lxor" => vec!["Nat.xor", "XorOp.xor", "HXor.hXor"],
        "shl" => vec!["Nat.shiftLeft", "HShiftLeft.hShiftLeft", "ShiftLeft.shiftLeft"],
        "shr" => vec!["Nat.shiftRight", "HShiftRight.hShiftRight", "ShiftRight.shiftRight"],
        "succ" => vec!["Nat.succ"],
        "pred" => vec!["Nat.pred"],
        "le" => vec!["LE.le"],
        "lt" => vec!["LT.lt"],
        "ge" => vec!["Nat.bge", "GE.ge"],
        "gt" => vec!["Nat.bgt", "GT.gt"],
        "eq" => vec!["Eq"],
        "ne" => vec!["Nat.bne", "Ne", "BNe.bne", "bne"],
        "ble" => vec!["Nat.ble"],
        "blt" => vec!["Nat.blt"],
        "beq" => vec!["Nat.beq", "BEq.beq"],
        "band" => vec!["Bool.and", "and", "HAnd.hAnd"],
        "bor" => vec!["Bool.or", "or", "HOr.hOr"],
        "bxor" => vec!["Bool.xor", "xor", "HXor.hXor"],
        "b_eq" => vec!["Nat.beq", "Eq", "BEq.beq"],
        "b_ne" => vec!["Nat.bne", "Ne", "BNe.bne", "bne"],
        _ => panic!("unmapped key {key}"),
    }
}

fn app1(name: &str, a: LeanExpr) -> LeanExpr {
    LeanExpr::App(Box::new(LeanExpr::Const(name.into())), Box::new(a))
}

fn app2(name: &str, a: LeanExpr, b: LeanExpr) -> LeanExpr {
    LeanExpr::App(
        Box::new(LeanExpr::App(Box::new(LeanExpr::Const(name.into())), Box::new(a))),
        Box::new(b),
    )
}

fn c(n: &str) -> LeanExpr {
    LeanExpr::Const(n.into())
}

fn nat_state(iv: IntervalBound) -> AbstractState {
    AbstractState {
        sign: AbstractSign::NonNegative,
        interval: Some(iv),
        boolean: None,
        is_deterministic: true,
        is_pure: true,
    }
    .refine_nat()
}

fn bool_state(b: AbstractBool) -> AbstractState {
    AbstractState::from_abstract_bool(b)
}

fn contains(iv: &IntervalBound, v: Option<u128>) -> bool {
    match v {
        Some(v) if v < INF as u128 => iv.min as u128 <= v && v <= iv.max as u128,
        _ => iv.max == INF,
    }
}

fn bool_ok(got: Option<AbstractBool>, want: bool) -> bool {
    match got {
        Some(AbstractBool::Top) => true,
        Some(AbstractBool::True) => want,
        Some(AbstractBool::False) => !want,
        _ => false,
    }
}

fn to_bool_state(b: bool) -> AbstractState {
    AbstractState::const_bool(b)
}

#[test]
fn oracle_matches_pinned_toolchain() {
    let o = load();
    let local_pin = concat!(env!("CARGO_MANIFEST_DIR"), "/lean/lean-toolchain");
    let pin = std::fs::read_to_string(local_pin).unwrap();
    assert!(pin.contains(&o.version), "fixture {} vs pin {}", o.version, pin.trim());
}

#[test]
fn point_inputs_agree_with_lean() {
    let o = load();
    let interp = LeanAbstractInterpreter::new();
    let mut checked = 0usize;
    for ((key, a, b), r) in &o.nat {
        let exact_in = *a < INF as u128 && *b < INF as u128;
        for name in names(key) {
            let e = app2(name, LeanExpr::LitNat(*a as u64), LeanExpr::LitNat(*b as u64));
            let s = interp.eval_expr(&e);
            let iv = s.interval.unwrap_or_else(|| panic!("{name} {a} {b}: no interval"));
            assert!(contains(&iv, *r), "{name} {a} {b}: lean={r:?} got {iv:?}");
            if exact_in {
                let want = match r {
                    Some(v) if *v < INF as u128 => IntervalBound::point(*v as i64),
                    _ => IntervalBound::point(INF),
                };
                assert_eq!(iv, want, "{name} {a} {b} must be exact");
            }
            checked += 1;
        }
    }
    for ((key, a), r) in &o.unary_nat {
        let exact_in = *a < INF as u128;
        for name in names(key) {
            let e = app1(name, LeanExpr::LitNat(*a as u64));
            let s = interp.eval_expr(&e);
            let iv = s.interval.unwrap_or_else(|| panic!("{name} {a}: no interval"));
            assert!(contains(&iv, *r), "{name} {a}: lean={r:?} got {iv:?}");
            if exact_in {
                let want = match r {
                    Some(v) if *v < INF as u128 => IntervalBound::point(*v as i64),
                    _ => IntervalBound::point(INF),
                };
                assert_eq!(iv, want, "{name} {a} must be exact");
            }
            checked += 1;
        }
    }
    for ((key, a, b), r) in &o.rel {
        let exact_in = *a < INF as u128 && *b < INF as u128;
        for name in names(key) {
            let e = app2(name, LeanExpr::LitNat(*a as u64), LeanExpr::LitNat(*b as u64));
            let got = interp.eval_expr(&e).boolean;
            assert!(bool_ok(got, *r), "{name} {a} {b}: lean={r} got {got:?}");
            if exact_in {
                let want = if *r { AbstractBool::True } else { AbstractBool::False };
                assert_eq!(got, Some(want), "{name} {a} {b} must be exact");
            }
            checked += 1;
        }
    }
    assert!(checked > 40_000, "only {checked} checks");
    eprintln!("point checks: {checked}");
}

fn intervals() -> Vec<IntervalBound> {
    let mut v = vec![];
    for l in 0..10i64 {
        for h in l..10i64 {
            v.push(IntervalBound::new(l, h));
        }
    }
    for l in [0i64, 3, 16, 255] {
        v.push(IntervalBound::new(l, INF));
    }
    v
}

fn table_values() -> Vec<u128> {
    let mut v: Vec<u128> = (0..10).collect();
    v.extend([
        15u128, 16, 17, 31, 32, 33, 63, 64, 65, 100, 255, 256, 1000, 65535, 65536,
        4294967295, 4294967296, 4611686018427387903, 4611686018427387904,
        9223372036854775807, 9223372036854775808,
    ]);
    v
}

fn inside(iv: &IntervalBound, v: u128) -> bool {
    if v >= INF as u128 {
        iv.max == INF
    } else {
        iv.min as u128 <= v && v <= iv.max as u128
    }
}

#[test]
fn interval_inputs_are_sound() {
    let o = load();
    let ivs = intervals();
    let vals = table_values();
    let mut checks = 0usize;
    let keys_nat = [
        "add", "sub", "mul", "div", "mod", "min", "max", "pow", "land", "lor", "lxor", "shl",
        "shr",
    ];
    let keys_rel = ["le", "lt", "ge", "gt", "eq", "ne", "ble", "blt", "beq"];
    for ia in &ivs {
        let mut u_interp = LeanAbstractInterpreter::new();
        u_interp.set_decl_state("x", nat_state(*ia));
        for key in ["succ", "pred"] {
            for name in names(key) {
                let s = u_interp.eval_expr(&app1(name, c("x")));
                let iv = s.interval.expect("unary nat op yields interval");
                for a in vals.iter().filter(|a| inside(ia, **a)) {
                    if let Some(r) = o.unary_nat.get(&(key.to_string(), *a)) {
                        assert!(
                            contains(&iv, *r),
                            "{name} x in {ia:?}: lean({a})={r:?} not in {iv:?}"
                        );
                        checks += 1;
                    }
                }
            }
        }
        for ib in &ivs {
            let mut interp = LeanAbstractInterpreter::new();
            interp.set_decl_state("x", nat_state(*ia));
            interp.set_decl_state("y", nat_state(*ib));
            let pairs: Vec<(u128, u128)> = vals
                .iter()
                .filter(|a| inside(ia, **a))
                .flat_map(|a| vals.iter().filter(|b| inside(ib, **b)).map(move |b| (*a, *b)))
                .collect();
            for key in keys_nat {
                for name in names(key) {
                    let s = interp.eval_expr(&app2(name, c("x"), c("y")));
                    let iv = s.interval.expect("nat op yields interval");
                    assert!(iv.min <= iv.max, "{name} {ia:?} {ib:?}: inverted {iv:?}");
                    for (a, b) in &pairs {
                        if let Some(r) = o.nat.get(&(key.to_string(), *a, *b)) {
                            assert!(
                                contains(&iv, *r),
                                "{name} x in {ia:?} y in {ib:?}: lean({a},{b})={r:?} not in {iv:?}"
                            );
                            checks += 1;
                        }
                    }
                }
            }
            for key in keys_rel {
                for name in names(key) {
                    let s = interp.eval_expr(&app2(name, c("x"), c("y")));
                    for (a, b) in &pairs {
                        if let Some(r) = o.rel.get(&(key.to_string(), *a, *b)) {
                            assert!(
                                bool_ok(s.boolean, *r),
                                "{name} x in {ia:?} y in {ib:?}: lean({a},{b})={r} got {:?}",
                                s.boolean
                            );
                            checks += 1;
                        }
                    }
                }
            }
        }
    }
    eprintln!("interval checks: {checks}");
    assert!(checks > 500_000, "only {checks}");
}

#[test]
fn boolean_operators_agree_with_lean() {
    let o = load();
    let states = [AbstractBool::False, AbstractBool::True, AbstractBool::Top];
    for (key, a, b, r) in &o.boolean {
        for name in names(key) {
            let mut interp = LeanAbstractInterpreter::new();
            interp.set_decl_state("p", to_bool_state(*a));
            interp.set_decl_state("q", to_bool_state(*b));
            let got = interp.eval_expr(&app2(name, c("p"), c("q"))).boolean;
            let want = if *r { AbstractBool::True } else { AbstractBool::False };
            assert_eq!(got, Some(want), "{name} {a} {b}");
            // every abstract superset must contain the Lean result
            for sa in states {
                for sb in states {
                    let inc = |s: AbstractBool, v: bool| {
                        s == AbstractBool::Top || (s == AbstractBool::True) == v
                    };
                    if inc(sa, *a) && inc(sb, *b) {
                        let mut i2 = LeanAbstractInterpreter::new();
                        i2.set_decl_state("p", bool_state(sa));
                        i2.set_decl_state("q", bool_state(sb));
                        let g = i2.eval_expr(&app2(name, c("p"), c("q"))).boolean;
                        assert!(bool_ok(g, *r), "{name} {sa:?} {sb:?}: lean={r} got {g:?}");
                    }
                }
            }
        }
    }
    for (a, r) in &o.bnot {
        for name in ["Bool.not", "not"] {
            let mut interp = LeanAbstractInterpreter::new();
            interp.set_decl_state("p", to_bool_state(*a));
            let e = LeanExpr::App(Box::new(c(name)), Box::new(c("p")));
            let want = if *r { AbstractBool::True } else { AbstractBool::False };
            assert_eq!(interp.eval_expr(&e).boolean, Some(want), "{name} {a}");
        }
    }
}

#[test]
fn conditionals_and_guard_refinement_agree_with_lean() {
    let o = load();
    let ivs: Vec<IntervalBound> = intervals().into_iter().filter(|i| i.max < 10).collect();
    for cs in [AbstractBool::False, AbstractBool::True, AbstractBool::Top] {
        for it in &ivs {
            for ie in &ivs {
                for name in ["ite", "cond", "bif"] {
                    let mut interp = LeanAbstractInterpreter::new();
                    interp.set_decl_state("cb", bool_state(cs));
                    interp.set_decl_state("x", nat_state(*it));
                    interp.set_decl_state("y", nat_state(*ie));
                    let e = LeanExpr::App(
                        Box::new(LeanExpr::App(
                            Box::new(LeanExpr::App(Box::new(c(name)), Box::new(c("cb")))),
                            Box::new(c("x")),
                        )),
                        Box::new(c("y")),
                    );
                    let iv = interp.eval_expr(&e).interval.expect("cond interval");
                    for (cv, t, el, r) in &o.cond {
                        let cin = cs == AbstractBool::Top || (cs == AbstractBool::True) == *cv;
                        if cin && inside(it, *t) && inside(ie, *el) {
                            assert!(contains(&iv, Some(*r)), "{name} {cs:?} {it:?} {ie:?}");
                        }
                    }
                }
            }
        }
    }
    // Verify relational guard refinement: for x in [0, 20], `if x < 5 then x else 4` has max <= 4.
    let mut interp = LeanAbstractInterpreter::new();
    interp.set_decl_state("x", nat_state(IntervalBound::new(0, 20)));
    let cond_lt = app2("Nat.blt", c("x"), LeanExpr::LitNat(5));
    let clamp = LeanExpr::App(
        Box::new(LeanExpr::App(
            Box::new(LeanExpr::App(Box::new(c("ite")), Box::new(cond_lt))),
            Box::new(c("x")),
        )),
        Box::new(LeanExpr::LitNat(4)),
    );
    let clamped = interp.eval_expr(&clamp);
    assert_eq!(clamped.interval, Some(IntervalBound::new(0, 4)));

    // Verify `if x != 0 then x else 1` refines x in [0, 10] to [1, 10] (Positive sign).
    interp.set_decl_state("x", nat_state(IntervalBound::new(0, 10)));
    let cond_ne = app2("Nat.bne", c("x"), c("Nat.zero"));
    let pos_expr = LeanExpr::App(
        Box::new(LeanExpr::App(
            Box::new(LeanExpr::App(Box::new(c("ite")), Box::new(cond_ne))),
            Box::new(c("x")),
        )),
        Box::new(LeanExpr::LitNat(1)),
    );
    let pos_state = interp.eval_expr(&pos_expr);
    assert_eq!(pos_state.interval, Some(IntervalBound::new(1, 10)));
    assert_eq!(pos_state.sign, AbstractSign::Positive);
}

#[test]
fn congruence_and_reduced_product_agree_with_lean_oracle() {
    let o = load();
    let mut checked = 0usize;

    // 1. Point inputs below u64::MAX must be sound and exact on constants.
    for ((key, a, b), r) in &o.nat {
        let Some(rv) = r else { continue };
        if *a > u64::MAX as u128 || *b > u64::MAX as u128 || *rv > u64::MAX as u128 {
            continue;
        }
        let ca = NatCongruence::singleton(*a as u64);
        let cb = NatCongruence::singleton(*b as u64);
        let res = match key.as_str() {
            "add" => Some(ca.add(&cb)),
            "sub" => Some(ca.nat_sub(&cb, *a >= *b)),
            "mul" => Some(ca.mul(&cb)),
            "mod" => Some(ca.nat_mod(&cb)),
            "shl" => Some(ca.nat_shl(&cb)),
            _ => None,
        };
        if let Some(cg) = res {
            assert!(
                cg.contains(*rv as u64),
                "congruence {key}({a}, {b}) -> {cg:?} excluded Lean oracle result {rv}"
            );
            assert_eq!(
                cg,
                NatCongruence::singleton(*rv as u64),
                "congruence {key}({a}, {b}) must be exact on constants"
            );
            checked += 1;
        }
    }

    for ((key, a), r) in &o.unary_nat {
        let Some(rv) = r else { continue };
        if *a > u64::MAX as u128 || *rv > u64::MAX as u128 {
            continue;
        }
        let ca = NatCongruence::singleton(*a as u64);
        let cg = match key.as_str() {
            "succ" => ca.nat_succ(),
            "pred" => ca.nat_pred(),
            _ => continue,
        };
        assert!(cg.contains(*rv as u64));
        assert_eq!(cg, NatCongruence::singleton(*rv as u64));
        checked += 1;
    }

    // 2. Strided congruences and Granger interval-congruence reduction over oracle grid.
    let strides = [1u64, 2, 3, 4, 5, 8, 16];
    let vals: Vec<u64> = table_values()
        .into_iter()
        .filter(|v| *v <= 1000)
        .map(|v| v as u64)
        .collect();
    for &sa in &strides {
        for oa in 0..sa {
            let ca = NatCongruence::new(sa, oa);
            for &sb in &strides {
                for ob in 0..sb {
                    let cb = NatCongruence::new(sb, ob);
                    let c_add = ca.add(&cb);
                    let c_sub = ca.nat_sub(&cb, false);
                    let c_mul = ca.mul(&cb);
                    let c_mod = ca.nat_mod(&cb);
                    let c_shl = ca.nat_shl(&cb);
                    for &va in vals.iter().filter(|&&v| ca.contains(v)) {
                        for &vb in vals.iter().filter(|&&v| cb.contains(v)) {
                            let check = |key: &str, cg: NatCongruence| -> usize {
                                if let Some(Some(rv)) =
                                    o.nat.get(&(key.to_string(), va as u128, vb as u128))
                                {
                                    if *rv <= u64::MAX as u128 {
                                        assert!(
                                            cg.contains(*rv as u64),
                                            "{key}({va} in {ca:?}, {vb} in {cb:?}) = {rv} not in {cg:?}"
                                        );
                                        return 1;
                                    }
                                }
                                0
                            };
                            checked += check("add", c_add);
                            checked += check("sub", c_sub);
                            checked += check("mul", c_mul);
                            checked += check("mod", c_mod);
                            checked += check("shl", c_shl);
                        }
                    }
                }
            }
        }
    }

    // 3. Granger reduction soundness across intervals and congruences.
    for iv in intervals() {
        for &s in &strides {
            for off in 0..s {
                let cg = NatCongruence::new(s, off);
                let red = reduce_interval_congruence(iv, cg);
                for &v in &vals {
                    if inside(&iv, v as u128) && cg.contains(v) {
                        let (r_iv, r_cg) =
                            red.unwrap_or_else(|| panic!("empty reduction on {v} in {iv:?} & {cg:?}"));
                        assert!(inside(&r_iv, v as u128) && r_cg.contains(v));
                        checked += 1;
                    }
                }
            }
        }
    }

    eprintln!("congruence + reduced-product oracle checks: {checked}");
    assert!(checked > 25_000, "only {checked} congruence oracle checks");
}

