//! tests/test_interval_soundness.rs
//! Exhaustive soundness, optimality, and lattice monotonicity checks of the
//! natural-number interval transfer functions against Lean 4 semantics on
//! small ranges. 

use lean_analyzer::lattice::AbstractBool;
use lean_analyzer::IntervalBound as I;

type Abs = fn(&I, &I) -> I;
type Conc = fn(i64, i64) -> i64;
type AbsRel = fn(&I, &I) -> AbstractBool;
type ConcRel = fn(i64, i64) -> bool;

fn lean_div(a: i64, b: i64) -> i64 {
    if b == 0 {
        0
    } else {
        a / b
    }
}
fn lean_mod(a: i64, b: i64) -> i64 {
    if b == 0 {
        a
    } else {
        a % b
    }
}
fn lean_pow(a: i64, b: i64) -> i64 {
    a.pow(b as u32)
}

fn subset(sub: &I, sup: &I) -> bool {
    sup.min <= sub.min && sub.max <= sup.max
}

fn check(name: &str, abs: Abs, conc: Conc, max: i64, require_exact_bounds: bool) {
    let mut failures = Vec::new();
    for al in 0..=max {
        for ah in al..=max {
            for bl in 0..=max {
                for bh in bl..=max {
                    let ia = I::new(al, ah);
                    let ib = I::new(bl, bh);
                    let r = abs(&ia, &ib);
                    let mut exact_min = i64::MAX;
                    let mut exact_max = i64::MIN;
                    for a in al..=ah {
                        for b in bl..=bh {
                            let c = conc(a, b);
                            exact_min = exact_min.min(c);
                            exact_max = exact_max.max(c);
                            if c < r.min || c > r.max {
                                failures.push(format!(
                                    "{name}([{al},{ah}],[{bl},{bh}]) = [{},{}] misses {name}({a},{b}) = {c}",
                                    r.min, r.max
                                ));
                            }
                        }
                    }
                    if require_exact_bounds && (r.min != exact_min || r.max != exact_max) {
                        failures.push(format!(
                            "{name}([{al},{ah}],[{bl},{bh}]) = [{},{}] not optimal vs exact [{exact_min},{exact_max}]",
                            r.min, r.max
                        ));
                    }
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} failures for {name}; first: {}",
        failures.len(),
        failures[0]
    );
}

fn check_monotonicity(name: &str, abs: Abs, max: i64) {
    let mut ivs = Vec::new();
    for l in 0..=max {
        for h in l..=max {
            ivs.push(I::new(l, h));
        }
    }
    ivs.push(I::new(0, i64::MAX));
    ivs.push(I::new(2, i64::MAX));
    for i1 in &ivs {
        for i1_sup in &ivs {
            if !subset(i1, i1_sup) {
                continue;
            }
            for i2 in &ivs {
                for i2_sup in &ivs {
                    if !subset(i2, i2_sup) {
                        continue;
                    }
                    let r_sub = abs(i1, i2);
                    let r_sup = abs(i1_sup, i2_sup);
                    assert!(
                        subset(&r_sub, &r_sup),
                        "{name} non-monotonic: {i1:?} <= {i1_sup:?}, {i2:?} <= {i2_sup:?} gave {r_sub:?} vs {r_sup:?}"
                    );
                }
            }
        }
    }
}

fn check_rel(name: &str, abs: AbsRel, conc: ConcRel, max: i64) {
    for al in 0..=max {
        for ah in al..=max {
            for bl in 0..=max {
                for bh in bl..=max {
                    let r = abs(&I::new(al, ah), &I::new(bl, bh));
                    let mut all_true = true;
                    let mut all_false = true;
                    for a in al..=ah {
                        for b in bl..=bh {
                            if conc(a, b) {
                                all_false = false;
                            } else {
                                all_true = false;
                            }
                        }
                    }
                    let want = if all_true {
                        AbstractBool::True
                    } else if all_false {
                        AbstractBool::False
                    } else {
                        AbstractBool::Top
                    };
                    assert_eq!(
                        r, want,
                        "{name}([{al},{ah}],[{bl},{bh}]) got {r:?}, want {want:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn nat_add_sound() {
    check("add", I::add, |a, b| a + b, 6, true);
    check_monotonicity("add", I::add, 4);
}
#[test]
fn nat_sub_sound() {
    check("nat_sub", I::nat_sub, |a, b| (a - b).max(0), 6, true);
    check_monotonicity("nat_sub", I::nat_sub, 4);
}
#[test]
fn nat_mul_sound() {
    check("mul", I::mul, |a, b| a * b, 6, true);
    check_monotonicity("mul", I::mul, 4);
}
#[test]
fn nat_div_sound() {
    check("nat_div", I::nat_div, lean_div, 8, false);
    check_monotonicity("nat_div", I::nat_div, 4);
}
#[test]
fn nat_mod_sound_and_single_bucket_optimal() {
    check("nat_mod", I::nat_mod, lean_mod, 8, false);
    check_monotonicity("nat_mod", I::nat_mod, 4);
    // Single quotient bucket [10, 11] % [4, 4] must be exact [2, 3]
    assert_eq!(I::new(10, 11).nat_mod(&I::point(4)), I::new(2, 3));
}
#[test]
fn nat_min_sound() {
    check("nat_min", I::nat_min, |a, b| a.min(b), 6, true);
    check_monotonicity("nat_min", I::nat_min, 4);
}
#[test]
fn nat_max_sound() {
    check("nat_max", I::nat_max, |a, b| a.max(b), 6, true);
    check_monotonicity("nat_max", I::nat_max, 4);
}
#[test]
fn nat_pow_sound() {
    check("nat_pow", I::nat_pow, lean_pow, 6, true);
    check_monotonicity("nat_pow", I::nat_pow, 4);
}
#[test]
fn nat_bitwise_warren_exact_and_monotonic() {
    // Warren's Hacker's Delight bounds must achieve exact min & max on every finite interval!
    check("nat_land", I::nat_land, |a, b| a & b, 15, true);
    check("nat_lor", I::nat_lor, |a, b| a | b, 15, true);
    check("nat_xor", I::nat_xor, |a, b| a ^ b, 15, true);
    check_monotonicity("nat_land", I::nat_land, 5);
    check_monotonicity("nat_lor", I::nat_lor, 5);
    check_monotonicity("nat_xor", I::nat_xor, 5);
}
#[test]
fn nat_shifts_and_unary_sound() {
    check("nat_shl", I::nat_shl, |a, b| a << b, 7, true);
    check("nat_shr", I::nat_shr, |a, b| a >> b, 7, true);
    check_monotonicity("nat_shl", I::nat_shl, 4);
    check_monotonicity("nat_shr", I::nat_shr, 4);
    for l in 0..=8 {
        for h in l..=8 {
            assert_eq!(I::new(l, h).nat_succ(), I::new(l + 1, h + 1));
            assert_eq!(I::new(l, h).nat_pred(), I::new((l - 1).max(0), (h - 1).max(0)));
        }
    }
}
#[test]
fn nat_relations_exact_on_intervals() {
    check_rel("ble", I::ble, |a, b| a <= b, 7);
    check_rel("blt", I::blt, |a, b| a < b, 7);
    check_rel("bge", I::bge, |a, b| a >= b, 7);
    check_rel("bgt", I::bgt, |a, b| a > b, 7);
    check_rel("beq", I::beq, |a, b| a == b, 7);
    check_rel("bne", I::bne, |a, b| a != b, 7);
}
