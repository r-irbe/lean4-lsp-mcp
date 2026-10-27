//! src/lib.rs
//! High-Speed In-Process Abstract Interpreter and AST Evaluator for Lean 4.
//!
//! Provides:
//! - Bitset abstract sign and interval lattices.
//! - Compact Lean 4 expression representation.
//! - In-process abstract evaluation and fixpoint analysis.
//! - Zero-dependency WASM / C ABI exports.
//!
//! 

pub mod affine;
pub mod ast;
#[cfg(not(target_arch = "wasm32"))]
pub mod batch_scanner;
pub mod congruence;
pub mod ilean_parser;
pub mod interpreter;
pub mod lattice;
#[cfg(not(target_arch = "wasm32"))]
pub mod mmap_reader;
pub mod nat_interval;
pub mod octagon;
pub mod ops;
pub mod treesitter_mode;
pub mod wasm_abi;
pub mod wto;
pub mod zone;

pub use affine::{reduce_weighted_linear_two_vars, NatAffineConservation, MAX_AFFINE_VARS};
pub use ast::LeanExpr;
#[cfg(not(target_arch = "wasm32"))]
pub use batch_scanner::{BatchILeanScanner, IndexedDeclaration};
pub use congruence::{reduce_interval_congruence, NatCongruence};
pub use ilean_parser::{ILeanDecl, ILeanParser, ILeanSummary};
pub use interpreter::{DiagnosticCertificate, DiagnosticKind, LeanAbstractInterpreter};
pub use lattice::{
    AbstractBool, AbstractSign, AbstractState, FloatIntervalBound, IntervalBound, PackedSignVector,
};
#[cfg(not(target_arch = "wasm32"))]
pub use mmap_reader::MmapReader;
pub use octagon::{NatOctagonDomain, MAX_OCT_VARS};
pub use treesitter_mode::{CstNodeKind, TreeSitterCstNode, TreeSitterSExprParser};
pub use wasm_abi::*;
pub use wto::{TracePartitionedState, TraceToken, WtoElement, WtoOrdering};
pub use zone::{NatZoneDomain, MAX_ZONE_VARS};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lattice_bitwise_join_meet() {
        let zero = AbstractSign::Zero;
        let pos = AbstractSign::Positive;
        let non_neg = zero.join(pos);
        assert_eq!(non_neg, AbstractSign::NonNegative);

        let meet = non_neg.meet(pos);
        assert_eq!(meet, AbstractSign::Positive);

        let neg = AbstractSign::Negative;
        assert_eq!(non_neg.meet(neg), AbstractSign::Bottom);
        assert_eq!(pos.join(neg), AbstractSign::NonZero);
    }

    #[test]
    fn test_eval_nat_add() {
        let interp = LeanAbstractInterpreter::new();
        let expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.add".to_string())),
                Box::new(LeanExpr::LitNat(15)),
            )),
            Box::new(LeanExpr::LitNat(25)),
        );

        let state = interp.eval_expr(&expr);
        assert_eq!(state.sign, AbstractSign::Positive);
        assert_eq!(state.interval, Some(IntervalBound::new(40, 40)));
        assert!(state.is_deterministic);
        assert!(state.is_pure);
    }

    #[test]
    fn test_eval_nat_sub_mul_let() {
        let interp = LeanAbstractInterpreter::new();

        // 30 - 10 = 20
        let sub_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.sub".to_string())),
                Box::new(LeanExpr::LitNat(30)),
            )),
            Box::new(LeanExpr::LitNat(10)),
        );
        let sub_state = interp.eval_expr(&sub_expr);
        assert_eq!(sub_state.sign, AbstractSign::Positive);
        assert_eq!(sub_state.interval, Some(IntervalBound::new(20, 20)));

        // 5 * 6 = 30
        let mul_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.mul".to_string())),
                Box::new(LeanExpr::LitNat(5)),
            )),
            Box::new(LeanExpr::LitNat(6)),
        );
        let mul_state = interp.eval_expr(&mul_expr);
        assert_eq!(mul_state.sign, AbstractSign::Positive);
        assert_eq!(mul_state.interval, Some(IntervalBound::new(30, 30)));

        // let x := 7; x + 3 = 10
        let let_expr = LeanExpr::Let(
            "x".to_string(),
            Box::new(LeanExpr::Const("Nat".to_string())),
            Box::new(LeanExpr::LitNat(7)),
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::Const("Nat.add".to_string())),
                    Box::new(LeanExpr::Const("x".to_string())),
                )),
                Box::new(LeanExpr::LitNat(3)),
            )),
        );
        let let_state = interp.eval_expr(&let_expr);
        assert_eq!(let_state.sign, AbstractSign::Positive);
        assert_eq!(let_state.interval, Some(IntervalBound::new(10, 10)));
    }

    #[test]
    fn test_fixpoint_monotonicity() {
        let interp = LeanAbstractInterpreter::new();
        let init = AbstractState {
            sign: AbstractSign::Zero,
            interval: Some(IntervalBound::point(0)),
            boolean: None,
            is_deterministic: true,
            is_pure: true,
        };

        let fixpoint = interp.compute_fixpoint(
            init,
            |curr| {
                let cur_max = curr.interval.map(|i| i.max).unwrap_or(0);
                let next_max = (cur_max + 1).min(10);
                AbstractState {
                    sign: if next_max > 0 {
                        AbstractSign::Positive
                    } else {
                        AbstractSign::Zero
                    },
                    interval: Some(IntervalBound::new(0, next_max)),
                    boolean: None,
                    is_deterministic: true,
                    is_pure: true,
                }
            },
            20,
        );

        assert_eq!(fixpoint.interval.unwrap().max, 10);
        assert_eq!(fixpoint.sign, AbstractSign::NonNegative);
    }

    #[test]
    fn test_wasm_abi_functions() {
        assert_eq!(lean_analyzer_version(), 100);

        // Zero (1) | Positive (2) = NonNegative (3)
        let joined = lean_analyzer_join_signs(1, 2);
        assert_eq!(joined, 3);

        // NonNegative (3) & Positive (2) = Positive (2)
        let met = lean_analyzer_meet_signs(3, 2);
        assert_eq!(met, 2);

        let mut buf = [0i64; 2];
        let ok = lean_analyzer_eval_nat_add(10, 20, 5, 15, buf.as_mut_ptr());
        assert_eq!(ok, 1);
        assert_eq!(buf[0], 15);
        assert_eq!(buf[1], 35);

        // Test ilean wasm exports
        let json = br#"{"decls":{"SampleProject.Test":[10,0,20,5,12,0,12,10]},"directImports":[],"module":"SampleProject.Test","references":{},"version":5}"#;
        let mut ver = 0u32;
        let mut decls_count = 0u32;
        let mut imp_count = 0u32;
        let mut ref_count = 0u32;
        let res = lean_analyzer_parse_ilean_meta(
            json.as_ptr(),
            json.len(),
            &mut ver,
            &mut decls_count,
            &mut imp_count,
            &mut ref_count,
        );
        assert_eq!(res, 1);
        assert_eq!(ver, 5);
        assert_eq!(decls_count, 1);

        let mut name_buf = [0u8; 64];
        let written = lean_analyzer_find_decl_at(
            json.as_ptr(),
            json.len(),
            12,
            2,
            name_buf.as_mut_ptr(),
            name_buf.len(),
        );
        assert_eq!(written, "SampleProject.Test".len() as u32);
        let name_str = std::str::from_utf8(&name_buf[..written as usize]).unwrap();
        assert_eq!(name_str, "SampleProject.Test");
    }

    #[test]
    fn test_packed_sign_vector() {
        let mut v1 = PackedSignVector::new();
        v1.set(0, AbstractSign::Zero);
        v1.set(1, AbstractSign::Positive);
        v1.set(15, AbstractSign::Negative);

        let mut v2 = PackedSignVector::new();
        v2.set(0, AbstractSign::Positive);
        v2.set(1, AbstractSign::Positive);
        v2.set(15, AbstractSign::Zero);

        let joined = v1.join(&v2);
        assert_eq!(joined.get(0), AbstractSign::NonNegative);
        assert_eq!(joined.get(1), AbstractSign::Positive);
        assert_eq!(joined.get(15), AbstractSign::NonPositive);

        let met = v1.meet(&v2);
        assert_eq!(met.get(0), AbstractSign::Bottom);
        assert_eq!(met.get(1), AbstractSign::Positive);
        assert_eq!(met.get(15), AbstractSign::Bottom);

        assert!(met.is_le(&v1));
        assert!(v1.is_le(&joined));
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn test_batch_ilean_scanner() {
        let mut scanner = BatchILeanScanner::new();
        let json = br#"{"decls":{"Foo.bar":[1,0,2,0,1,0,1,10],"Foo.baz":[3,0,4,0,3,0,3,10]},"directImports":[],"module":"Foo","references":{},"version":5}"#;
        scanner.index_mmap_buffer(std::path::Path::new("/dummy/Foo.ilean"), json);

        assert_eq!(scanner.total_symbols(), 2);
        let decl = scanner.lookup("Foo.bar").expect("Foo.bar not found");
        assert_eq!(decl.module, "Foo");
        assert_eq!(decl.range, [1, 0, 2, 0]);

        let decls = scanner
            .module_declarations("Foo")
            .expect("module Foo not found");
        assert_eq!(decls.len(), 2);
    }

    #[test]
    fn test_eval_nat_div_mod() {
        let interp = LeanAbstractInterpreter::new();
        // 10 / 2 = 5
        let div_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.div".to_string())),
                Box::new(LeanExpr::LitNat(10)),
            )),
            Box::new(LeanExpr::LitNat(2)),
        );
        let s_div = interp.eval_expr(&div_expr);
        assert_eq!(s_div.interval, Some(IntervalBound::new(5, 5)));
        assert_eq!(s_div.sign, AbstractSign::Positive);

        // 10 % 3 = 1
        let mod_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.mod".to_string())),
                Box::new(LeanExpr::LitNat(10)),
            )),
            Box::new(LeanExpr::LitNat(3)),
        );
        let s_mod = interp.eval_expr(&mod_expr);
        assert_eq!(s_mod.interval, Some(IntervalBound::new(1, 1)));
        assert_eq!(s_mod.sign, AbstractSign::Positive);

        // Div by zero in Lean is 0
        let div0_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.div".to_string())),
                Box::new(LeanExpr::LitNat(10)),
            )),
            Box::new(LeanExpr::LitNat(0)),
        );
        let s_div0 = interp.eval_expr(&div0_expr);
        assert_eq!(s_div0.interval, Some(IntervalBound::new(0, 0)));
        assert_eq!(s_div0.sign, AbstractSign::Zero);
    }

    #[test]
    fn test_eval_relational_and_ite() {
        let interp = LeanAbstractInterpreter::new();
        // 5 <= 10 -> True
        let ble_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.ble".to_string())),
                Box::new(LeanExpr::LitNat(5)),
            )),
            Box::new(LeanExpr::LitNat(10)),
        );
        let s_ble = interp.eval_expr(&ble_expr);
        assert_eq!(s_ble.boolean, Some(AbstractBool::True));

        // 10 < 5 -> False
        let blt_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.blt".to_string())),
                Box::new(LeanExpr::LitNat(10)),
            )),
            Box::new(LeanExpr::LitNat(5)),
        );
        let s_blt = interp.eval_expr(&blt_expr);
        assert_eq!(s_blt.boolean, Some(AbstractBool::False));

        // ite (5 <= 10) 42 0 -> 42
        let ite_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::Const("ite".to_string())),
                    Box::new(ble_expr),
                )),
                Box::new(LeanExpr::LitNat(42)),
            )),
            Box::new(LeanExpr::LitNat(0)),
        );
        let s_ite = interp.eval_expr(&ite_expr);
        assert_eq!(s_ite.interval, Some(IntervalBound::new(42, 42)));
        assert_eq!(s_ite.sign, AbstractSign::Positive);
    }

    #[test]
    fn test_abstract_bool_algebra() {
        assert_eq!(
            AbstractBool::True.join(AbstractBool::False),
            AbstractBool::Top
        );
        assert_eq!(
            AbstractBool::True.meet(AbstractBool::False),
            AbstractBool::Bottom
        );
        assert_eq!(AbstractBool::True.not(), AbstractBool::False);
        assert_eq!(AbstractBool::False.not(), AbstractBool::True);
        assert_eq!(AbstractBool::Top.not(), AbstractBool::Top);
        assert_eq!(
            AbstractBool::True.and(AbstractBool::False),
            AbstractBool::False
        );
        assert_eq!(
            AbstractBool::True.or(AbstractBool::False),
            AbstractBool::True
        );
    }

    #[test]
    fn test_widening_narrowing_operators() {
        let i1 = IntervalBound::new(0, 10);
        let i2 = IntervalBound::new(0, 15);
        // Widening: upper bound grew, so jumps to i64::MAX
        let widened = i1.widen(&i2);
        assert_eq!(widened.min, 0);
        assert_eq!(widened.max, i64::MAX);

        let nat_widened = i1.nat_widen(&i2);
        assert_eq!(nat_widened.min, 0);
        assert_eq!(nat_widened.max, i64::MAX);

        // Narrowing: refines infinite upper bound back to post-fixpoint bound
        let narrowed = widened.narrow(&IntervalBound::new(0, 20));
        assert_eq!(narrowed.min, 0);
        assert_eq!(narrowed.max, 20);
    }

    #[test]
    fn test_float_interval_bound() {
        let f1 = FloatIntervalBound::new(0.0, 0.5);
        let f2 = FloatIntervalBound::new(0.2, 0.8);

        let joined = f1.join(&f2);
        assert!((joined.min - 0.0).abs() < 1e-9);
        assert!((joined.max - 0.8).abs() < 1e-9);

        let met = f1.meet(&f2);
        assert!((met.min - 0.2).abs() < 1e-9);
        assert!((met.max - 0.5).abs() < 1e-9);

        let widened = f1.widen(&FloatIntervalBound::new(0.0, 0.6));
        assert_eq!(widened.min, 0.0);
        assert_eq!(widened.max, f64::INFINITY);

        let narrowed = widened.narrow(&FloatIntervalBound::new(0.0, 0.75));
        assert_eq!(narrowed.min, 0.0);
        assert!((narrowed.max - 0.75).abs() < 1e-9);

        // Threshold widening with policy checkpoints: [0.0, 0.15, 0.5, 1.0]
        let thresholds = [0.0, 0.15, 0.5, 1.0];
        let thresh_widened = f1.widen_with_thresholds(&FloatIntervalBound::new(0.0, 0.6), &thresholds);
        assert_eq!(thresh_widened.min, 0.0);
        assert_eq!(thresh_widened.max, 1.0);
    }

    #[test]
    fn test_widening_fixpoint_acceleration() {
        let interp = LeanAbstractInterpreter::new();
        let init = AbstractState {
            sign: AbstractSign::Zero,
            interval: Some(IntervalBound::point(0)),
            boolean: None,
            is_deterministic: true,
            is_pure: true,
        };

        // Transfer function grows by +1 unbounded
        let fixpoint = interp.compute_widening_fixpoint(
            init,
            |curr| {
                let cur_max = curr.interval.map(|i| i.max).unwrap_or(0);
                AbstractState {
                    sign: AbstractSign::Positive,
                    interval: Some(IntervalBound::new(0, cur_max.saturating_add(1))),
                    boolean: None,
                    is_deterministic: true,
                    is_pure: true,
                }
            },
            3,
            10,
        );

        // At iteration 3, widening triggers jumping to i64::MAX, stabilizing immediately
        assert_eq!(fixpoint.interval.unwrap().max, i64::MAX);

        // Verify nat_widen dispatch on AbstractState::widen for NonNegative states
        let s1 = AbstractState {
            sign: AbstractSign::Positive,
            interval: Some(IntervalBound::new(5, 10)),
            boolean: None,
            is_deterministic: true,
            is_pure: true,
        };
        let s2 = AbstractState {
            sign: AbstractSign::NonNegative,
            interval: Some(IntervalBound::new(2, 12)),
            boolean: None,
            is_deterministic: true,
            is_pure: true,
        };
        let s_widened = s1.widen(&s2);
        assert_eq!(s_widened.interval, Some(IntervalBound::new(0, i64::MAX)));
        assert_eq!(s_widened.sign, AbstractSign::NonNegative);

        // Verify post-fixpoint termination and narrowing recovery in compute_widening_fixpoint
        let bounded_fp = interp.compute_widening_fixpoint(
            init,
            |curr| {
                let cur_max = curr.interval.map(|i| i.max).unwrap_or(0);
                let next_max = cur_max.saturating_add(1).min(50);
                AbstractState {
                    sign: AbstractSign::NonNegative,
                    interval: Some(IntervalBound::new(0, next_max)),
                    boolean: None,
                    is_deterministic: true,
                    is_pure: true,
                }
            },
            2,
            20,
        );
        assert_eq!(bounded_fp.interval, Some(IntervalBound::new(0, 50)));
        assert_eq!(bounded_fp.sign, AbstractSign::NonNegative);
    }

    #[test]
    fn test_abstract_bool_logic_evaluation() {
        let interp = LeanAbstractInterpreter::new();

        // Bool.not true => false
        let not_true = LeanExpr::App(
            Box::new(LeanExpr::Const("Bool.not".to_string())),
            Box::new(LeanExpr::Const("true".to_string())),
        );
        let res_not = interp.eval_expr(&not_true);
        assert_eq!(res_not.boolean, Some(AbstractBool::False));

        // Bool.and true false => false
        let and_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Bool.and".to_string())),
                Box::new(LeanExpr::Const("true".to_string())),
            )),
            Box::new(LeanExpr::Const("false".to_string())),
        );
        let res_and = interp.eval_expr(&and_expr);
        assert_eq!(res_and.boolean, Some(AbstractBool::False));

        // Bool.or false true => true
        let or_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Bool.or".to_string())),
                Box::new(LeanExpr::Const("false".to_string())),
            )),
            Box::new(LeanExpr::Const("true".to_string())),
        );
        let res_or = interp.eval_expr(&or_expr);
        assert_eq!(res_or.boolean, Some(AbstractBool::True));

        // Test WASM ABI boolean logic
        assert_eq!(wasm_abi::lean_analyzer_bool_not(2), 1); // not True => False
        assert_eq!(wasm_abi::lean_analyzer_bool_not(1), 2); // not False => True
        assert_eq!(wasm_abi::lean_analyzer_bool_and(2, 1), 1); // True and False => False
        assert_eq!(wasm_abi::lean_analyzer_bool_and(2, 2), 2); // True and True => True
        assert_eq!(wasm_abi::lean_analyzer_bool_or(1, 2), 2);  // False or True => True
        assert_eq!(wasm_abi::lean_analyzer_bool_or(1, 1), 1);  // False or False => False
    }
}

