//! src/interpreter.rs
//! In-process abstract evaluation engine over LeanExpr.
//! 

use crate::ast::LeanExpr;
use crate::lattice::{AbstractBool, AbstractSign, AbstractState};
use std::collections::HashMap;

/// Actionable static diagnostic kind emitted by `LeanAbstractInterpreter::diagnose_expr`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticKind {
    /// `Nat.sub` (`a - b`) where `a <= b` always or potentially holds, truncating to `0`.
    NatSubTruncation,
    /// `Nat.div` or `Nat.mod` where divisor interval includes `0` (`a / 0 = 0`, `a % 0 = a`).
    NatDivModByZero,
    /// `ite` / `cond` / `bif` guard whose condition is statically constant (`True` or `False`).
    DeadBranch,
    /// Theorem conclusion repeats a hypothesis binder type and closes via `exact h` / `assumption` / `h.symm`.
    HypothesisEcho,
    /// Theorem conclusion is syntactically reflexive (`lhs = lhs`) closed by `rfl`.
    ReflexiveTautology,
    /// Theorem conclusion asserts `0 <= e` or `e >= 0` over `Nat` binders (trivially true on `Nat`).
    NatNonnegTriviality,
    /// Explicit underscore-prefixed or dead value binder `(_h : P)` / `(x : Nat)` never used in conclusion or proof.
    UnusedUnderscoreBinder,
    /// Executable `Bool`-returning function `def f ... : Bool` has only one-way soundness without `<->` (`iff`).
    OneWayBoolChecker,
    /// SAIR Law 6: explicit `.brecOn`, `.binductionOn`, `.below`, `.ibelow`, or `WellFounded.fix` in computational `def` blocks.
    KernelBrecOnTax,
    /// SAIR Law 14: `/ 2^k` or `% 2^k` (or `Nat.div` / `Nat.mod` by literal power of 2 >= 4) in computational `def` blocks.
    KernelPowerOfTwoDivMod,
    /// Theorem declaration with 4+ sequential numbered scalar parameters (`a0 a1 a2 a3` or `q1_n1 q1_n2 q1_n3`).
    OverConcreteFixedArity,
}

/// Structured, human-readable static diagnostic certificate with concrete fix hints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticCertificate {
    pub kind: DiagnosticKind,
    pub operator: String,
    pub summary: String,
    pub hint: String,
}

pub struct LeanAbstractInterpreter {
    environment: HashMap<String, AbstractState>,
}

impl Default for LeanAbstractInterpreter {
    fn default() -> Self {
        Self::new()
    }
}

impl LeanAbstractInterpreter {
    pub fn new() -> Self {
        Self {
            environment: HashMap::new(),
        }
    }

    pub fn set_decl_state(&mut self, name: &str, state: AbstractState) {
        self.environment.insert(name.to_string(), state);
    }

    pub fn get_decl_state(&self, name: &str) -> Option<&AbstractState> {
        self.environment.get(name)
    }

    /// Refines the environment under the assumption that `cond_expr` evaluates to `truth`.
    /// Returns `None` if the branch is provably unreachable (empty interval).
    fn refine_env_for_guard(&self, cond_expr: &LeanExpr, truth: bool) -> Option<Self> {
        if let LeanExpr::App(f, rhs) = cond_expr {
            if let LeanExpr::Const(op_name) = f.as_ref() {
                if op_name == "Bool.not" || op_name == "not" {
                    return self.refine_env_for_guard(rhs, !truth);
                }
            }
            if let LeanExpr::App(f_inner, lhs) = f.as_ref() {
                if let LeanExpr::Const(op_name) = f_inner.as_ref() {
                    if let Some(op) = crate::ops::BinOp::from_name(op_name) {
                        if let Some((var, bound_expr, flipped)) = match (lhs.as_ref(), rhs.as_ref()) {
                            (LeanExpr::Const(v), _) if self.environment.contains_key(v) => {
                                Some((v.as_str(), rhs.as_ref(), false))
                            }
                            (_, LeanExpr::Const(v)) if self.environment.contains_key(v) => {
                                Some((v.as_str(), lhs.as_ref(), true))
                            }
                            _ => None,
                        } {
                            let b_state = self.eval_expr(bound_expr).refine_nat();
                            let orig = self.environment.get(var).copied()?.refine_nat();
                            if let (Some(orig_iv), Some(b_iv)) = (orig.interval, b_state.interval) {
                                use crate::lattice::IntervalBound;
                                use crate::nat_interval::INF;
                                // Orient the relation so `var rel b_iv` holds when `truth == true`.
                                let eff_op = match (op, flipped, truth) {
                                    (crate::ops::BinOp::Le, false, true)
                                    | (crate::ops::BinOp::Ge, true, true)
                                    | (crate::ops::BinOp::Gt, false, false)
                                    | (crate::ops::BinOp::Lt, true, false) => Some(crate::ops::BinOp::Le),
                                    (crate::ops::BinOp::Lt, false, true)
                                    | (crate::ops::BinOp::Gt, true, true)
                                    | (crate::ops::BinOp::Ge, false, false)
                                    | (crate::ops::BinOp::Le, true, false) => Some(crate::ops::BinOp::Lt),
                                    (crate::ops::BinOp::Ge, false, true)
                                    | (crate::ops::BinOp::Le, true, true)
                                    | (crate::ops::BinOp::Lt, false, false)
                                    | (crate::ops::BinOp::Gt, true, false) => Some(crate::ops::BinOp::Ge),
                                    (crate::ops::BinOp::Gt, false, true)
                                    | (crate::ops::BinOp::Lt, true, true)
                                    | (crate::ops::BinOp::Le, false, false)
                                    | (crate::ops::BinOp::Ge, true, false) => Some(crate::ops::BinOp::Gt),
                                    (crate::ops::BinOp::Eq, _, true)
                                    | (crate::ops::BinOp::Ne, _, false) => Some(crate::ops::BinOp::Eq),
                                    (crate::ops::BinOp::Ne, _, true)
                                    | (crate::ops::BinOp::Eq, _, false) => Some(crate::ops::BinOp::Ne),
                                    _ => None,
                                };
                                let refined_iv = match eff_op {
                                    Some(crate::ops::BinOp::Le) => {
                                        Some(IntervalBound::new(orig_iv.min, orig_iv.max.min(b_iv.max)))
                                    }
                                    Some(crate::ops::BinOp::Lt) => {
                                        if b_iv.max == 0 {
                                            return None;
                                        }
                                        let cap = if b_iv.max == INF { INF } else { b_iv.max - 1 };
                                        Some(IntervalBound::new(orig_iv.min, orig_iv.max.min(cap)))
                                    }
                                    Some(crate::ops::BinOp::Ge) => {
                                        Some(IntervalBound::new(orig_iv.min.max(b_iv.min), orig_iv.max))
                                    }
                                    Some(crate::ops::BinOp::Gt) => {
                                        let floor = b_iv.min.saturating_add(1);
                                        Some(IntervalBound::new(orig_iv.min.max(floor), orig_iv.max))
                                    }
                                    Some(crate::ops::BinOp::Eq) => Some(IntervalBound::new(
                                        orig_iv.min.max(b_iv.min),
                                        orig_iv.max.min(b_iv.max),
                                    )),
                                    Some(crate::ops::BinOp::Ne) => {
                                        if b_iv.min == b_iv.max && b_iv.max != INF {
                                            let c = b_iv.min;
                                            let lo = if orig_iv.min == c {
                                                orig_iv.min.saturating_add(1)
                                            } else {
                                                orig_iv.min
                                            };
                                            let hi = if orig_iv.max == c {
                                                orig_iv.max - 1
                                            } else {
                                                orig_iv.max
                                            };
                                            Some(IntervalBound::new(lo, hi))
                                        } else {
                                            Some(orig_iv)
                                        }
                                    }
                                    _ => None,
                                };
                                if let Some(iv) = refined_iv {
                                    if iv.min > iv.max {
                                        return None;
                                    }
                                    let mut env = self.environment.clone();
                                    let mut new_state = orig;
                                    new_state.interval = Some(iv);
                                    env.insert(var.to_string(), new_state.refine_nat());
                                    return Some(Self { environment: env });
                                }
                            }
                        }
                        // Backward arithmetic guard propagation (`COUSOT s64.1 p1`):
                        // Handles `(v + c) rel b`, `(c + v) rel b`, and `(v - c) rel b` (or flipped).
                        if let Some((sub_expr, bound_expr, flipped)) =
                            match (lhs.as_ref(), rhs.as_ref()) {
                                (LeanExpr::App(_, _), _) => Some((lhs.as_ref(), rhs.as_ref(), false)),
                                (_, LeanExpr::App(_, _)) => Some((rhs.as_ref(), lhs.as_ref(), true)),
                                _ => None,
                            }
                        {
                            if let LeanExpr::App(sub_f, sub_r) = sub_expr {
                                if let LeanExpr::App(sub_op_expr, sub_l) = sub_f.as_ref() {
                                    if let LeanExpr::Const(sub_op_name) = sub_op_expr.as_ref() {
                                        if let Some(sub_op) = crate::ops::BinOp::from_name(sub_op_name)
                                        {
                                            let var_and_const = match (sub_op, sub_l.as_ref(), sub_r.as_ref()) {
                                                (
                                                    crate::ops::BinOp::Add,
                                                    LeanExpr::Const(v),
                                                    other,
                                                ) if self.environment.contains_key(v) => {
                                                    Some((v.as_str(), other, true))
                                                }
                                                (
                                                    crate::ops::BinOp::Add,
                                                    other,
                                                    LeanExpr::Const(v),
                                                ) if self.environment.contains_key(v) => {
                                                    Some((v.as_str(), other, true))
                                                }
                                                (
                                                    crate::ops::BinOp::Sub,
                                                    LeanExpr::Const(v),
                                                    other,
                                                ) if self.environment.contains_key(v) => {
                                                    Some((v.as_str(), other, false))
                                                }
                                                _ => None,
                                            };
                                            if let Some((var, c_expr, is_add)) = var_and_const {
                                                let c_state = self.eval_expr(c_expr).refine_nat();
                                                let b_state = self.eval_expr(bound_expr).refine_nat();
                                                let orig =
                                                    self.environment.get(var).copied()?.refine_nat();
                                                if let (Some(orig_iv), Some(c_iv), Some(b_iv)) = (
                                                    orig.interval,
                                                    c_state.interval,
                                                    b_state.interval,
                                                ) {
                                                    use crate::lattice::IntervalBound;
                                                    use crate::nat_interval::INF;
                                                    let eff_op = match (op, flipped, truth) {
                                                        (crate::ops::BinOp::Le, false, true)
                                                        | (crate::ops::BinOp::Ge, true, true)
                                                        | (crate::ops::BinOp::Gt, false, false)
                                                        | (crate::ops::BinOp::Lt, true, false) => {
                                                            Some(crate::ops::BinOp::Le)
                                                        }
                                                        (crate::ops::BinOp::Lt, false, true)
                                                        | (crate::ops::BinOp::Gt, true, true)
                                                        | (crate::ops::BinOp::Ge, false, false)
                                                        | (crate::ops::BinOp::Le, true, false) => {
                                                            Some(crate::ops::BinOp::Lt)
                                                        }
                                                        (crate::ops::BinOp::Ge, false, true)
                                                        | (crate::ops::BinOp::Le, true, true)
                                                        | (crate::ops::BinOp::Lt, false, false)
                                                        | (crate::ops::BinOp::Gt, true, false) => {
                                                            Some(crate::ops::BinOp::Ge)
                                                        }
                                                        (crate::ops::BinOp::Gt, false, true)
                                                        | (crate::ops::BinOp::Lt, true, true)
                                                        | (crate::ops::BinOp::Le, false, false)
                                                        | (crate::ops::BinOp::Ge, true, false) => {
                                                            Some(crate::ops::BinOp::Gt)
                                                        }
                                                        (crate::ops::BinOp::Eq, _, true)
                                                        | (crate::ops::BinOp::Ne, _, false) => {
                                                            Some(crate::ops::BinOp::Eq)
                                                        }
                                                        _ => None,
                                                    };
                                                    // Compute target range [t_lo, t_hi] for the sub_expr (v + c or v - c)
                                                    let target_iv = match eff_op {
                                                        Some(crate::ops::BinOp::Le) => {
                                                            Some(IntervalBound::new(0, b_iv.max))
                                                        }
                                                        Some(crate::ops::BinOp::Lt) => {
                                                            if b_iv.max == 0 {
                                                                return None;
                                                            }
                                                            let cap = if b_iv.max == INF {
                                                                INF
                                                            } else {
                                                                b_iv.max - 1
                                                            };
                                                            Some(IntervalBound::new(0, cap))
                                                        }
                                                        Some(crate::ops::BinOp::Ge) => {
                                                            Some(IntervalBound::new(b_iv.min, INF))
                                                        }
                                                        Some(crate::ops::BinOp::Gt) => {
                                                            Some(IntervalBound::new(
                                                                b_iv.min.saturating_add(1),
                                                                INF,
                                                            ))
                                                        }
                                                        Some(crate::ops::BinOp::Eq) => Some(b_iv),
                                                        _ => None,
                                                    };
                                                    if let Some(t_iv) = target_iv {
                                                        let back_iv = if is_add {
                                                            // v + c in [t_lo, t_hi]  =>  v >= max(0, t_lo - c_hi) and v <= t_hi - c_lo
                                                            if t_iv.max != INF && c_iv.min > t_iv.max {
                                                                return None;
                                                            }
                                                            let lo = if c_iv.max == INF {
                                                                0
                                                            } else {
                                                                (t_iv.min - c_iv.max).max(0)
                                                            };
                                                            let hi = if t_iv.max == INF {
                                                                INF
                                                            } else {
                                                                t_iv.max - c_iv.min
                                                            };
                                                            IntervalBound::new(lo, hi)
                                                        } else {
                                                            // v - c in [t_lo, t_hi] (Nat saturating sub):
                                                            // Lower bound: if t_lo >= 1, v - c >= t_lo requires v >= t_lo + c_lo.
                                                            // Upper bound: v - c <= t_hi allows v <= t_hi + c_hi.
                                                            let lo = if t_iv.min > 0 {
                                                                if t_iv.min == INF || c_iv.min == INF {
                                                                    INF
                                                                } else {
                                                                    t_iv.min.saturating_add(c_iv.min)
                                                                }
                                                            } else {
                                                                0
                                                            };
                                                            let hi = if t_iv.max == INF || c_iv.max == INF {
                                                                INF
                                                            } else {
                                                                t_iv.max.saturating_add(c_iv.max).min(INF)
                                                            };
                                                            IntervalBound::new(lo, hi)
                                                        };
                                                        let iv = IntervalBound::new(
                                                            orig_iv.min.max(back_iv.min),
                                                            orig_iv.max.min(back_iv.max),
                                                        );
                                                        if iv.min > iv.max {
                                                            return None;
                                                        }
                                                        let mut env = self.environment.clone();
                                                        let mut new_state = orig;
                                                        new_state.interval = Some(iv);
                                                        env.insert(
                                                            var.to_string(),
                                                            new_state.refine_nat(),
                                                        );
                                                        return Some(Self { environment: env });
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        Some(Self {
            environment: self.environment.clone(),
        })
    }

    /// Evaluates a Lean expression into its abstract state.
    pub fn eval_expr(&self, expr: &LeanExpr) -> AbstractState {
        match expr {
            LeanExpr::LitNat(val) => AbstractState::const_nat(*val),
            LeanExpr::Const(name) => {
                if name == "true" || name == "Bool.true" {
                    AbstractState::const_bool(true)
                } else if name == "false" || name == "Bool.false" {
                    AbstractState::const_bool(false)
                } else if name == "Nat.zero" {
                    AbstractState::const_nat(0)
                } else if let Some(state) = self.environment.get(name) {
                    state.refine_nat()
                } else {
                    AbstractState::top()
                }
            }
            LeanExpr::App(f, a) => {
                // Check for 3-argument operators like ite cond then_expr else_expr
                if let LeanExpr::App(f2, then_expr) = f.as_ref() {
                    if let LeanExpr::App(f1, cond_expr) = f2.as_ref() {
                        if let LeanExpr::Const(op_name) = f1.as_ref() {
                            if op_name == "ite" || op_name == "cond" || op_name == "bif" {
                                let c_state = self.eval_expr(cond_expr);
                                let else_expr = a;
                                match c_state.boolean {
                                    Some(AbstractBool::True) => {
                                        let env = self.refine_env_for_guard(cond_expr, true);
                                        return env
                                            .as_ref()
                                            .unwrap_or(self)
                                            .eval_expr(then_expr);
                                    }
                                    Some(AbstractBool::False) => {
                                        let env = self.refine_env_for_guard(cond_expr, false);
                                        return env
                                            .as_ref()
                                            .unwrap_or(self)
                                            .eval_expr(else_expr);
                                    }
                                    Some(AbstractBool::Bottom) => return AbstractState::top(),
                                    _ => {
                                        let t_env = self.refine_env_for_guard(cond_expr, true);
                                        let e_env = self.refine_env_for_guard(cond_expr, false);
                                        return match (t_env, e_env) {
                                            (Some(te), Some(ee)) => {
                                                te.eval_expr(then_expr).join(&ee.eval_expr(else_expr))
                                            }
                                            (Some(te), None) => te.eval_expr(then_expr),
                                            (None, Some(ee)) => ee.eval_expr(else_expr),
                                            (None, None) => {
                                                self.eval_expr(then_expr).join(&self.eval_expr(else_expr))
                                            }
                                        };
                                    }
                                }
                            }
                        }
                    }
                }

                // Check for 1-argument unary operators (table in ops.rs)
                if let LeanExpr::Const(op_name) = f.as_ref() {
                    if let Some(uop) = crate::ops::UnaryOp::from_name(op_name) {
                        let s = self.eval_expr(a);
                        return uop.apply(&s);
                    }
                }

                // 2-argument binary operators (table in ops.rs)
                if let LeanExpr::App(f_inner, arg1) = f.as_ref() {
                    if let LeanExpr::Const(op_name) = f_inner.as_ref() {
                        if let Some(op) = crate::ops::BinOp::from_name(op_name) {
                            let s1 = self.eval_expr(arg1);
                            let s2 = self.eval_expr(a);
                            return op.apply(&s1, &s2);
                        }
                    }
                }
                // Try beta-reduction if the head was an abstraction
                if let Some(reduced) = expr.beta_reduce_once() {
                    return self.eval_expr(&reduced);
                }
                AbstractState::top()
            }
            LeanExpr::Let(var, _ty, val, body) => {
                let val_state = self.eval_expr(val);
                let mut local_interp = LeanAbstractInterpreter {
                    environment: self.environment.clone(),
                };
                local_interp.set_decl_state(var, val_state);
                local_interp.eval_expr(body)
            }
            LeanExpr::LitStr(_) => AbstractState {
                sign: AbstractSign::Top,
                interval: None,
                boolean: None,
                is_deterministic: true,
                is_pure: true,
            },
            _ => AbstractState::top(),
        }
    }

    /// Computes a fixpoint over monotonic state transitions.
    pub fn compute_fixpoint<F>(
        &self,
        init: AbstractState,
        mut transfer: F,
        max_iter: usize,
    ) -> AbstractState
    where
        F: FnMut(&AbstractState) -> AbstractState,
    {
        let mut curr = init;
        for _ in 0..max_iter {
            let next = transfer(&curr);
            if curr == next {
                return curr;
            }
            curr = curr.join(&next);
        }
        curr
    }

    /// Computes a fixpoint with Cousot-Cousot widening and narrowing steps.
    pub fn compute_widening_fixpoint<F>(
        &self,
        init: AbstractState,
        mut transfer: F,
        widen_after_iter: usize,
        max_iter: usize,
    ) -> AbstractState
    where
        F: FnMut(&AbstractState) -> AbstractState,
    {
        let mut curr = init;
        for i in 0..max_iter {
            let next = transfer(&curr);
            if next.is_le(&curr) {
                break;
            }
            if i >= widen_after_iter {
                curr = curr.widen(&next);
            } else {
                curr = curr.join(&next);
            }
        }
        let post = transfer(&curr).refine_nat();
        curr = curr.narrow(&post).refine_nat();
        curr
    }

    /// Computes a fixpoint using threshold widening (`MOLLER-SPA s5.12 p1`, `RIVAL-YI s6.1 p1`)
    /// followed by one narrowing pass to recover exact upper bounds from loop conditions.
    pub fn compute_threshold_widening_fixpoint<F>(
        &self,
        init: AbstractState,
        mut transfer: F,
        thresholds: &[i64],
        widen_after_iter: usize,
        max_iter: usize,
    ) -> AbstractState
    where
        F: FnMut(&AbstractState) -> AbstractState,
    {
        let mut curr = init;
        for i in 0..max_iter {
            let next = transfer(&curr);
            if curr == next {
                return curr;
            }
            if i >= widen_after_iter {
                let joined = curr.join(&next);
                let widened = curr.widen_with_thresholds(&joined, thresholds);
                if widened == curr {
                    break;
                }
                curr = widened;
            } else {
                curr = curr.join(&next);
            }
        }
        let post = transfer(&curr);
        curr.narrow(&post)
    }

    /// Computes a mutual/nested recursive fixpoint over an adjacency graph `adj`
    /// using Bourdoncle's hierarchical Weak Topological Ordering (`WtoOrdering`, ).
    pub fn compute_wto_fixpoint<F>(
        &self,
        adj: &[Vec<usize>],
        entry: usize,
        init_states: &[AbstractState],
        transfer_vertex: F,
        thresholds: &[i64],
        widen_delay: usize,
        max_component_iters: usize,
    ) -> Vec<AbstractState>
    where
        F: FnMut(usize, &[AbstractState]) -> AbstractState,
    {
        let wto = crate::wto::WtoOrdering::from_adjacency(adj, entry);
        wto.solve_fixpoint(
            init_states,
            transfer_vertex,
            thresholds,
            widen_delay,
            max_component_iters,
        )
    }

    /// Evaluates a Lean expression using Bounded Trace Partitioning (`Rival & Mauborgne 2007`, ),
    /// maintaining separate `AbstractState` buckets for each control-flow branch sequence up to
    /// `max_depth` nested `ite` / `cond` / `bif` splits before folding via lattice `join`.
    pub fn eval_expr_trace_partitioned(
        &self,
        expr: &LeanExpr,
        max_depth: usize,
    ) -> crate::wto::TracePartitionedState {
        let mut out = crate::wto::TracePartitionedState::new(max_depth);
        self.eval_trace_rec(
            expr,
            crate::wto::TraceToken::root(),
            max_depth,
            &mut out,
        );
        out
    }

    fn eval_trace_rec(
        &self,
        expr: &LeanExpr,
        token: crate::wto::TraceToken,
        max_depth: usize,
        out: &mut crate::wto::TracePartitionedState,
    ) {
        if let LeanExpr::App(f, else_expr) = expr {
            if let LeanExpr::App(f2, then_expr) = f.as_ref() {
                if let LeanExpr::App(f1, cond_expr) = f2.as_ref() {
                    if let LeanExpr::Const(op_name) = f1.as_ref() {
                        if op_name == "ite" || op_name == "cond" || op_name == "bif" {
                            let c_state = self.eval_expr(cond_expr);
                            match c_state.boolean {
                                Some(AbstractBool::True) => {
                                    let tok_t = token.push_branch(1, max_depth);
                                    if let Some(te) = self.refine_env_for_guard(cond_expr, true) {
                                        te.eval_trace_rec(then_expr, tok_t, max_depth, out);
                                    } else {
                                        self.eval_trace_rec(then_expr, tok_t, max_depth, out);
                                    }
                                    return;
                                }
                                Some(AbstractBool::False) => {
                                    let tok_f = token.push_branch(0, max_depth);
                                    if let Some(ee) = self.refine_env_for_guard(cond_expr, false) {
                                        ee.eval_trace_rec(else_expr, tok_f, max_depth, out);
                                    } else {
                                        self.eval_trace_rec(else_expr, tok_f, max_depth, out);
                                    }
                                    return;
                                }
                                Some(AbstractBool::Bottom) => return,
                                _ => {
                                    let tok_t = token.push_branch(1, max_depth);
                                    let tok_f = token.push_branch(0, max_depth);
                                    if let Some(te) = self.refine_env_for_guard(cond_expr, true) {
                                        te.eval_trace_rec(then_expr, tok_t, max_depth, out);
                                    }
                                    if let Some(ee) = self.refine_env_for_guard(cond_expr, false) {
                                        ee.eval_trace_rec(else_expr, tok_f, max_depth, out);
                                    }
                                    return;
                                }
                            }
                        }
                    }
                }
            }
        }
        if let LeanExpr::Let(var, _ty, val, body) = expr {
            let val_tp = self.eval_expr_trace_partitioned(val, max_depth);
            for (sub_tok, val_state) in val_tp.partitions {
                let mut local_interp = LeanAbstractInterpreter {
                    environment: self.environment.clone(),
                };
                local_interp.set_decl_state(var, val_state);
                let mut merged_tok = token.clone();
                for &b in &sub_tok.history {
                    merged_tok = merged_tok.push_branch(b, max_depth);
                }
                local_interp.eval_trace_rec(body, merged_tok, max_depth, out);
            }
            return;
        }
        out.record(token, self.eval_expr(expr));
    }

    /// Evaluates `expr` and collects actionable static `DiagnosticCertificate` warnings
    /// (`NatSubTruncation`, `NatDivModByZero`, `DeadBranch`) across all reachable sub-expressions.
    pub fn diagnose_expr(&self, expr: &LeanExpr) -> (AbstractState, Vec<DiagnosticCertificate>) {
        let mut certs = Vec::new();
        self.collect_diagnostics(expr, &mut certs);
        (self.eval_expr(expr), certs)
    }

    /// Statically lints a Lean 4 module source string for specification and vacuity defects:
    /// `HypothesisEcho`, `ReflexiveTautology`, `NatNonnegTriviality`, `NatSubTruncation`,
    /// `UnusedUnderscoreBinder`, and `OneWayBoolChecker`.
    pub fn diagnose_source_text(&self, source_text: &str) -> Vec<DiagnosticCertificate> {
        let mut certs = Vec::new();
        let lines: Vec<&str> = source_text.lines().collect();
        let mut bool_defs: Vec<String> = Vec::new();
        let mut nat_consts: HashMap<String, u64> = HashMap::new();
        let mut theorem_headers: Vec<(String, String, String)> = Vec::new();

        let mut i = 0;
        while i < lines.len() {
            let trimmed = lines[i].trim();
            if trimmed.is_empty() || trimmed.starts_with("--") || trimmed.starts_with("/-") {
                i += 1;
                continue;
            }
            if let Some((cname, cval)) = Self::parse_nat_const_decl(trimmed) {
                nat_consts.insert(cname, cval);
            }
            if let Some(def_name) = Self::parse_bool_def_name(trimmed) {
                bool_defs.push(def_name);
            }
            if let Some((def_name, sig, body, is_noncomp, has_csimp, next_i)) =
                Self::parse_computational_def_decl(&lines, i)
            {
                if !is_noncomp && !has_csimp {
                    Self::lint_computational_def(&def_name, &sig, &body, &nat_consts, &mut certs);
                }
                i = next_i;
                continue;
            }
            if let Some((thm_name, sig, body, next_i)) = Self::parse_theorem_decl(&lines, i) {
                Self::lint_single_theorem(&thm_name, &sig, &body, &mut certs);
                theorem_headers.push((thm_name, sig, body));
                i = next_i;
                continue;
            }
            i += 1;
        }

        // Check OneWayBoolChecker across module declarations
        for fn_name in &bool_defs {
            let mut has_one_way = false;
            let mut has_iff_or_complete = false;
            let mut first_thm = String::new();
            for (thm_name, sig, _body) in &theorem_headers {
                if !Self::contains_word(sig, fn_name) {
                    continue;
                }
                if sig.contains('\u{2194}') || sig.contains("<->") || Self::contains_word(sig, "Iff") || thm_name.ends_with("_iff") {
                    has_iff_or_complete = true;
                    break;
                }
                let conc = Self::extract_conclusion_str(sig);
                if let Some(rhs) = conc.split("->").nth(1).or_else(|| conc.split('\u{2192}').nth(1)) {
                    if Self::contains_word(rhs, fn_name) {
                        has_iff_or_complete = true;
                        break;
                    }
                }
                if sig.contains("= false") && sig.contains('(') {
                    has_iff_or_complete = true;
                    break;
                }
                if sig.contains("= true") {
                    if !has_one_way {
                        first_thm = thm_name.clone();
                    }
                    has_one_way = true;
                }
            }
            if has_one_way && !has_iff_or_complete {
                certs.push(DiagnosticCertificate {
                    kind: DiagnosticKind::OneWayBoolChecker,
                    operator: fn_name.clone(),
                    summary: format!(
                        "Executable Bool checker `{fn_name}` only has one-way soundness (`{first_thm}`) without a companion `<->` (`iff`) or completeness theorem."
                    ),
                    hint: format!(
                        "Prove `{fn_name} ... = true <-> Spec ...` (Check 5 necessity and sufficiency pairing)."
                    ),
                });
            }
        }

        certs
    }

    fn parse_bool_def_name(trimmed_line: &str) -> Option<String> {
        let mut rest = trimmed_line;
        for kw in ["private ", "protected ", "public ", "scoped ", "noncomputable "] {
            if let Some(r) = rest.strip_prefix(kw) {
                rest = r.trim_start();
            }
        }
        let after_def = rest.strip_prefix("def ")?.trim_start();
        let name: String = after_def
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
            .collect();
        if name.is_empty() {
            return None;
        }
        if let Some((before_assign, _)) = after_def.split_once(":=") {
            if before_assign.trim_end().ends_with(": Bool") {
                return Some(name);
            }
        }
        None
    }

    fn is_power_of_two_ge_4(k: u64) -> bool {
        k >= 4 && (k & (k - 1)) == 0
    }

    fn parse_nat_const_decl(trimmed_line: &str) -> Option<(String, u64)> {
        let mut rest = trimmed_line;
        while rest.starts_with("@[") {
            if let Some(idx) = rest.find(']') {
                rest = rest[idx + 1..].trim_start();
            } else {
                break;
            }
        }
        loop {
            let mut matched = false;
            for kw in ["private ", "protected ", "public ", "scoped ", "noncomputable "] {
                if let Some(r) = rest.strip_prefix(kw) {
                    rest = r.trim_start();
                    matched = true;
                }
            }
            if !matched {
                break;
            }
        }
        let after_kw = rest
            .strip_prefix("abbrev ")
            .or_else(|| rest.strip_prefix("def "))?;
        let name: String = after_kw
            .trim_start()
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'' || *c == '.')
            .collect();
        if name.is_empty() {
            return None;
        }
        let (sig_part, rhs_part) = after_kw.split_once(":=")?;
        let before_assign = sig_part[name.len()..].trim();
        if !before_assign.is_empty()
            && before_assign != ": Nat"
            && before_assign != ": \u{2115}"
        {
            return None;
        }
        let rhs_clean = rhs_part
            .split("--")
            .next()
            .unwrap_or(rhs_part)
            .trim()
            .trim_matches(|c| c == '(' || c == ')')
            .trim();
        if let Some((base_s, exp_s)) = rhs_clean.split_once('^') {
            if base_s.trim() == "2" {
                if let Ok(exp) = exp_s.trim().parse::<u32>() {
                    if exp < 64 {
                        return Some((name, 1u64 << exp));
                    }
                }
            }
        }
        let val = rhs_clean.replace('_', "").parse::<u64>().ok()?;
        Some((name, val))
    }

    fn is_top_level_decl_boundary(trimmed: &str) -> bool {
        trimmed.starts_with("theorem ")
            || trimmed.starts_with("lemma ")
            || trimmed.starts_with("def ")
            || trimmed.starts_with("abbrev ")
            || trimmed.starts_with("noncomputable ")
            || trimmed.starts_with("partial ")
            || trimmed.starts_with("unsafe ")
            || trimmed.starts_with("private ")
            || trimmed.starts_with("protected ")
            || trimmed.starts_with("structure ")
            || trimmed.starts_with("inductive ")
            || trimmed.starts_with("class ")
            || trimmed.starts_with("instance ")
            || trimmed.starts_with("mutual")
            || trimmed.starts_with("namespace ")
            || trimmed.starts_with("section ")
            || trimmed.starts_with("@[")
            || trimmed.starts_with("/--")
            || trimmed.starts_with("end ")
            || trimmed == "end"
    }

    fn parse_computational_def_decl(
        lines: &[&str],
        start_idx: usize,
    ) -> Option<(String, String, String, bool, bool, usize)> {
        let base_indent = lines[start_idx].len() - lines[start_idx].trim_start().len();
        let mut first = lines[start_idx].trim();
        let mut has_csimp = first.contains("@[csimp");
        if start_idx > 0 && lines[start_idx - 1].trim().contains("@[csimp") {
            has_csimp = true;
        }
        while first.starts_with("@[") {
            if let Some(idx) = first.find(']') {
                first = first[idx + 1..].trim_start();
            } else {
                break;
            }
        }
        let mut is_noncomp = false;
        loop {
            let mut matched = false;
            for kw in ["private ", "protected ", "public ", "scoped ", "partial ", "unsafe "] {
                if let Some(r) = first.strip_prefix(kw) {
                    first = r.trim_start();
                    matched = true;
                }
            }
            if let Some(r) = first.strip_prefix("noncomputable ") {
                is_noncomp = true;
                first = r.trim_start();
                matched = true;
            }
            if !matched {
                break;
            }
        }
        let after_kw = first.strip_prefix("def ")?;
        let def_name: String = after_kw
            .trim_start()
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'' || *c == '.')
            .collect();
        if def_name.is_empty() {
            return None;
        }

        let mut combined = String::new();
        let mut j = start_idx;
        let mut found_assign = false;
        let mut is_pattern_match_def = false;
        while j < lines.len() {
            let ln = lines[j];
            let t = ln.trim();
            let indent = ln.len() - ln.trim_start().len();
            if j > start_idx && !t.is_empty() && indent <= base_indent && Self::is_top_level_decl_boundary(t) {
                break;
            }
            let code_part = ln.split("--").next().unwrap_or(ln).trim();
            if !code_part.is_empty() {
                if j > start_idx && !found_assign && code_part.starts_with("| ") {
                    if let Some((lhs, rhs)) = code_part.split_once("=>") {
                        combined.push_str(" := ");
                        combined.push_str(lhs);
                        combined.push_str(" => ");
                        combined.push_str(rhs);
                        found_assign = true;
                        is_pattern_match_def = true;
                    } else {
                        combined.push(' ');
                        combined.push_str(code_part);
                    }
                } else {
                    if !combined.is_empty() {
                        combined.push(' ');
                    }
                    combined.push_str(code_part);
                }
            }
            if code_part.contains(":=") {
                found_assign = true;
            }
            j += 1;
            if found_assign && j < lines.len() {
                let nxt = lines[j].trim();
                let nxt_indent = lines[j].len() - lines[j].trim_start().len();
                if nxt.is_empty() {
                    if is_pattern_match_def && j + 1 < lines.len() && lines[j + 1].trim().starts_with("| ") {
                        continue;
                    }
                    break;
                }
                if nxt_indent <= base_indent && (Self::is_top_level_decl_boundary(nxt) || nxt.starts_with("--")) {
                    break;
                }
            }
        }
        let (sig_part, body_part) = combined.split_once(":=")?;
        Some((
            def_name,
            sig_part.trim().to_string(),
            body_part.trim().to_string(),
            is_noncomp,
            has_csimp,
            j,
        ))
    }

    fn resolve_pow2_divisor_token(tok: &str, next_tok: Option<&str>, nat_consts: &HashMap<String, u64>) -> Option<u64> {
        let clean = tok.trim_matches(|c| c == '(' || c == ')').replace('_', "");
        if let Ok(k) = clean.parse::<u64>() {
            if Self::is_power_of_two_ge_4(k) {
                return Some(k);
            }
        }
        if let Some((base_s, exp_s)) = clean.split_once('^') {
            if base_s == "2" && !exp_s.is_empty() {
                if let Ok(exp) = exp_s.parse::<u32>() {
                    if (2..64).contains(&exp) {
                        return Some(1u64 << exp);
                    }
                }
            }
        }
        if clean == "2^" {
            if let Some(nt) = next_tok {
                if let Ok(exp) = nt.trim_matches(|c| c == '(' || c == ')').parse::<u32>() {
                    if (2..64).contains(&exp) {
                        return Some(1u64 << exp);
                    }
                }
            }
        }
        if let Some(&val) = nat_consts.get(tok) {
            if Self::is_power_of_two_ge_4(val) {
                return Some(val);
            }
        }
        None
    }

    fn lint_computational_def(
        def_name: &str,
        _sig: &str,
        body: &str,
        nat_consts: &HashMap<String, u64>,
        certs: &mut Vec<DiagnosticCertificate>,
    ) {
        // SAIR Law 6: KernelBrecOnTax
        let brec_markers = [
            ".brecOn",
            ".binductionOn",
            ".below",
            ".ibelow",
            "WellFounded.fix",
            "WellFounded.fixF",
        ];
        for marker in &brec_markers {
            if body.contains(marker) {
                certs.push(DiagnosticCertificate {
                    kind: DiagnosticKind::KernelBrecOnTax,
                    operator: def_name.to_string(),
                    summary: format!(
                        "Computational def `{def_name}` invokes `{marker}` (SAIR Law 6 brecOn/WellFounded tax)."
                    ),
                    hint: "Replace `.brecOn` / `WellFounded.fix` with structural `@Nat.rec` fuel recursion or a `@[csimp]` theorem.".to_string(),
                });
                break;
            }
        }

        // SAIR Law 14: KernelPowerOfTwoDivMod
        let tokens: Vec<&str> = body
            .split(|c: char| c.is_whitespace() || c == '(' || c == ')' || c == '[' || c == ']' || c == ',')
            .filter(|s| !s.is_empty())
            .collect();
        for idx in 0..tokens.len() {
            let tok = tokens[idx];
            if (tok == "/" || tok == "%") && idx + 1 < tokens.len() {
                let next_after = if idx + 2 < tokens.len() {
                    Some(tokens[idx + 2])
                } else {
                    None
                };
                let mut resolved = Self::resolve_pow2_divisor_token(tokens[idx + 1], next_after, nat_consts);
                if resolved.is_none()
                    && tokens[idx + 1] == "2"
                    && idx + 3 < tokens.len()
                    && tokens[idx + 2] == "^"
                {
                    if let Ok(exp) = tokens[idx + 3].parse::<u32>() {
                        if (2..64).contains(&exp) {
                            resolved = Some(1u64 << exp);
                        }
                    }
                }
                if let Some(k) = resolved {
                    let shift = k.trailing_zeros();
                    let mask = k - 1;
                    certs.push(DiagnosticCertificate {
                        kind: DiagnosticKind::KernelPowerOfTwoDivMod,
                        operator: def_name.to_string(),
                        summary: format!(
                            "Computational def `{def_name}` uses `{tok} {k}` by power-of-2 >= 4 (SAIR Law 14)."
                        ),
                        hint: format!(
                            "Replace `/ {k}` with bitwise shift `>>> {shift}` (`Nat.shiftRight`) or `% {k}` with bitwise mask `&&& {mask}` (`Nat.land`)."
                        ),
                    });
                    break;
                }
            }
            if (tok == "Nat.div" || tok == "Nat.mod" || tok == "HDiv.hDiv" || tok == "HMod.hMod")
                && idx + 2 < tokens.len()
            {
                let next_after = if idx + 3 < tokens.len() {
                    Some(tokens[idx + 3])
                } else {
                    None
                };
                if let Some(k) = Self::resolve_pow2_divisor_token(tokens[idx + 2], next_after, nat_consts) {
                    let shift = k.trailing_zeros();
                    let mask = k - 1;
                    certs.push(DiagnosticCertificate {
                        kind: DiagnosticKind::KernelPowerOfTwoDivMod,
                        operator: def_name.to_string(),
                        summary: format!(
                            "Computational def `{def_name}` applies `{tok}` by power-of-2 `{k}` >= 4 (SAIR Law 14)."
                        ),
                        hint: format!(
                            "Replace `{tok} _ {k}` with `Nat.shiftRight _ {shift}` (`>>> {shift}`) or `Nat.land _ {mask}` (`&&& {mask}`)."
                        ),
                    });
                    break;
                }
            }
        }
    }

    fn split_trailing_digits(name: &str) -> Option<(&str, u64)> {
        let trimmed = name.trim_end_matches('\'');
        let digit_len = trimmed
            .chars()
            .rev()
            .take_while(|c| c.is_ascii_digit())
            .count();
        if digit_len == 0 || digit_len == trimmed.len() {
            return None;
        }
        let split_at = trimmed.len() - digit_len;
        let prefix = &trimmed[..split_at];
        let num = trimmed[split_at..].parse::<u64>().ok()?;
        Some((prefix, num))
    }

    fn parse_theorem_decl(lines: &[&str], start_idx: usize) -> Option<(String, String, String, usize)> {
        let mut first = lines[start_idx].trim();
        while first.starts_with("@[") {
            if let Some(idx) = first.find(']') {
                first = first[idx + 1..].trim_start();
            } else {
                break;
            }
        }
        for kw in ["private ", "protected ", "public ", "scoped ", "noncomputable "] {
            if let Some(r) = first.strip_prefix(kw) {
                first = r.trim_start();
            }
        }
        let after_kw = first
            .strip_prefix("theorem ")
            .or_else(|| first.strip_prefix("lemma "))?;
        let thm_name: String = after_kw
            .trim_start()
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
            .collect();
        if thm_name.is_empty() {
            return None;
        }

        let mut combined = String::new();
        let mut j = start_idx;
        let mut found_assign = false;
        while j < lines.len() {
            let ln = lines[j];
            let base_indent = lines[start_idx].len() - lines[start_idx].trim_start().len();
            let ln_indent = ln.len() - ln.trim_start().len();
            if j > start_idx && !ln.trim().is_empty() && ln_indent <= base_indent {
                let t = ln.trim();
                if Self::is_top_level_decl_boundary(t) {
                    break;
                }
            }
            if !combined.is_empty() {
                combined.push(' ');
            }
            combined.push_str(ln.trim());
            if ln.contains(":=") {
                found_assign = true;
            }
            j += 1;
            if found_assign && j < lines.len() {
                let nxt = lines[j].trim();
                if nxt.is_empty()
                    || (!lines[j].starts_with(' ')
                        && !lines[j].starts_with('\t')
                        && (nxt.starts_with("theorem ")
                            || nxt.starts_with("lemma ")
                            || nxt.starts_with("def ")
                            || nxt.starts_with("/--")
                            || nxt.starts_with("--")))
                {
                    break;
                }
            }
        }
        let (sig_part, body_part) = combined.split_once(":=")?;
        Some((thm_name, sig_part.trim().to_string(), body_part.trim().to_string(), j))
    }

    fn extract_binders_and_types(sig: &str) -> Vec<(Vec<String>, String, char)> {
        let mut out = Vec::new();
        let bytes = sig.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            let open_b = bytes[i];
            let close_b = match open_b {
                b'(' => Some(b')'),
                b'{' => Some(b'}'),
                b'[' => Some(b']'),
                _ => None,
            };
            if let Some(cb) = close_b {
                let mut depth = 1usize;
                let mut k = i + 1;
                let mut colon_pos = None;
                while k < bytes.len() && depth > 0 {
                    if bytes[k] == open_b {
                        depth += 1;
                    } else if bytes[k] == cb {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    } else if bytes[k] == b':' && depth == 1 && colon_pos.is_none() {
                        colon_pos = Some(k);
                    }
                    k += 1;
                }
                if depth == 0 {
                    if let Some(cp) = colon_pos {
                        let names_str = &sig[i + 1..cp];
                        let ty_str = sig[cp + 1..k].trim().to_string();
                        let names: Vec<String> = names_str
                            .split_whitespace()
                            .map(|s| s.trim().to_string())
                            .filter(|s| !s.is_empty())
                            .collect();
                        out.push((names, ty_str, open_b as char));
                    }
                    i = k + 1;
                    continue;
                }
            } else if open_b == b':' {
                break;
            }
            i += 1;
        }
        out
    }

    fn extract_conclusion_str(sig: &str) -> String {
        let bytes = sig.as_bytes();
        let mut depth = 0i32;
        for i in 0..bytes.len() {
            match bytes[i] {
                b'(' | b'{' | b'[' => depth += 1,
                b')' | b'}' | b']' => depth -= 1,
                b':' if depth == 0 => {
                    if i + 1 < bytes.len() && bytes[i + 1] == b'=' {
                        break;
                    }
                    return sig[i + 1..].trim().to_string();
                }
                _ => {}
            }
        }
        String::new()
    }

    fn contains_word(haystack: &str, needle: &str) -> bool {
        if needle.is_empty() {
            return false;
        }
        let h_bytes = haystack.as_bytes();
        let n_bytes = needle.as_bytes();
        if n_bytes.len() > h_bytes.len() {
            return false;
        }
        let is_word = |b: u8| b.is_ascii_alphanumeric() || b == b'_' || b == b'\'';
        for i in 0..=(h_bytes.len() - n_bytes.len()) {
            if &h_bytes[i..i + n_bytes.len()] == n_bytes {
                let prev_ok = i == 0 || !is_word(h_bytes[i - 1]);
                let next_ok = i + n_bytes.len() == h_bytes.len() || !is_word(h_bytes[i + n_bytes.len()]);
                if prev_ok && next_ok {
                    return true;
                }
            }
        }
        false
    }

    fn lint_single_theorem(
        thm_name: &str,
        sig: &str,
        body: &str,
        certs: &mut Vec<DiagnosticCertificate>,
    ) {
        let binders = Self::extract_binders_and_types(sig);
        let conc = Self::extract_conclusion_str(sig);
        let body_clean = body.strip_prefix("by ").unwrap_or(body).trim();

        // 1. HypothesisEcho
        let is_echo_closer = body_clean == "assumption"
            || body_clean == "trivial"
            || body_clean.starts_with("exact ")
            || body_clean.ends_with(".symm")
            || (body_clean.starts_with('\u{27e8}') && body_clean.ends_with('\u{27e9}'))
            || body_clean.starts_with("And.intro ")
            || binders.iter().any(|(ns, _, _)| ns.iter().any(|n| n == body_clean));

        if is_echo_closer && !conc.is_empty() {
            for (_names, ty, _) in &binders {
                if ty == &conc {
                    certs.push(DiagnosticCertificate {
                        kind: DiagnosticKind::HypothesisEcho,
                        operator: thm_name.to_string(),
                        summary: format!(
                            "Theorem `{thm_name}` conclusion `{conc}` repeats hypothesis `{ty}` and closes via `{body_clean}`."
                        ),
                        hint: "Prove a non-trivial consequence or unfold the underlying definition instead of echoing a hypothesis.".to_string(),
                    });
                    break;
                }
                if let Some((l, r)) = ty.split_once(" = ") {
                    let swapped = format!("{} = {}", r.trim(), l.trim());
                    if swapped == conc {
                        certs.push(DiagnosticCertificate {
                            kind: DiagnosticKind::HypothesisEcho,
                            operator: thm_name.to_string(),
                            summary: format!(
                                "Theorem `{thm_name}` conclusion `{conc}` is a symmetric echo of hypothesis `{ty}` closed via `{body_clean}`."
                            ),
                            hint: "State a substantive equality rather than restating a symmetric hypothesis.".to_string(),
                        });
                        break;
                    }
                }
            }
        }

        // 2. ReflexiveTautology
        if (body_clean == "rfl" || body_clean == "exact rfl" || body_clean == "Eq.refl") && !conc.is_empty() {
            if let Some((lhs, rhs)) = conc.split_once(" = ") {
                if lhs.trim() == rhs.trim() && !lhs.trim().is_empty() {
                    certs.push(DiagnosticCertificate {
                        kind: DiagnosticKind::ReflexiveTautology,
                        operator: thm_name.to_string(),
                        summary: format!(
                            "Theorem `{thm_name}` conclusion `{conc}` is syntactically reflexive (`lhs = lhs`) and closed by `rfl`."
                        ),
                        hint: "Relate distinct implementation and specification expressions rather than `e = e`.".to_string(),
                    });
                }
            }
        }

        // 3. NatNonnegTriviality & NatSubTruncation on Nat binders
        let mut nat_vars: Vec<String> = Vec::new();
        let mut hyp_types: Vec<String> = Vec::new();
        for (names, ty, _) in &binders {
            if ty == "Nat" || ty == "\u{2115}" {
                nat_vars.extend(names.iter().cloned());
            } else {
                hyp_types.push(ty.clone());
            }
        }
        if !nat_vars.is_empty() && !conc.is_empty() {
            let is_nonneg_conc = conc.ends_with(">= 0")
                || conc.ends_with("\u{2265} 0")
                || conc.starts_with("0 <=")
                || conc.starts_with("0 \u{2264}");
            if is_nonneg_conc && nat_vars.iter().any(|v| Self::contains_word(&conc, v)) {
                certs.push(DiagnosticCertificate {
                    kind: DiagnosticKind::NatNonnegTriviality,
                    operator: thm_name.to_string(),
                    summary: format!(
                        "Theorem `{thm_name}` conclusion `{conc}` asserts `>= 0` over `Nat`, which holds trivially for all `Nat`."
                    ),
                    hint: "State a positive lower bound (`>= 1`), an exact identity, or cast to `Int`.".to_string(),
                });
            }

            // Check unguarded `a - b` on Nat binders across hypotheses and conclusion
            let mut prop_clauses = hyp_types.clone();
            for part in conc.split("->") {
                for subpart in part.split('\u{2192}') {
                    let trimmed = subpart.trim();
                    if !trimmed.is_empty() {
                        prop_clauses.push(trimmed.to_string());
                    }
                }
            }
            let mut reported_sub = false;
            for (c_idx, clause) in prop_clauses.iter().enumerate() {
                if reported_sub {
                    break;
                }
                let other_hyps: Vec<String> = prop_clauses
                    .iter()
                    .enumerate()
                    .filter(|(idx, _)| *idx != c_idx)
                    .map(|(_, s)| s.clone())
                    .collect();
                for v in &nat_vars {
                    let pat = format!("{v} - ");
                    let mut search_from = 0usize;
                    while let Some(rel_pos) = clause[search_from..].find(&pat) {
                        let pos = search_from + rel_pos;
                        search_from = pos + pat.len();
                        let is_word = |b: u8| b.is_ascii_alphanumeric() || b == b'_' || b == b'\'';
                        if pos > 0 && is_word(clause.as_bytes()[pos - 1]) {
                            continue;
                        }
                        let before = clause[..pos].trim_end();
                        if !before.is_empty() {
                            if before.ends_with(')') || before.ends_with(']') {
                                continue;
                            }
                            let tok_start = before
                                .rfind(|c: char| !c.is_ascii_alphanumeric() && c != '_' && c != '\'' && c != '.')
                                .map(|idx| idx + 1)
                                .unwrap_or(0);
                            let prev_tok = &before[tok_start..];
                            if !prev_tok.is_empty()
                                && !matches!(
                                    prev_tok,
                                    "then" | "else" | "in" | "fun" | "let" | "have" | "return" | "by"
                                )
                            {
                                continue;
                            }
                        }
                        let after = &clause[pos + pat.len()..];
                        let rhs: String = after
                            .chars()
                            .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
                            .collect();
                        if rhs.is_empty() || rhs == "0" || &rhs == v {
                            continue;
                        }
                        let rhs_is_num = rhs.chars().all(|c| c.is_ascii_digit());
                        if !rhs_is_num {
                            if !nat_vars.contains(&rhs) {
                                continue;
                            }
                            let after_rhs = &after[rhs.len()..];
                            if after_rhs.starts_with('.') {
                                continue;
                            }
                            if after_rhs.starts_with(|c: char| c.is_whitespace()) {
                                let trimmed_after = after_rhs.trim_start();
                                if let Some(first_ch) = trimmed_after.chars().next() {
                                    if first_ch.is_ascii_alphanumeric() || first_ch == '_' || first_ch == '\'' || first_ch == '(' {
                                        let next_tok: String = trimmed_after
                                            .chars()
                                            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '\'')
                                            .collect();
                                        if !matches!(next_tok.as_str(), "then" | "else" | "with" | "by") {
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                        let guarded = other_hyps.iter().any(|h| {
                            if !Self::contains_word(h, v) {
                                return false;
                            }
                            if rhs_is_num {
                                if h.contains(&format!("{v} > 0"))
                                    || h.contains(&format!("0 < {v}"))
                                    || h.contains(&format!("{v} != 0"))
                                    || h.contains(&format!("{v} \u{2260} 0"))
                                    || h.contains(&format!("{v} >="))
                                    || h.contains(&format!("{v} \u{2265}"))
                                    || h.contains(&format!("<= {v}"))
                                    || h.contains(&format!("\u{2264} {v}"))
                                    || h.contains(&format!("< {v}"))
                                    || h.contains(&format!("{v} >"))
                                {
                                    return true;
                                }
                                if rhs == "1" && h.contains('+') && h.contains('=') {
                                    return true;
                                }
                            }
                            let has_rhs = Self::contains_word(h, &rhs) || rhs_is_num;
                            if !has_rhs {
                                return false;
                            }
                            if let Some(v_pos) = h.find(v.as_str()) {
                                if let Some(r_pos) = h.find(rhs.as_str()) {
                                    if r_pos < v_pos
                                        && (h.contains("<=")
                                            || h.contains('\u{2264}')
                                            || h.contains('<'))
                                    {
                                        return true;
                                    }
                                    if v_pos < r_pos
                                        && (h.contains(">=")
                                            || h.contains('\u{2265}')
                                            || h.contains('>'))
                                    {
                                        return true;
                                    }
                                    if h.contains('=')
                                        && !h.contains("!=")
                                        && !h.contains('\u{2260}')
                                        && !h.contains("<=")
                                        && !h.contains(">=")
                                        && !h.contains('\u{2264}')
                                        && !h.contains('\u{2265}')
                                    {
                                        if let Some((eq_l, eq_r)) = h.split_once('=') {
                                            let l_trim = eq_l.trim();
                                            let r_trim = eq_r.trim();
                                            if (l_trim == v && r_trim == rhs)
                                                || (l_trim == rhs && r_trim == v)
                                            {
                                                return true;
                                            }
                                            if (l_trim == v && Self::contains_word(r_trim, &rhs) && r_trim.contains('+'))
                                                || (r_trim == v && Self::contains_word(l_trim, &rhs) && l_trim.contains('+'))
                                            {
                                                return true;
                                            }
                                            if l_trim == rhs && Self::contains_word(r_trim, v) && r_trim.contains('-') {
                                                return true;
                                            }
                                        }
                                    }
                                }
                            }
                            false
                        });
                        if !guarded {
                            certs.push(DiagnosticCertificate {
                                kind: DiagnosticKind::NatSubTruncation,
                                operator: thm_name.to_string(),
                                summary: format!(
                                    "Theorem `{thm_name}` contains unguarded Nat subtraction `{v} - {rhs}` without `{rhs} <= {v}`."
                                ),
                                hint: format!(
                                    "Add guard `({rhs} <= {v})` or rewrite in additive form to prevent truncating subtraction at 0."
                                ),
                            });
                            reported_sub = true;
                            break;
                        }
                    }
                    if reported_sub {
                        break;
                    }
                }
            }
        }

        // 4. UnusedUnderscoreBinder (and dead value binders)
        for (idx, (names, ty, bracket)) in binders.iter().enumerate() {
            let is_val_ty = matches!(
                ty.as_str(),
                "Nat" | "\u{2115}" | "Int" | "\u{2124}" | "Bool" | "UInt8" | "UInt16" | "UInt32" | "UInt64"
            );
            for name in names {
                if name == "_" {
                    continue;
                }
                let is_underscore = name.starts_with('_');
                if *bracket != '(' && !is_underscore {
                    continue;
                }
                if !is_underscore && !is_val_ty {
                    continue;
                }
                let used_in_conc = Self::contains_word(&conc, name);
                let used_in_other = binders
                    .iter()
                    .enumerate()
                    .any(|(o_idx, (_, o_ty, _))| o_idx != idx && Self::contains_word(o_ty, name));
                let used_in_body = Self::contains_word(body_clean, name);
                if !used_in_conc && !used_in_other && !used_in_body {
                    certs.push(DiagnosticCertificate {
                        kind: DiagnosticKind::UnusedUnderscoreBinder,
                        operator: thm_name.to_string(),
                        summary: format!(
                            "Binder `{name} : {ty}` in `{thm_name}` is never referenced in conclusion, hypotheses, or proof body."
                        ),
                        hint: "Remove the dead binder or tighten the conclusion so it depends on the parameter.".to_string(),
                    });
                }
            }
        }

        // 5. OverConcreteFixedArity: 4+ sequential numbered scalar parameters (`a0 a1 a2 a3` or `q1_n1 q1_n2 q1_n3`)
        let mut prefix_groups: HashMap<String, Vec<(String, u64)>> = HashMap::new();
        for (names, _ty, _bracket) in &binders {
            for name in names {
                if name == "_" || name.starts_with('_') {
                    continue;
                }
                if let Some((prefix, num)) = Self::split_trailing_digits(name) {
                    prefix_groups
                        .entry(prefix.to_string())
                        .or_default()
                        .push((name.clone(), num));
                }
            }
        }
        let mut prefix_keys: Vec<String> = prefix_groups.keys().cloned().collect();
        prefix_keys.sort();
        for prefix in prefix_keys {
            if let Some(items) = prefix_groups.get(&prefix) {
                let threshold = if prefix.contains('_') { 3 } else { 4 };
                if items.len() >= threshold {
                    let mut nums: Vec<u64> = items.iter().map(|(_, n)| *n).collect();
                    nums.sort_unstable();
                    nums.dedup();
                    if nums.len() >= threshold {
                        let is_seq = nums.windows(2).all(|w| w[1] == w[0] + 1);
                        if is_seq {
                            let param_list: Vec<String> =
                                items.iter().map(|(nm, _)| nm.clone()).collect();
                            certs.push(DiagnosticCertificate {
                                kind: DiagnosticKind::OverConcreteFixedArity,
                                operator: thm_name.to_string(),
                                summary: format!(
                                    "Theorem `{thm_name}` has {} sequential numbered scalar parameters ({}) with prefix `{prefix}`.",
                                    items.len(),
                                    param_list.join(" ")
                                ),
                                hint: "Generalize fixed-arity scalar parameters (`a0 a1 a2 a3 ...`) to a `List` or `Fin n -> Nat` induction theorem.".to_string(),
                            });
                            break;
                        }
                    }
                }
            }
        }
    }


    fn collect_diagnostics(&self, expr: &LeanExpr, certs: &mut Vec<DiagnosticCertificate>) {
        match expr {
            LeanExpr::App(f, a) => {
                // 3-argument conditional: ite / cond / bif
                if let LeanExpr::App(f2, then_expr) = f.as_ref() {
                    if let LeanExpr::App(f1, cond_expr) = f2.as_ref() {
                        if let LeanExpr::Const(op_name) = f1.as_ref() {
                            if op_name == "ite" || op_name == "cond" || op_name == "bif" {
                                self.collect_diagnostics(cond_expr, certs);
                                let c_state = self.eval_expr(cond_expr);
                                let else_expr = a;
                                match c_state.boolean {
                                    Some(AbstractBool::True) => {
                                        certs.push(DiagnosticCertificate {
                                            kind: DiagnosticKind::DeadBranch,
                                            operator: op_name.clone(),
                                            summary: format!(
                                                "Condition in `{op_name}` is statically True; else-branch is unreachable."
                                            ),
                                            hint: "Simplify conditional to its then-branch or strengthen guard.".to_string(),
                                        });
                                        if let Some(te) = self.refine_env_for_guard(cond_expr, true) {
                                            te.collect_diagnostics(then_expr, certs);
                                        } else {
                                            self.collect_diagnostics(then_expr, certs);
                                        }
                                        return;
                                    }
                                    Some(AbstractBool::False) => {
                                        certs.push(DiagnosticCertificate {
                                            kind: DiagnosticKind::DeadBranch,
                                            operator: op_name.clone(),
                                            summary: format!(
                                                "Condition in `{op_name}` is statically False; then-branch is unreachable."
                                            ),
                                            hint: "Simplify conditional to its else-branch or check guard direction.".to_string(),
                                        });
                                        if let Some(ee) = self.refine_env_for_guard(cond_expr, false) {
                                            ee.collect_diagnostics(else_expr, certs);
                                        } else {
                                            self.collect_diagnostics(else_expr, certs);
                                        }
                                        return;
                                    }
                                    _ => {
                                        if let Some(te) = self.refine_env_for_guard(cond_expr, true) {
                                            te.collect_diagnostics(then_expr, certs);
                                        }
                                        if let Some(ee) = self.refine_env_for_guard(cond_expr, false) {
                                            ee.collect_diagnostics(else_expr, certs);
                                        }
                                        return;
                                    }
                                }
                            }
                        }
                    }
                }

                // 2-argument binary operator
                if let LeanExpr::App(f_inner, arg1) = f.as_ref() {
                    if let LeanExpr::Const(op_name) = f_inner.as_ref() {
                        if let Some(op) = crate::ops::BinOp::from_name(op_name) {
                            self.collect_diagnostics(arg1, certs);
                            self.collect_diagnostics(a, certs);
                            if matches!(op, crate::ops::BinOp::Div | crate::ops::BinOp::Mod) {
                                if let LeanExpr::LitNat(k) = a.as_ref() {
                                    if Self::is_power_of_two_ge_4(*k) {
                                        let shift = k.trailing_zeros();
                                        let mask = k - 1;
                                        certs.push(DiagnosticCertificate {
                                            kind: DiagnosticKind::KernelPowerOfTwoDivMod,
                                            operator: op_name.clone(),
                                            summary: format!(
                                                "`{op_name}` by literal power-of-2 `{k}` >= 4 (SAIR Law 14)."
                                            ),
                                            hint: format!(
                                                "Replace `{op_name}` by `{k}` with `Nat.shiftRight` (`>>> {shift}`) or `Nat.land` (`&&& {mask}`)."
                                            ),
                                        });
                                    }
                                }
                            }
                            let s1 = self.eval_expr(arg1).refine_nat();
                            let s2 = self.eval_expr(a).refine_nat();
                            if let (Some(iv1), Some(iv2)) = (s1.interval, s2.interval) {
                                match op {
                                    crate::ops::BinOp::Sub => {
                                        if iv1.max <= iv2.min && iv2.min > 0 {
                                            certs.push(DiagnosticCertificate {
                                                kind: DiagnosticKind::NatSubTruncation,
                                                operator: op_name.clone(),
                                                summary: format!(
                                                    "Natural subtraction `{op_name}` on [{}, {}] - [{}, {}] saturates to [0, 0].",
                                                    iv1.min, iv1.max, iv2.min, iv2.max
                                                ),
                                                hint: "Add guard `b <= a` or switch to `Int` subtraction if negative values are intended.".to_string(),
                                            });
                                        }
                                    }
                                    crate::ops::BinOp::Div | crate::ops::BinOp::Mod => {
                                        if iv2.min <= 0 && 0 <= iv2.max {
                                            certs.push(DiagnosticCertificate {
                                                kind: DiagnosticKind::NatDivModByZero,
                                                operator: op_name.clone(),
                                                summary: format!(
                                                    "Divisor interval [{}, {}] in `{op_name}` includes 0 (Lean total semantics: a / 0 = 0, a % 0 = a).",
                                                    iv2.min, iv2.max
                                                ),
                                                hint: "Prove divisor `d > 0` (`d != 0`) before dividing to avoid total-zero fallback.".to_string(),
                                            });
                                        }
                                    }
                                    crate::ops::BinOp::Eq => {
                                        if arg1 == a {
                                            certs.push(DiagnosticCertificate {
                                                kind: DiagnosticKind::ReflexiveTautology,
                                                operator: op_name.clone(),
                                                summary: format!(
                                                    "Equality `{op_name}` has identical LHS and RHS sub-expressions."
                                                ),
                                                hint: "Relate distinct implementation and specification expressions instead of `e = e`.".to_string(),
                                            });
                                        }
                                    }
                                    crate::ops::BinOp::Ge => {
                                        if matches!(a.as_ref(), LeanExpr::LitNat(0)) && iv1.min >= 0 {
                                            certs.push(DiagnosticCertificate {
                                                kind: DiagnosticKind::NatNonnegTriviality,
                                                operator: op_name.clone(),
                                                summary: format!(
                                                    "Comparison `{op_name}` checks `>= 0` on non-negative Nat interval [{}, {}].",
                                                    iv1.min, iv1.max
                                                ),
                                                hint: "Every Nat satisfies `>= 0` trivially; state a stricter bound (`>= 1`) or use `Int`.".to_string(),
                                            });
                                        }
                                    }
                                    crate::ops::BinOp::Le => {
                                        if matches!(arg1.as_ref(), LeanExpr::LitNat(0)) && iv2.min >= 0 {
                                            certs.push(DiagnosticCertificate {
                                                kind: DiagnosticKind::NatNonnegTriviality,
                                                operator: op_name.clone(),
                                                summary: format!(
                                                    "Comparison `{op_name}` checks `0 <= e` on non-negative Nat interval [{}, {}].",
                                                    iv2.min, iv2.max
                                                ),
                                                hint: "Every Nat satisfies `0 <= e` trivially; state a stricter bound (`1 <= e`) or use `Int`.".to_string(),
                                            });
                                        }
                                    }
                                    _ => {}
                                }
                            }
                            return;
                        }
                    }
                }

                self.collect_diagnostics(f, certs);
                self.collect_diagnostics(a, certs);
            }
            LeanExpr::Let(var, _ty, val, body) => {
                self.collect_diagnostics(val, certs);
                let val_state = self.eval_expr(val);
                let mut local_interp = LeanAbstractInterpreter {
                    environment: self.environment.clone(),
                };
                local_interp.set_decl_state(var, val_state);
                local_interp.collect_diagnostics(body, certs);
            }
            LeanExpr::Lam(_var, _ty, body) => {
                self.collect_diagnostics(body, certs);
            }
            LeanExpr::Const(c) => {
                if c.ends_with(".brecOn")
                    || c.ends_with(".binductionOn")
                    || c.ends_with(".below")
                    || c.ends_with(".ibelow")
                    || c == "WellFounded.fix"
                    || c == "WellFounded.fixF"
                {
                    certs.push(DiagnosticCertificate {
                        kind: DiagnosticKind::KernelBrecOnTax,
                        operator: c.clone(),
                        summary: format!(
                            "Expression references `{c}` in computational cone (SAIR Law 6 brecOn/WellFounded tax)."
                        ),
                        hint: "Replace `.brecOn` / `WellFounded.fix` with structural `@Nat.rec` fuel recursion or a `@[csimp]` theorem.".to_string(),
                    });
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_lambda_beta_reduction() {
        let interp = LeanAbstractInterpreter::new();
        // (fun x : Nat => x + 1) 41
        let lam = LeanExpr::Lam(
            "x".to_string(),
            Box::new(LeanExpr::Const("Nat".to_string())),
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::Const("Nat.add".to_string())),
                    Box::new(LeanExpr::BVar(0)),
                )),
                Box::new(LeanExpr::LitNat(1)),
            )),
        );
        let app = LeanExpr::App(Box::new(lam), Box::new(LeanExpr::LitNat(41)));
        let state = interp.eval_expr(&app);
        assert_eq!(state.sign, AbstractSign::Positive);
        assert_eq!(state.interval, Some(crate::lattice::IntervalBound::new(42, 42)));
    }

    #[test]
    fn test_eval_extended_operators() {
        let interp = LeanAbstractInterpreter::new();

        // 2 ^ 5 = 32
        let pow_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.pow".to_string())),
                Box::new(LeanExpr::LitNat(2)),
            )),
            Box::new(LeanExpr::LitNat(5)),
        );
        let s_pow = interp.eval_expr(&pow_expr);
        assert_eq!(s_pow.interval, Some(crate::lattice::IntervalBound::new(32, 32)));
        assert_eq!(s_pow.sign, AbstractSign::Positive);

        // min 15 40 = 15
        let min_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.min".to_string())),
                Box::new(LeanExpr::LitNat(15)),
            )),
            Box::new(LeanExpr::LitNat(40)),
        );
        let s_min = interp.eval_expr(&min_expr);
        assert_eq!(s_min.interval, Some(crate::lattice::IntervalBound::new(15, 15)));

        // max 15 40 = 40
        let max_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.max".to_string())),
                Box::new(LeanExpr::LitNat(15)),
            )),
            Box::new(LeanExpr::LitNat(40)),
        );
        let s_max = interp.eval_expr(&max_expr);
        assert_eq!(s_max.interval, Some(crate::lattice::IntervalBound::new(40, 40)));

        // 10 != 20 -> True
        let bne_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.bne".to_string())),
                Box::new(LeanExpr::LitNat(10)),
            )),
            Box::new(LeanExpr::LitNat(20)),
        );
        let s_bne = interp.eval_expr(&bne_expr);
        assert_eq!(s_bne.boolean, Some(crate::lattice::AbstractBool::True));

        // 25 >= 10 -> True
        let bge_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.bge".to_string())),
                Box::new(LeanExpr::LitNat(25)),
            )),
            Box::new(LeanExpr::LitNat(10)),
        );
        let s_bge = interp.eval_expr(&bge_expr);
        assert_eq!(s_bge.boolean, Some(crate::lattice::AbstractBool::True));

        // 10 > 25 -> False
        let bgt_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.bgt".to_string())),
                Box::new(LeanExpr::LitNat(10)),
            )),
            Box::new(LeanExpr::LitNat(25)),
        );
        let s_bgt = interp.eval_expr(&bgt_expr);
        assert_eq!(s_bgt.boolean, Some(crate::lattice::AbstractBool::False));

        // true xor true -> False
        let xor_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Bool.xor".to_string())),
                Box::new(LeanExpr::Const("true".to_string())),
            )),
            Box::new(LeanExpr::Const("true".to_string())),
        );
        let s_xor = interp.eval_expr(&xor_expr);
        assert_eq!(s_xor.boolean, Some(crate::lattice::AbstractBool::False));
    }

    #[test]
    fn test_backward_arithmetic_guard_refinement() {
        let mut interp = LeanAbstractInterpreter::new();
        interp.set_decl_state(
            "x",
            AbstractState {
                sign: AbstractSign::Top,
                interval: Some(crate::lattice::IntervalBound::new(0, 100)),
                ..AbstractState::top()
            },
        );

        // Guard 1: (x + 5) < 20  =>  in then-branch x in [0, 14]
        let cond_add = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.blt".to_string())),
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::App(
                        Box::new(LeanExpr::Const("Nat.add".to_string())),
                        Box::new(LeanExpr::Const("x".to_string())),
                    )),
                    Box::new(LeanExpr::LitNat(5)),
                )),
            )),
            Box::new(LeanExpr::LitNat(20)),
        );
        let ite_then_x = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::Const("ite".to_string())),
                    Box::new(cond_add.clone()),
                )),
                Box::new(LeanExpr::Const("x".to_string())),
            )),
            Box::new(LeanExpr::LitNat(10)),
        );
        let res_then = interp.eval_expr(&ite_then_x);
        assert_eq!(
            res_then.interval,
            Some(crate::lattice::IntervalBound::new(0, 14))
        );

        // Guard 2: (x - 3) >= 2  =>  in then-branch x >= 5, so [5, 100]
        let cond_sub = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.bge".to_string())),
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::App(
                        Box::new(LeanExpr::Const("Nat.sub".to_string())),
                        Box::new(LeanExpr::Const("x".to_string())),
                    )),
                    Box::new(LeanExpr::LitNat(3)),
                )),
            )),
            Box::new(LeanExpr::LitNat(2)),
        );
        let ite_sub = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::Const("ite".to_string())),
                    Box::new(cond_sub),
                )),
                Box::new(LeanExpr::Const("x".to_string())),
            )),
            Box::new(LeanExpr::LitNat(50)),
        );
        let res_sub = interp.eval_expr(&ite_sub);
        assert_eq!(
            res_sub.interval,
            Some(crate::lattice::IntervalBound::new(5, 100))
        );
    }

    #[test]
    fn test_threshold_widening_fixpoint_and_ast_harvest() {
        let interp = LeanAbstractInterpreter::new();
        // Guard AST mentioning threshold 100: i < 100
        let guard_ast = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.blt".to_string())),
                Box::new(LeanExpr::Const("i".to_string())),
            )),
            Box::new(LeanExpr::LitNat(100)),
        );
        let thresholds = guard_ast.collect_nat_thresholds();
        assert!(thresholds.contains(&99));
        assert!(thresholds.contains(&100));
        assert!(thresholds.contains(&101));

        // Loop starting at [0, 0], stepping by +1 while <= 99:
        // Standard widening jumps to [0, INF]; threshold widening stops at [0, 100].
        let init = AbstractState::const_nat(0);
        let fp = interp.compute_threshold_widening_fixpoint(
            init,
            |curr| {
                let iv = curr.interval.unwrap();
                let clamped_max = iv.max.min(99);
                let next_iv = crate::lattice::IntervalBound::new(0, clamped_max + 1);
                AbstractState {
                    sign: AbstractSign::Top,
                    interval: Some(next_iv),
                    ..AbstractState::top()
                }.refine_nat()
            },
            &thresholds,
            2,
            16,
        );
        assert_eq!(fp.interval, Some(crate::lattice::IntervalBound::new(0, 100)));
    }

    #[test]
    fn test_diagnose_expr_certificates() {
        let mut interp = LeanAbstractInterpreter::new();
        interp.set_decl_state(
            "n",
            AbstractState {
                sign: AbstractSign::NonNegative,
                interval: Some(crate::lattice::IntervalBound::new(0, 10)),
                ..AbstractState::top()
            },
        );

        // `if n < 5 then n - 10 else n / n`:
        // - True branch refines `n` to `[0, 4]`, so `n - 10` triggers `NatSubTruncation`.
        // - False branch refines `n` to `[5, 10]`, so `n / n` has divisor `[5, 10]` (NO `NatDivModByZero`).
        let cond_lt5 = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.blt".to_string())),
                Box::new(LeanExpr::Const("n".to_string())),
            )),
            Box::new(LeanExpr::LitNat(5)),
        );
        let sub_10 = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.sub".to_string())),
                Box::new(LeanExpr::Const("n".to_string())),
            )),
            Box::new(LeanExpr::LitNat(10)),
        );
        let div_n = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.div".to_string())),
                Box::new(LeanExpr::Const("n".to_string())),
            )),
            Box::new(LeanExpr::Const("n".to_string())),
        );
        let ite_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::Const("ite".to_string())),
                    Box::new(cond_lt5),
                )),
                Box::new(sub_10),
            )),
            Box::new(div_n),
        );
        let (_state, certs) = interp.diagnose_expr(&ite_expr);
        assert_eq!(certs.len(), 1);
        assert_eq!(certs[0].kind, DiagnosticKind::NatSubTruncation);
        assert!(certs[0].summary.contains("[0, 4] - [10, 10]"));
    }

    #[test]
    fn test_eval_expr_trace_partitioned() {
        let mut interp = LeanAbstractInterpreter::new();
        interp.set_decl_state(
            "x",
            AbstractState {
                sign: AbstractSign::NonNegative,
                interval: Some(crate::lattice::IntervalBound::new(0, 100)),
                ..AbstractState::top()
            },
        );

        // let y = (if x < 50 then 10 else 90) in y + 5
        // Standard `eval_expr` joins y to [10, 90] and produces [15, 95].
        // Trace-partitioned `eval_expr_trace_partitioned` keeps two disjoint partitions:
        //   trace [1] -> [15, 15], trace [0] -> [95, 95].
        let cond_lt50 = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.blt".to_string())),
                Box::new(LeanExpr::Const("x".to_string())),
            )),
            Box::new(LeanExpr::LitNat(50)),
        );
        let ite_y = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::Const("ite".to_string())),
                    Box::new(cond_lt50),
                )),
                Box::new(LeanExpr::LitNat(10)),
            )),
            Box::new(LeanExpr::LitNat(90)),
        );
        let body = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.add".to_string())),
                Box::new(LeanExpr::Const("y".to_string())),
            )),
            Box::new(LeanExpr::LitNat(5)),
        );
        let let_expr = LeanExpr::Let(
            "y".to_string(),
            Box::new(LeanExpr::Const("Nat".to_string())),
            Box::new(ite_y),
            Box::new(body),
        );

        let tp = interp.eval_expr_trace_partitioned(&let_expr, 2);
        assert_eq!(tp.partitions.len(), 2);
        let tok_true = crate::wto::TraceToken::root().push_branch(1, 2);
        let tok_false = crate::wto::TraceToken::root().push_branch(0, 2);
        assert_eq!(
            tp.partitions.get(&tok_true).unwrap().interval,
            Some(crate::lattice::IntervalBound::new(15, 15))
        );
        assert_eq!(
            tp.partitions.get(&tok_false).unwrap().interval,
            Some(crate::lattice::IntervalBound::new(95, 95))
        );
        assert_eq!(
            tp.collapse().interval,
            Some(crate::lattice::IntervalBound::new(15, 95))
        );
    }

    #[test]
    fn test_specification_lint_detectors() {
        let interp = LeanAbstractInterpreter::new();
        let src = "\
def checkFlag (n : Nat) : Bool := n > 5
theorem checkFlag_sound (n : Nat) (h : checkFlag n = true) : n > 5 := by decide
theorem echo_thm (x : Nat) (h : x > 0) : x > 0 := by exact h
theorem refl_thm (a b : Nat) : a + b = a + b := by rfl
theorem nonneg_thm (a b : Nat) : a - b >= 0 := by omega
theorem unused_binder_thm (a : Nat) (_h : a > 0) (dead : Nat) : a = a := by rfl
";
        let certs = interp.diagnose_source_text(src);
        let kinds: Vec<DiagnosticKind> = certs.iter().map(|c| c.kind).collect();
        assert!(kinds.contains(&DiagnosticKind::HypothesisEcho), "Missing HypothesisEcho: {:?}", certs);
        assert!(kinds.contains(&DiagnosticKind::ReflexiveTautology), "Missing ReflexiveTautology: {:?}", certs);
        assert!(kinds.contains(&DiagnosticKind::NatNonnegTriviality), "Missing NatNonnegTriviality: {:?}", certs);
        assert!(kinds.contains(&DiagnosticKind::NatSubTruncation), "Missing NatSubTruncation: {:?}", certs);
        assert!(kinds.contains(&DiagnosticKind::UnusedUnderscoreBinder), "Missing UnusedUnderscoreBinder: {:?}", certs);
        assert!(kinds.contains(&DiagnosticKind::OneWayBoolChecker), "Missing OneWayBoolChecker: {:?}", certs);

        // Verify clean source produces 0 lint findings (including additive guard b + 1 <= a)
        let clean_src = "\
def checkFlag (n : Nat) : Bool := n > 5
theorem checkFlag_iff (n : Nat) : checkFlag n = true <-> n > 5 := by decide
theorem sub_cancel (a b : Nat) (h : b <= a) : a - b + b = a := by omega
theorem sub_add_guard (a b : Nat) (h : b + 1 <= a) : a - b >= 1 := by omega
";
        let clean_certs = interp.diagnose_source_text(clean_src);
        assert!(clean_certs.is_empty(), "Expected 0 findings on clean source, got: {:?}", clean_certs);

        // Verify hypothesis-embedded Nat subtraction and implicit underscore binder detection
        let edge_src = "\
theorem sub_in_hyp (a b : Nat) (h : a - b = 3) : a >= 3 := by omega
theorem imp_under {a : Nat} {_h : a > 0} (b : Nat) : b + 0 = b := by omega
";
        let edge_certs = interp.diagnose_source_text(edge_src);
        let edge_kinds: Vec<DiagnosticKind> = edge_certs.iter().map(|c| c.kind).collect();
        assert!(edge_kinds.contains(&DiagnosticKind::NatSubTruncation), "Expected NatSubTruncation on sub_in_hyp: {:?}", edge_certs);
        assert!(edge_kinds.contains(&DiagnosticKind::UnusedUnderscoreBinder), "Expected UnusedUnderscoreBinder on imp_under: {:?}", edge_certs);

        // Verify function-application tokens across `-` and equality/additive/strict-lt guards produce 0 false positives
        let fp_clean_src = "\
theorem fn_app_sub (numStages n : Nat) (h_stages : numStages >= 2) (h_n : n > 0) : unfusedGlobalMemOps numStages n - fusedGlobalMemOps n = 2 * (numStages - 1) * n := by omega
theorem int_cast_sub (pp pn : Nat) : ternaryDot pp pn = (Int.ofNat pp - Int.ofNat pn) := by rfl
theorem eq_guard_sub (s1 s2 : Nat) (h_eq : s1 = s2) : s1 - s2 = 0 := by omega
theorem add_sum_guard (visited culled total : Nat) (h_part : visited + culled = total) : total - culled = visited := by omega
theorem strict_lt_guard (i h_read : Nat) (hi : i < h_read) : i <= h_read - 1 := by omega
";
        let fp_certs = interp.diagnose_source_text(fp_clean_src);
        assert!(fp_certs.is_empty(), "Expected 0 NatSubTruncation false positives on fp_clean_src, got: {:?}", fp_certs);
    }

    #[test]
    fn test_sair_kernel_law_auditor_diagnostics() {
        let interp = LeanAbstractInterpreter::new();

        // 1. Source-level SAIR Law 6 (KernelBrecOnTax), Law 14 (KernelPowerOfTwoDivMod), and OverConcreteFixedArity
        let sair_src = "def badBrec (n : Nat) : Nat := Nat.brecOn n (fun k _ => k)
def badWf (n : Nat) : Nat := WellFounded.fix Nat.lt_wfRel.wf (fun k _ => k) n
def badDivMod (x : Nat) : Nat := (x / 64) + (x % 4096)
theorem fixed_arity_4 (a0 a1 a2 a3 : Nat) : a0 + a1 + a2 + a3 >= 0 := by omega
theorem fixed_arity_q (q1_n1 q1_n2 q1_n3 : Nat) : q1_n1 + q1_n2 + q1_n3 = q1_n1 + (q1_n2 + q1_n3) := by omega
";
        let certs = interp.diagnose_source_text(sair_src);
        let brec_certs: Vec<&DiagnosticCertificate> = certs
            .iter()
            .filter(|c| c.kind == DiagnosticKind::KernelBrecOnTax)
            .collect();
        assert_eq!(brec_certs.len(), 2, "Expected 2 KernelBrecOnTax certs: {:?}", certs);

        let pow2_certs: Vec<&DiagnosticCertificate> = certs
            .iter()
            .filter(|c| c.kind == DiagnosticKind::KernelPowerOfTwoDivMod)
            .collect();
        assert_eq!(pow2_certs.len(), 1, "Expected KernelPowerOfTwoDivMod on badDivMod: {:?}", certs);
        assert_eq!(pow2_certs[0].operator, "badDivMod");

        let arity_certs: Vec<&DiagnosticCertificate> = certs
            .iter()
            .filter(|c| c.kind == DiagnosticKind::OverConcreteFixedArity)
            .collect();
        assert_eq!(arity_certs.len(), 2, "Expected 2 OverConcreteFixedArity certs: {:?}", certs);

        // 2. Clean SAIR source (structural Nat.rec, bitwise shifts/masks, noncomputable, @[csimp], parameterized List)
        let clean_sair_src = "def goodRec (n : Nat) : Nat := @Nat.rec (fun _ => Nat) 0 (fun k acc => acc + (k >>> 6) + (k &&& 4095)) n
noncomputable def allowedNoncomp (n : Nat) : Nat := WellFounded.fix Nat.lt_wfRel.wf (fun k _ => k / 64) n
@[csimp] def csimpReplaced (n : Nat) : Nat := Nat.brecOn n (fun k _ => k)
theorem two_params_ok (x1 x2 : Nat) : x1 + x2 = x2 + x1 := by omega
";
        let clean_certs = interp.diagnose_source_text(clean_sair_src);
        assert!(
            clean_certs.is_empty(),
            "Expected 0 diagnostics on clean SAIR source, got: {:?}",
            clean_certs
        );

        // 3. Expression-level diagnose_expr checks for KernelBrecOnTax and KernelPowerOfTwoDivMod
        let div64_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.div".to_string())),
                Box::new(LeanExpr::Const("x".to_string())),
            )),
            Box::new(LeanExpr::LitNat(64)),
        );
        let (_st, expr_certs) = interp.diagnose_expr(&div64_expr);
        assert!(
            expr_certs
                .iter()
                .any(|c| c.kind == DiagnosticKind::KernelPowerOfTwoDivMod),
            "Expected KernelPowerOfTwoDivMod from diagnose_expr: {:?}",
            expr_certs
        );

        let brec_expr = LeanExpr::App(
            Box::new(LeanExpr::Const("Nat.brecOn".to_string())),
            Box::new(LeanExpr::LitNat(10)),
        );
        let (_st2, brec_expr_certs) = interp.diagnose_expr(&brec_expr);
        assert!(
            brec_expr_certs
                .iter()
                .any(|c| c.kind == DiagnosticKind::KernelBrecOnTax),
            "Expected KernelBrecOnTax from diagnose_expr: {:?}",
            brec_expr_certs
        );

        // 4. Edge cases: mutual ... end blocks, pattern-matching defs without `:=`, `2^k` syntax, and `abbrev` power-of-2 aliases
        let edge_src = "abbrev radixMod : Nat := 64
mutual
  def mutualStepA (n : Nat) : Nat :=
    Nat.brecOn n (fun k _ => k)
  def mutualStepB : Nat -> Nat
    | 0 => 0
    | k + 1 => (k / radixMod) + (k % (2 ^ 12))
end
";
        let edge_certs = interp.diagnose_source_text(edge_src);
        assert!(
            edge_certs
                .iter()
                .any(|c| c.kind == DiagnosticKind::KernelBrecOnTax && c.operator == "mutualStepA"),
            "Expected KernelBrecOnTax on indented mutualStepA: {:?}",
            edge_certs
        );
        assert!(
            edge_certs
                .iter()
                .any(|c| c.kind == DiagnosticKind::KernelPowerOfTwoDivMod && c.operator == "mutualStepB"),
            "Expected KernelPowerOfTwoDivMod on pattern-matched mutualStepB with abbrev alias: {:?}",
            edge_certs
        );
    }
}
