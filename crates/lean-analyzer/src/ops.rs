//! src/ops.rs
//! Unary and binary operator tables: maps Lean (and analyzer-alias) names to transfer functions.
//! 

use crate::lattice::{AbstractBool, AbstractSign, AbstractState, IntervalBound};
use crate::nat_interval::INF;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    BoolNot,
    NatSucc,
    NatPred,
}

impl UnaryOp {
    pub fn from_name(n: &str) -> Option<Self> {
        Some(match n {
            "Bool.not" | "not" => Self::BoolNot,
            "Nat.succ" => Self::NatSucc,
            "Nat.pred" => Self::NatPred,
            _ => return None,
        })
    }

    pub fn apply(self, s: &AbstractState) -> AbstractState {
        let s = s.refine_nat();
        match self {
            Self::BoolNot => AbstractState {
                sign: AbstractSign::Top,
                interval: None,
                boolean: Some(s.boolean.unwrap_or(AbstractBool::Top).not()),
                is_deterministic: s.is_deterministic,
                is_pure: s.is_pure,
            },
            Self::NatSucc => {
                let iv = s.interval.map(|i| i.nat_succ());
                AbstractState {
                    sign: AbstractSign::Positive,
                    interval: iv,
                    boolean: None,
                    is_deterministic: s.is_deterministic,
                    is_pure: s.is_pure,
                }
            }
            Self::NatPred => {
                let iv = s.interval.map(|i| i.nat_pred());
                let sign = match iv {
                    Some(v) if v.min > 0 => AbstractSign::Positive,
                    Some(v) if v.max == 0 => AbstractSign::Zero,
                    _ if s.sign == AbstractSign::Zero => AbstractSign::Zero,
                    _ => AbstractSign::NonNegative,
                };
                AbstractState {
                    sign,
                    interval: iv,
                    boolean: None,
                    is_deterministic: s.is_deterministic,
                    is_pure: s.is_pure,
                }
                .refine_nat()
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Min,
    Max,
    Pow,
    Land,
    Lor,
    Lxor,
    Shl,
    Shr,
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
    Ne,
    /// `&&`/`and`: Bool only.
    BAnd,
    BOr,
    BXor,
    /// `HAnd.hAnd` etc: Nat bitwise or Bool depending on argument kind.
    PolyAnd,
    PolyOr,
    PolyXor,
}

impl BinOp {
    /// Names starting with `Nat.bge`, `Nat.bgt`, `Nat.bne`, `BNe.bne` are analyzer
    /// aliases (no such Lean constants); the rest are real Lean names.
    pub fn from_name(n: &str) -> Option<Self> {
        Some(match n {
            "Nat.add" | "HAdd.hAdd" => Self::Add,
            "Nat.sub" | "HSub.hSub" => Self::Sub,
            "Nat.mul" | "HMul.hMul" => Self::Mul,
            "Nat.div" | "HDiv.hDiv" => Self::Div,
            "Nat.mod" | "HMod.hMod" => Self::Mod,
            "Nat.min" | "min" => Self::Min,
            "Nat.max" | "max" => Self::Max,
            "Nat.pow" | "HPow.hPow" => Self::Pow,
            "Nat.land" | "Nat.landOp" | "AndOp.and" => Self::Land,
            "Nat.lor" | "OrOp.or" => Self::Lor,
            "Nat.xor" | "XorOp.xor" => Self::Lxor,
            "Nat.shiftLeft" | "HShiftLeft.hShiftLeft" | "ShiftLeft.shiftLeft" => Self::Shl,
            "Nat.shiftRight" | "HShiftRight.hShiftRight" | "ShiftRight.shiftRight" => Self::Shr,
            "Nat.ble" | "LE.le" => Self::Le,
            "Nat.blt" | "LT.lt" => Self::Lt,
            "Nat.bge" | "GE.ge" => Self::Ge,
            "Nat.bgt" | "GT.gt" => Self::Gt,
            "Nat.beq" | "Eq" | "BEq.beq" => Self::Eq,
            "Nat.bne" | "Ne" | "BNe.bne" | "bne" => Self::Ne,
            "Bool.and" | "and" => Self::BAnd,
            "Bool.or" | "or" => Self::BOr,
            "Bool.xor" | "xor" => Self::BXor,
            "HAnd.hAnd" => Self::PolyAnd,
            "HOr.hOr" => Self::PolyOr,
            "HXor.hXor" => Self::PolyXor,
            _ => return None,
        })
    }

    fn is_nat_valued(self) -> bool {
        !matches!(
            self,
            Self::Le | Self::Lt | Self::Ge | Self::Gt | Self::Eq | Self::Ne
                | Self::BAnd | Self::BOr | Self::BXor
        )
    }

    /// Exact Lean result on concrete naturals, saturated to INF (= i64::MAX).
    fn concrete(self, a: u128, b: u128) -> i64 {
        let clamp = |v: Option<u128>| match v {
            Some(v) if v < INF as u128 => v as i64,
            _ => INF,
        };
        match self {
            Self::Add => clamp(a.checked_add(b)),
            Self::Sub => clamp(Some(a.saturating_sub(b))),
            Self::Mul => clamp(a.checked_mul(b)),
            Self::Div => clamp(Some(if b == 0 { 0 } else { a / b })),
            Self::Mod => clamp(Some(if b == 0 { a } else { a % b })),
            Self::Min => clamp(Some(a.min(b))),
            Self::Max => clamp(Some(a.max(b))),
            Self::Pow => {
                if b == 0 {
                    1
                } else if a <= 1 {
                    a as i64
                } else if b > u32::MAX as u128 {
                    INF
                } else {
                    clamp(a.checked_pow(b as u32))
                }
            }
            Self::Land | Self::PolyAnd => clamp(Some(a & b)),
            Self::Lor | Self::PolyOr => clamp(Some(a | b)),
            Self::Lxor | Self::PolyXor => clamp(Some(a ^ b)),
            Self::Shl => {
                if a == 0 {
                    0
                } else if b >= 128 || (a.leading_zeros() as u128) < b {
                    INF
                } else {
                    clamp(Some(a << b))
                }
            }
            Self::Shr => clamp(Some(if b >= 128 { 0 } else { a >> b })),
            _ => INF,
        }
    }

    pub fn apply(self, s1: &AbstractState, s2: &AbstractState) -> AbstractState {
        let s1 = s1.refine_nat();
        let s2 = s2.refine_nat();
        let det = s1.is_deterministic && s2.is_deterministic;
        let pure = s1.is_pure && s2.is_pure;
        let mk_bool = |b: AbstractBool| AbstractState {
            sign: AbstractSign::Top,
            interval: None,
            boolean: Some(b),
            is_deterministic: det,
            is_pure: pure,
        };
        let mk_nat = |iv: Option<IntervalBound>, sign: AbstractSign| {
            AbstractState {
                sign,
                interval: iv,
                boolean: None,
                is_deterministic: det,
                is_pure: pure,
            }
            .refine_nat()
        };
        let both = match (s1.interval, s2.interval) {
            (Some(a), Some(b)) => Some((a, b)),
            _ => None,
        };
        let sign_of = |iv: &Option<IntervalBound>| match iv {
            Some(v) if v.min > 0 => AbstractSign::Positive,
            Some(v) if v.max == 0 => AbstractSign::Zero,
            _ => AbstractSign::NonNegative,
        };
        let nat = |f: fn(&IntervalBound, &IntervalBound) -> IntervalBound| {
            let iv = both.map(|(a, b)| f(&a, &b));
            mk_nat(iv, sign_of(&iv))
        };
        let rel = |f: fn(&IntervalBound, &IntervalBound) -> AbstractBool| {
            mk_bool(both.map(|(a, b)| f(&a, &b)).unwrap_or(AbstractBool::Top))
        };
        let bb = |f: fn(AbstractBool, AbstractBool) -> AbstractBool| {
            let b1 = s1.boolean.unwrap_or(AbstractBool::Top);
            let b2 = s2.boolean.unwrap_or(AbstractBool::Top);
            mk_bool(f(b1, b2))
        };
        // Polymorphic dispatch: Nat bitwise if both have intervals, Bool if both
        // have booleans and no interval, otherwise unknown.
        let poly = |nf: fn(&IntervalBound, &IntervalBound) -> IntervalBound,
                    bf: fn(AbstractBool, AbstractBool) -> AbstractBool| {
            if both.is_some() {
                nat(nf)
            } else if s1.interval.is_none()
                && s2.interval.is_none()
                && s1.boolean.is_some()
                && s2.boolean.is_some()
            {
                bb(bf)
            } else {
                let mut t = AbstractState::top();
                t.is_deterministic = det;
                t.is_pure = pure;
                t
            }
        };
        // Exact evaluation on finite point inputs (Lean semantics, u128 arithmetic).
        if let (Some((a, b)), true) = (both, self.is_nat_valued()) {
            if a.min == a.max && b.min == b.max && a.max != INF && b.max != INF {
                let r = self.concrete(a.min as u128, b.min as u128);
                let iv = Some(IntervalBound::point(r));
                return mk_nat(iv, sign_of(&iv));
            }
        }
        match self {
            Self::Add => {
                let iv = both.map(|(a, b)| a.add(&b));
                let sign = match (s1.sign, s2.sign) {
                    (AbstractSign::Zero, AbstractSign::Zero) => AbstractSign::Zero,
                    (AbstractSign::Positive, _) | (_, AbstractSign::Positive) => {
                        AbstractSign::Positive
                    }
                    _ => AbstractSign::NonNegative,
                };
                mk_nat(iv, sign)
            }
            Self::Mul => {
                let iv = both.map(|(a, b)| a.mul(&b));
                let sign = match (s1.sign, s2.sign) {
                    (AbstractSign::Zero, _) | (_, AbstractSign::Zero) => AbstractSign::Zero,
                    (AbstractSign::Positive, AbstractSign::Positive) => AbstractSign::Positive,
                    _ => AbstractSign::NonNegative,
                };
                mk_nat(iv, sign)
            }
            Self::Sub => nat(IntervalBound::nat_sub),
            Self::Div => nat(IntervalBound::nat_div),
            Self::Mod => nat(IntervalBound::nat_mod),
            Self::Min => nat(IntervalBound::nat_min),
            Self::Max => nat(IntervalBound::nat_max),
            Self::Pow => nat(IntervalBound::nat_pow),
            Self::Land => nat(IntervalBound::nat_land),
            Self::Lor => nat(IntervalBound::nat_lor),
            Self::Lxor => nat(IntervalBound::nat_xor),
            Self::Shl => nat(IntervalBound::nat_shl),
            Self::Shr => nat(IntervalBound::nat_shr),
            Self::Le => rel(IntervalBound::ble),
            Self::Lt => rel(IntervalBound::blt),
            Self::Ge => rel(IntervalBound::bge),
            Self::Gt => rel(IntervalBound::bgt),
            Self::Eq => {
                if both.is_some() {
                    rel(IntervalBound::beq)
                } else if s1.interval.is_none()
                    && s2.interval.is_none()
                    && s1.boolean.is_some()
                    && s2.boolean.is_some()
                {
                    bb(|b1, b2| b1.xor(b2).not())
                } else {
                    mk_bool(AbstractBool::Top)
                }
            }
            Self::Ne => {
                if both.is_some() {
                    rel(IntervalBound::bne)
                } else if s1.interval.is_none()
                    && s2.interval.is_none()
                    && s1.boolean.is_some()
                    && s2.boolean.is_some()
                {
                    bb(AbstractBool::xor)
                } else {
                    mk_bool(AbstractBool::Top)
                }
            }
            Self::BAnd => bb(AbstractBool::and),
            Self::BOr => bb(AbstractBool::or),
            Self::BXor => bb(AbstractBool::xor),
            Self::PolyAnd => poly(IntervalBound::nat_land, AbstractBool::and),
            Self::PolyOr => poly(IntervalBound::nat_lor, AbstractBool::or),
            Self::PolyXor => poly(IntervalBound::nat_xor, AbstractBool::xor),
        }
    }
}
