//! src/lattice.rs
//! High-speed bitset abstract lattice operations for Lean 4 terms.
//! 

/// Bitset encoding of abstract numeric signs:
/// - Bit 0: Zero
/// - Bit 1: Positive
/// - Bit 2: Negative
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum AbstractSign {
    Bottom = 0,
    Zero = 1,
    Positive = 2,
    NonNegative = 3, // Zero | Positive
    Negative = 4,
    NonPositive = 5, // Zero | Negative
    NonZero = 6,     // Positive | Negative
    Top = 7,         // Zero | Positive | Negative
}

impl AbstractSign {
    #[inline(always)]
    pub fn from_u8(val: u8) -> Self {
        match val & 7 {
            0 => AbstractSign::Bottom,
            1 => AbstractSign::Zero,
            2 => AbstractSign::Positive,
            3 => AbstractSign::NonNegative,
            4 => AbstractSign::Negative,
            5 => AbstractSign::NonPositive,
            6 => AbstractSign::NonZero,
            _ => AbstractSign::Top,
        }
    }

    #[inline(always)]
    pub fn as_u8(self) -> u8 {
        self as u8
    }

    /// Lattice Join (Least Upper Bound): Bitwise OR in CPU register.
    #[inline(always)]
    pub fn join(self, other: Self) -> Self {
        Self::from_u8(self.as_u8() | other.as_u8())
    }

    /// Lattice Meet (Greatest Lower Bound): Bitwise AND in CPU register.
    #[inline(always)]
    pub fn meet(self, other: Self) -> Self {
        Self::from_u8(self.as_u8() & other.as_u8())
    }

    /// Checks if self is lower or equal to other in the lattice order (a <= b iff a | b == b).
    #[inline(always)]
    pub fn is_le(self, other: Self) -> bool {
        (self.as_u8() | other.as_u8()) == other.as_u8()
    }
}

/// Bounded integer interval [min, max].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntervalBound {
    pub min: i64,
    pub max: i64,
}

impl IntervalBound {
    #[inline]
    pub fn new(min: i64, max: i64) -> Self {
        Self { min, max }
    }

    #[inline]
    pub fn point(val: i64) -> Self {
        Self { min: val, max: val }
    }

    #[inline]
    pub fn join(&self, other: &Self) -> Self {
        Self {
            min: self.min.min(other.min),
            max: self.max.max(other.max),
        }
    }

    /// Checks if `self` is a sub-interval of `other` (`self <= other` in the interval lattice).
    #[inline]
    pub fn is_le(&self, other: &Self) -> bool {
        if self.min > self.max {
            return true;
        }
        if other.min > other.max {
            return false;
        }
        self.min >= other.min && self.max <= other.max
    }

    #[inline]
    pub fn add(&self, other: &Self) -> Self {
        Self {
            min: self.min.saturating_add(other.min),
            max: self.max.saturating_add(other.max),
        }
    }

    #[inline]
    pub fn sub(&self, other: &Self) -> Self {
        Self {
            min: self.min.saturating_sub(other.max),
            max: self.max.saturating_sub(other.min),
        }
    }

    #[inline]
    pub fn mul(&self, other: &Self) -> Self {
        let p1 = self.min.saturating_mul(other.min);
        let p2 = self.min.saturating_mul(other.max);
        let p3 = self.max.saturating_mul(other.min);
        let p4 = self.max.saturating_mul(other.max);
        Self {
            min: p1.min(p2).min(p3).min(p4),
            max: p1.max(p2).max(p3).max(p4),
        }
    }


    /// Abstract interpretation widening operator (Cousot-Cousot).
    /// Jumps unstable bounds to infinity (i64::MIN / i64::MAX) to guarantee loop fixpoint convergence.
    #[inline]
    pub fn widen(&self, other: &Self) -> Self {
        let min = if other.min < self.min { i64::MIN } else { self.min };
        let max = if other.max > self.max { i64::MAX } else { self.max };
        Self { min, max }
    }

    /// Non-negative integer widening operator with zero floor.
    #[inline]
    pub fn nat_widen(&self, other: &Self) -> Self {
        let min = if other.min < self.min { 0 } else { self.min.max(0) };
        let max = if other.max > self.max { i64::MAX } else { self.max };
        Self { min, max }
    }

    /// Threshold widening over integer intervals (`MOLLER-SPA s5.12 p1`, `RIVAL-YI s6.1 p1`):
    /// Steps an expanding upper bound to the smallest threshold `>= other.max` (or `i64::MAX`),
    /// and a shrinking lower bound to the largest threshold `<= other.min` (or `0` for non-negative bounds).
    #[inline]
    pub fn widen_with_thresholds(&self, other: &Self, thresholds: &[i64]) -> Self {
        let min = if other.min < self.min {
            thresholds
                .iter()
                .copied()
                .rev()
                .find(|&t| t <= other.min)
                .unwrap_or(if self.min >= 0 && other.min >= 0 {
                    0
                } else {
                    i64::MIN
                })
        } else {
            self.min
        };
        let max = if other.max > self.max {
            thresholds
                .iter()
                .copied()
                .find(|&t| t >= other.max)
                .unwrap_or(i64::MAX)
        } else {
            self.max
        };
        Self { min, max }
    }

    /// Abstract interpretation narrowing operator (Cousot-Cousot).
    /// Refines infinite bounds after reaching a post-fixpoint.
    #[inline]
    pub fn narrow(&self, other: &Self) -> Self {
        let min = if self.min == i64::MIN {
            other.min
        } else {
            self.min
        };
        let max = if self.max == i64::MAX {
            other.max
        } else {
            self.max
        };
        Self { min, max }
    }

    // Natural-number comparison, min/max, pow and bitwise transfer functions live in
    // nat_interval.rs (explicit i64::MAX = +infinity convention, validated against Lean).

}


/// Bounded double-precision floating-point interval [min, max] (for continuous probabilities, Lyapunov energy, etc.)
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct FloatIntervalBound {
    pub min: f64,
    pub max: f64,
}

impl FloatIntervalBound {
    #[inline]
    pub fn new(min: f64, max: f64) -> Self {
        Self { min, max }
    }

    #[inline]
    pub fn point(val: f64) -> Self {
        Self { min: val, max: val }
    }

    #[inline]
    pub fn unit_interval() -> Self {
        Self { min: 0.0, max: 1.0 }
    }

    #[inline]
    pub fn join(&self, other: &Self) -> Self {
        Self {
            min: self.min.min(other.min),
            max: self.max.max(other.max),
        }
    }

    #[inline]
    pub fn meet(&self, other: &Self) -> Self {
        Self {
            min: self.min.max(other.min),
            max: self.max.min(other.max),
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.min > self.max
    }

    /// Abstract interpretation widening: jump to infinity if bound expands.
    #[inline]
    pub fn widen(&self, other: &Self) -> Self {
        let min = if other.min < self.min { f64::NEG_INFINITY } else { self.min };
        let max = if other.max > self.max { f64::INFINITY } else { self.max };
        Self { min, max }
    }

    /// Widening with designated policy thresholds (e.g. [0.0, 0.15, 0.5, 1.0]).
    #[inline]
    pub fn widen_with_thresholds(&self, other: &Self, thresholds: &[f64]) -> Self {
        let min = if other.min < self.min {
            thresholds.iter().copied().rev().find(|&t| t <= other.min).unwrap_or(f64::NEG_INFINITY)
        } else {
            self.min
        };
        let max = if other.max > self.max {
            thresholds.iter().copied().find(|&t| t >= other.max).unwrap_or(f64::INFINITY)
        } else {
            self.max
        };
        Self { min, max }
    }

    /// Abstract interpretation narrowing: refine infinite bounds with post-fixpoint bound.
    #[inline]
    pub fn narrow(&self, other: &Self) -> Self {
        let min = if self.min == f64::NEG_INFINITY {
            other.min
        } else {
            self.min
        };
        let max = if self.max == f64::INFINITY {
            other.max
        } else {
            self.max
        };
        Self { min, max }
    }
}

/// Abstract boolean lattice:
/// - Bottom = 0 (unreachable)
/// - False = 1
/// - True = 2
/// - Top = 3 (unknown / either)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum AbstractBool {
    Bottom = 0,
    False = 1,
    True = 2,
    Top = 3,
}

impl AbstractBool {
    #[inline(always)]
    pub fn from_u8(val: u8) -> Self {
        match val & 3 {
            0 => AbstractBool::Bottom,
            1 => AbstractBool::False,
            2 => AbstractBool::True,
            _ => AbstractBool::Top,
        }
    }

    #[inline(always)]
    pub fn as_u8(self) -> u8 {
        self as u8
    }

    #[inline(always)]
    pub fn join(self, other: Self) -> Self {
        Self::from_u8(self.as_u8() | other.as_u8())
    }

    #[inline(always)]
    pub fn meet(self, other: Self) -> Self {
        Self::from_u8(self.as_u8() & other.as_u8())
    }

    #[inline(always)]
    pub fn is_le(self, other: Self) -> bool {
        (self.as_u8() | other.as_u8()) == other.as_u8()
    }

    #[inline(always)]
    pub fn not(self) -> Self {
        match self {
            AbstractBool::Bottom => AbstractBool::Bottom,
            AbstractBool::False => AbstractBool::True,
            AbstractBool::True => AbstractBool::False,
            AbstractBool::Top => AbstractBool::Top,
        }
    }

    #[inline(always)]
    pub fn and(self, other: Self) -> Self {
        match (self, other) {
            (AbstractBool::False, _) | (_, AbstractBool::False) => AbstractBool::False,
            (AbstractBool::True, AbstractBool::True) => AbstractBool::True,
            (AbstractBool::Bottom, _) | (_, AbstractBool::Bottom) => AbstractBool::Bottom,
            _ => AbstractBool::Top,
        }
    }

    #[inline(always)]
    pub fn or(self, other: Self) -> Self {
        match (self, other) {
            (AbstractBool::True, _) | (_, AbstractBool::True) => AbstractBool::True,
            (AbstractBool::False, AbstractBool::False) => AbstractBool::False,
            (AbstractBool::Bottom, _) | (_, AbstractBool::Bottom) => AbstractBool::Bottom,
            _ => AbstractBool::Top,
        }
    }

    #[inline(always)]
    pub fn xor(self, other: Self) -> Self {
        match (self, other) {
            (AbstractBool::Bottom, _) | (_, AbstractBool::Bottom) => AbstractBool::Bottom,
            (AbstractBool::True, AbstractBool::True) | (AbstractBool::False, AbstractBool::False) => {
                AbstractBool::False
            }
            (AbstractBool::True, AbstractBool::False) | (AbstractBool::False, AbstractBool::True) => {
                AbstractBool::True
            }
            _ => AbstractBool::Top,
        }
    }
}

/// Abstract state of a Lean declaration or variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AbstractState {
    pub sign: AbstractSign,
    pub interval: Option<IntervalBound>,
    pub boolean: Option<AbstractBool>,
    pub is_deterministic: bool,
    pub is_pure: bool,
}

impl AbstractState {
    pub fn const_nat(val: u64) -> Self {
        let sign = if val > 0 {
            AbstractSign::Positive
        } else {
            AbstractSign::Zero
        };
        // i64::MAX is the +infinity marker; values >= i64::MAX saturate to it.
        let s_val = if val >= i64::MAX as u64 { i64::MAX } else { val as i64 };
        Self {
            sign,
            interval: Some(IntervalBound::point(s_val)),
            boolean: None,
            is_deterministic: true,
            is_pure: true,
        }
    }

    pub fn const_bool(val: bool) -> Self {
        Self {
            sign: AbstractSign::Top,
            interval: None,
            boolean: Some(if val {
                AbstractBool::True
            } else {
                AbstractBool::False
            }),
            is_deterministic: true,
            is_pure: true,
        }
    }

    pub fn from_abstract_bool(b: AbstractBool) -> Self {
        Self {
            sign: AbstractSign::Top,
            interval: None,
            boolean: Some(b),
            is_deterministic: true,
            is_pure: true,
        }
    }

    pub fn top() -> Self {
        Self {
            sign: AbstractSign::Top,
            interval: None,
            boolean: Some(AbstractBool::Top),
            is_deterministic: false,
            is_pure: false,
        }
    }

    pub fn bottom() -> Self {
        Self {
            sign: AbstractSign::Bottom,
            interval: None,
            boolean: Some(AbstractBool::Bottom),
            is_deterministic: true,
            is_pure: true,
        }
    }

    #[inline(always)]
    pub fn is_bottom(&self) -> bool {
        if self.sign == AbstractSign::Bottom {
            return true;
        }
        if let Some(iv) = self.interval {
            if iv.min > iv.max {
                return true;
            }
        }
        false
    }

    /// Mutually refines `sign` and `interval` for a natural-number abstract state.
    pub fn refine_nat(mut self) -> Self {
        if self.sign == AbstractSign::Bottom {
            self.interval = None;
            return self;
        }
        if self.sign == AbstractSign::Zero {
            self.interval = Some(match self.interval {
                Some(iv) if iv.min <= 0 && 0 <= iv.max => IntervalBound::point(0),
                None => IntervalBound::point(0),
                Some(iv) => iv,
            });
        } else if self.sign == AbstractSign::Positive {
            if let Some(ref mut iv) = self.interval {
                if iv.min == 0 && iv.max >= 1 {
                    iv.min = 1;
                }
            }
        }
        if let Some(iv) = self.interval {
            if iv.min > iv.max {
                self.sign = AbstractSign::Bottom;
                self.interval = None;
            } else if iv.min == 0 && iv.max == 0 {
                self.sign = AbstractSign::Zero;
            } else if iv.min > 0 {
                self.sign = AbstractSign::Positive;
            } else if iv.min == 0 {
                self.sign = AbstractSign::NonNegative;
            }
        }
        self
    }

    pub fn join(&self, other: &Self) -> Self {
        if self.is_bottom() {
            return *other;
        }
        if other.is_bottom() {
            return *self;
        }
        let sign = self.sign.join(other.sign);
        let interval = match (&self.interval, &other.interval) {
            (Some(i1), Some(i2)) => Some(i1.join(i2)),
            _ => None,
        };
        let boolean = match (&self.boolean, &other.boolean) {
            (Some(b1), Some(b2)) => Some(b1.join(*b2)),
            (Some(b), None) | (None, Some(b)) => Some(*b),
            (None, None) => None,
        };
        Self {
            sign,
            interval,
            boolean,
            is_deterministic: self.is_deterministic && other.is_deterministic,
            is_pure: self.is_pure && other.is_pure,
        }
    }

    /// Partial order check `self <= other` across sign, interval, and boolean components.
    pub fn is_le(&self, other: &Self) -> bool {
        if self.sign == AbstractSign::Bottom {
            return true;
        }
        if !self.sign.is_le(other.sign) {
            return false;
        }
        let iv_le = match (&self.interval, &other.interval) {
            (Some(i1), Some(i2)) => i1.is_le(i2),
            (_, None) => true,
            (None, Some(_)) => false,
        };
        if !iv_le {
            return false;
        }
        match (&self.boolean, &other.boolean) {
            (Some(b1), Some(b2)) => b1.is_le(*b2),
            (_, None) => true,
            (None, Some(b2)) => *b2 == AbstractBool::Top,
        }
    }

    /// Abstract interpretation widening: accelerates fixpoint calculation.
    pub fn widen(&self, other: &Self) -> Self {
        let sign = self.sign.join(other.sign);
        let is_non_neg = self.sign.is_le(AbstractSign::NonNegative)
            && other.sign.is_le(AbstractSign::NonNegative);
        let interval = match (&self.interval, &other.interval) {
            (Some(i1), Some(i2)) => Some(if is_non_neg {
                i1.nat_widen(i2)
            } else {
                i1.widen(i2)
            }),
            _ => None,
        };
        let boolean = match (&self.boolean, &other.boolean) {
            (Some(b1), Some(b2)) => Some(b1.join(*b2)),
            (Some(b), None) | (None, Some(b)) => Some(*b),
            (None, None) => None,
        };
        Self {
            sign,
            interval,
            boolean,
            is_deterministic: self.is_deterministic && other.is_deterministic,
            is_pure: self.is_pure && other.is_pure,
        }
        .refine_nat()
    }

    /// Threshold widening on `AbstractState` using sorted `thresholds` (`MOLLER-SPA s5.12 p1`).
    pub fn widen_with_thresholds(&self, other: &Self, thresholds: &[i64]) -> Self {
        let sign = self.sign.join(other.sign);
        let interval = match (&self.interval, &other.interval) {
            (Some(i1), Some(i2)) => Some(i1.widen_with_thresholds(i2, thresholds)),
            _ => None,
        };
        let boolean = match (&self.boolean, &other.boolean) {
            (Some(b1), Some(b2)) => Some(b1.join(*b2)),
            (Some(b), None) | (None, Some(b)) => Some(*b),
            (None, None) => None,
        };
        Self {
            sign,
            interval,
            boolean,
            is_deterministic: self.is_deterministic && other.is_deterministic,
            is_pure: self.is_pure && other.is_pure,
        }
        .refine_nat()
    }

    /// Mutually refines `self` against a `NatCongruence` via Granger reduction (`COUSOT s38.1 p1`).
    /// Returns `None` if the state is provably unreachable (`Bottom`).
    pub fn refine_with_congruence(
        self,
        cg: crate::congruence::NatCongruence,
    ) -> Option<(Self, crate::congruence::NatCongruence)> {
        let s = self.refine_nat();
        if cg.is_bottom() || s.sign == AbstractSign::Bottom {
            return None;
        }
        if let Some(iv) = s.interval {
            let (new_iv, new_cg) = crate::congruence::reduce_interval_congruence(iv, cg)?;
            let mut next = s;
            next.interval = Some(new_iv);
            Some((next.refine_nat(), new_cg))
        } else {
            Some((s, cg))
        }
    }

    /// Abstract interpretation narrowing: refines post-fixpoints.
    pub fn narrow(&self, other: &Self) -> Self {
        let sign = self.sign.meet(other.sign);
        let interval = match (&self.interval, &other.interval) {
            (Some(i1), Some(i2)) => Some(i1.narrow(i2)),
            _ => None,
        };
        let boolean = match (&self.boolean, &other.boolean) {
            (Some(b1), Some(b2)) => Some(b1.meet(*b2)),
            (Some(b), None) | (None, Some(b)) => Some(*b),
            (None, None) => None,
        };
        Self {
            sign,
            interval,
            boolean,
            is_deterministic: self.is_deterministic && other.is_deterministic,
            is_pure: self.is_pure && other.is_pure,
        }
    }
}

/// Packed 64-bit vector holding 16 abstract sign lattice elements (4 bits per slot).
/// Enables SIMD-style parallel join, meet, and subsumption in a single CPU register cycle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct PackedSignVector(pub u64);

impl PackedSignVector {
    pub const CAPACITY: usize = 16;

    #[inline(always)]
    pub fn new() -> Self {
        Self(0)
    }

    #[inline(always)]
    pub fn get(&self, index: usize) -> AbstractSign {
        if index >= Self::CAPACITY {
            return AbstractSign::Bottom;
        }
        let shift = index * 4;
        let val = ((self.0 >> shift) & 0x0F) as u8;
        AbstractSign::from_u8(val)
    }

    #[inline(always)]
    pub fn set(&mut self, index: usize, sign: AbstractSign) {
        if index >= Self::CAPACITY {
            return;
        }
        let shift = index * 4;
        let mask = !(0x0Fu64 << shift);
        let val = (sign.as_u8() as u64) & 0x0F;
        self.0 = (self.0 & mask) | (val << shift);
    }

    /// Parallel join of 16 lattice slots in a single 64-bit bitwise OR instruction.
    #[inline(always)]
    pub fn join(&self, other: &Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Parallel meet of 16 lattice slots in a single 64-bit bitwise AND instruction.
    #[inline(always)]
    pub fn meet(&self, other: &Self) -> Self {
        Self(self.0 & other.0)
    }

    /// Vectorized check: all 16 slots satisfy self[i] <= other[i].
    #[inline(always)]
    pub fn is_le(&self, other: &Self) -> bool {
        (self.0 | other.0) == other.0
    }
}
