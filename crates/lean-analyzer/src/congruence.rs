//! src/congruence.rs
//! Cartesian congruence abstract domain for natural numbers (Granger 1989; Cousot 2021 Ch. 40).
//!
//! Represents residue classes `stride * N + offset` (written `offset (mod stride)`),
//! plus `Bottom` (unreachable) and singleton constants (`stride == 0`, meaning `{offset}`).
//! Top (`N`) is canonically `NatCongruence { stride: 1, offset: 0 }`.
//!
//! Provides:
//! - Canonical normalization (`0 <= offset < stride` when `stride > 0`).
//! - Exact lattice `join` via `gcd(s1, s2, |o1 - o2|)` and `meet` via Extended GCD (CRT).
//! - Abstract arithmetic transfer functions (`add`, `nat_sub`, `mul`, `nat_succ`, `nat_pred`,
//!   `nat_shl`, `nat_shr`, `nat_mod`, `nat_div`) sound with respect to Lean 4 `Nat` semantics.
//! - Mutual Granger reduction `reduce_interval_congruence(&IntervalBound, &NatCongruence)`
//!   tightening interval endpoints to the nearest matching residue class and collapsing
//!   single-point intervals to exact singleton congruences.
//!
//! 

use crate::lattice::{AbstractBool, IntervalBound};
use crate::nat_interval::INF;

/// Greatest common divisor on `u64` (`gcd(0, x) = x`, `gcd(x, 0) = x`).
#[inline]
pub const fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

/// Extended Euclidean algorithm on `i128`: returns `(g, x, y)` such that `a * x + b * y = g = gcd(a, b)`.
#[inline]
pub fn ext_gcd_i128(a: i128, b: i128) -> (i128, i128, i128) {
    if b == 0 {
        if a >= 0 {
            (a, 1, 0)
        } else {
            (-a, -1, 0)
        }
    } else {
        let (g, x1, y1) = ext_gcd_i128(b, a % b);
        (g, y1, x1 - (a / b) * y1)
    }
}

/// Congruence abstract element over `Nat`:
/// - `Bottom`: empty set (`gamma(Bottom) = {}`).
/// - `Class { stride: 0, offset: c }`: singleton `{c}`.
/// - `Class { stride: s, offset: r }` with `s > 0` and `0 <= r < s`:
///   `{ r + k * s | k in Nat }`. Note that `stride = 1, offset = 0` is `Top` (`Nat`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NatCongruence {
    Bottom,
    Class { stride: u64, offset: u64 },
}

impl Default for NatCongruence {
    fn default() -> Self {
        Self::TOP
    }
}

impl NatCongruence {
    /// Top congruence `0 (mod 1)` covering all natural numbers.
    pub const TOP: Self = Self::Class {
        stride: 1,
        offset: 0,
    };

    /// Constructs a canonical congruence `offset (mod stride)`.
    #[inline]
    pub const fn new(stride: u64, offset: u64) -> Self {
        if stride == 0 {
            Self::Class { stride: 0, offset }
        } else {
            Self::Class {
                stride,
                offset: offset % stride,
            }
        }
    }

    /// Singleton congruence `{val}` (`stride = 0`).
    #[inline]
    pub const fn singleton(val: u64) -> Self {
        Self::Class {
            stride: 0,
            offset: val,
        }
    }

    #[inline]
    pub const fn is_bottom(&self) -> bool {
        matches!(self, Self::Bottom)
    }

    #[inline]
    pub const fn is_top(&self) -> bool {
        matches!(
            self,
            Self::Class {
                stride: 1,
                offset: 0
            }
        )
    }

    /// Checks whether concrete natural `n` belongs to `gamma(self)`.
    #[inline]
    pub const fn contains(&self, n: u64) -> bool {
        match *self {
            Self::Bottom => false,
            Self::Class { stride: 0, offset } => n == offset,
            Self::Class { stride, offset } => (n % stride) == (offset % stride),
        }
    }

    /// Partial order `self <= other` (`gamma(self) subseteq gamma(other)`).
    #[inline]
    pub const fn is_le(&self, other: &Self) -> bool {
        match (*self, *other) {
            (Self::Bottom, _) => true,
            (_, Self::Bottom) => false,
            (
                Self::Class {
                    stride: s1,
                    offset: o1,
                },
                Self::Class {
                    stride: s2,
                    offset: o2,
                },
            ) => {
                if s2 == 0 {
                    s1 == 0 && o1 == o2
                } else {
                    (s1 % s2 == 0) && (o1 % s2 == o2 % s2)
                }
            }
        }
    }

    /// Least upper bound (Granger 1989):
    /// `(s1 Z + o1) join (s2 Z + o2) = gcd(s1, s2, |o1 - o2|) Z + (o1 mod g)`.
    #[inline]
    pub const fn join(&self, other: &Self) -> Self {
        match (*self, *other) {
            (Self::Bottom, x) | (x, Self::Bottom) => x,
            (
                Self::Class {
                    stride: s1,
                    offset: o1,
                },
                Self::Class {
                    stride: s2,
                    offset: o2,
                },
            ) => {
                let diff = o1.abs_diff(o2);
                let g = gcd_u64(gcd_u64(s1, s2), diff);
                Self::new(g, o1)
            }
        }
    }

    /// Greatest lower bound via Chinese Remainder Theorem (Extended GCD).
    /// Returns `Bottom` if the two residue classes are disjoint.
    pub fn meet(&self, other: &Self) -> Self {
        match (*self, *other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (
                Self::Class {
                    stride: 0,
                    offset: o1,
                },
                c2,
            ) => {
                if c2.contains(o1) {
                    Self::singleton(o1)
                } else {
                    Self::Bottom
                }
            }
            (
                c1,
                Self::Class {
                    stride: 0,
                    offset: o2,
                },
            ) => {
                if c1.contains(o2) {
                    Self::singleton(o2)
                } else {
                    Self::Bottom
                }
            }
            (
                Self::Class {
                    stride: s1,
                    offset: o1,
                },
                Self::Class {
                    stride: s2,
                    offset: o2,
                },
            ) => {
                let (g, u, _v) = ext_gcd_i128(s1 as i128, s2 as i128);
                let diff = (o2 as i128) - (o1 as i128);
                if diff % g != 0 {
                    return Self::Bottom;
                }
                let s1_div_g = (s1 as i128) / g;
                let s2_div_g = (s2 as i128) / g;
                let lcm_i128 = match s1_div_g.checked_mul(s2 as i128) {
                    Some(v) if v <= u64::MAX as i128 => v,
                    _ => {
                        // If lcm overflows u64, fall back conservatively to the finer stride.
                        return if s1 >= s2 { *self } else { *other };
                    }
                };
                // Solve o = o1 + s1 * k where k = (diff / g) * u (mod s2 / g)
                let factor = ((diff / g) % s2_div_g) * (u % s2_div_g);
                let k = factor.rem_euclid(s2_div_g);
                let combined_offset = ((o1 as i128) + (s1 as i128) * k).rem_euclid(lcm_i128);
                Self::new(lcm_i128 as u64, combined_offset as u64)
            }
        }
    }

    /// Widening on congruences: because every divisor chain of `stride` in `Nat`
    /// is finite (except from `stride = 0`), jumping from `0` to `gcd` via `join`
    /// already satisfies the ascending chain condition.
    #[inline]
    pub const fn widen(&self, other: &Self) -> Self {
        self.join(other)
    }

    /// Narrowing on congruences: refines with `meet`.
    #[inline]
    pub fn narrow(&self, other: &Self) -> Self {
        self.meet(other)
    }

    /// Abstract addition `(s1 N + o1) + (s2 N + o2) = gcd(s1, s2) N + (o1 + o2)`.
    #[inline]
    pub const fn add(&self, other: &Self) -> Self {
        match (*self, *other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (
                Self::Class {
                    stride: s1,
                    offset: o1,
                },
                Self::Class {
                    stride: s2,
                    offset: o2,
                },
            ) => {
                let g = gcd_u64(s1, s2);
                match o1.checked_add(o2) {
                    Some(sum) => Self::new(g, sum),
                    None => {
                        if g == 0 {
                            Self::TOP
                        } else {
                            let rem = ((o1 as u128 + o2 as u128) % (g as u128)) as u64;
                            Self::new(g, rem)
                        }
                    }
                }
            }
        }
    }

    /// Abstract multiplication `(s1 N + o1) * (s2 N + o2)`:
    /// stride is `gcd(s1 * s2, gcd(s1 * o2, s2 * o1))`, offset is `o1 * o2`.
    #[inline]
    pub const fn mul(&self, other: &Self) -> Self {
        match (*self, *other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (
                Self::Class {
                    stride: 0,
                    offset: 0,
                },
                _,
            )
            | (
                _,
                Self::Class {
                    stride: 0,
                    offset: 0,
                },
            ) => Self::singleton(0),
            (
                Self::Class {
                    stride: s1,
                    offset: o1,
                },
                Self::Class {
                    stride: s2,
                    offset: o2,
                },
            ) => {
                let p_s1_s2 = s1.saturating_mul(s2);
                let p_s1_o2 = s1.saturating_mul(o2);
                let p_s2_o1 = s2.saturating_mul(o1);
                if p_s1_s2 == u64::MAX || p_s1_o2 == u64::MAX || p_s2_o1 == u64::MAX {
                    return Self::TOP;
                }
                let g = gcd_u64(p_s1_s2, gcd_u64(p_s1_o2, p_s2_o1));
                match o1.checked_mul(o2) {
                    Some(prod) => Self::new(g, prod),
                    None => {
                        if g == 0 {
                            Self::TOP
                        } else {
                            let rem = ((o1 as u128 * o2 as u128) % (g as u128)) as u64;
                            Self::new(g, rem)
                        }
                    }
                }
            }
        }
    }

    /// Abstract successor `n + 1`.
    #[inline]
    pub const fn nat_succ(&self) -> Self {
        self.add(&Self::singleton(1))
    }

    /// Abstract predecessor `Nat.pred n`:
    /// Note that in Lean 4, `Nat.pred 0 = 0`, so `0` maps to `0` rather than `-1`.
    /// When `self` is proven strictly positive (e.g., `offset > 0` and `stride == 0`),
    /// `Nat.pred` is exact; otherwise we join the `0 -> 0` case if `self.contains(0)`.
    #[inline]
    pub const fn nat_pred(&self) -> Self {
        match *self {
            Self::Bottom => Self::Bottom,
            Self::Class { stride: 0, offset } => Self::singleton(offset.saturating_sub(1)),
            Self::Class { stride, offset } => {
                let shifted = if offset == 0 {
                    stride - 1
                } else {
                    offset - 1
                };
                let pred_nonzero = Self::new(stride, shifted);
                if self.contains(0) {
                    pred_nonzero.join(&Self::singleton(0))
                } else {
                    pred_nonzero
                }
            }
        }
    }

    /// Abstract saturating subtraction `a - b` in Lean `Nat`.
    /// Because `a - b = 0` whenever `a <= b`, modular congruence is only preserved
    /// when `b` is a singleton `{0}` or both are singletons; otherwise if `a >= b`
    /// is not guaranteed by the congruence alone, `0` may also be produced.
    #[inline]
    pub const fn nat_sub(&self, other: &Self, guaranteed_ge: bool) -> Self {
        match (*self, *other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (
                Self::Class {
                    stride: 0,
                    offset: o1,
                },
                Self::Class {
                    stride: 0,
                    offset: o2,
                },
            ) => Self::singleton(o1.saturating_sub(o2)),
            (
                c1,
                Self::Class {
                    stride: 0,
                    offset: 0,
                },
            ) => c1,
            (
                Self::Class {
                    stride: s1,
                    offset: o1,
                },
                Self::Class {
                    stride: s2,
                    offset: o2,
                },
            ) => {
                let g = gcd_u64(s1, s2);
                if g == 0 {
                    return Self::singleton(o1.saturating_sub(o2));
                }
                let rem1 = o1 % g;
                let rem2 = o2 % g;
                let diff_rem = if rem1 >= rem2 {
                    rem1 - rem2
                } else {
                    g - (rem2 - rem1)
                };
                let modular = Self::new(g, diff_rem);
                if guaranteed_ge {
                    modular
                } else {
                    modular.join(&Self::singleton(0))
                }
            }
        }
    }

    /// Abstract modulo `a % b` in Lean `Nat` (`a % 0 = a`).
    #[inline]
    pub const fn nat_mod(&self, other: &Self) -> Self {
        match (*self, *other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (
                c1,
                Self::Class {
                    stride: 0,
                    offset: 0,
                },
            ) => c1,
            (
                Self::Class {
                    stride: 0,
                    offset: o1,
                },
                Self::Class {
                    stride: 0,
                    offset: o2,
                },
            ) => Self::singleton(o1 % o2),
            (
                Self::Class {
                    stride: s1,
                    offset: o1,
                },
                Self::Class {
                    stride: s2,
                    offset: o2,
                },
            ) => {
                // Any x = o1 + k1*s1 and m = o2 + k2*s2 (for m > 0) satisfies
                // x mod m = x - q*m, so gcd(s1, s2, o2) divides (x mod m) - o1.
                // Because Lean has x % 0 = x, that relation also holds at m = 0!
                let g = gcd_u64(s1, gcd_u64(s2, o2));
                Self::new(g, o1)
            }
        }
    }

    /// Abstract shift-left `a <<< b = a * 2^b`.
    #[inline]
    pub const fn nat_shl(&self, other: &Self) -> Self {
        match (*self, *other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (
                Self::Class {
                    stride: 0,
                    offset: 0,
                },
                _,
            ) => Self::singleton(0),
            (
                Self::Class { .. },
                Self::Class {
                    stride: 0,
                    offset: k,
                },
            ) => {
                if k >= 64 {
                    Self::TOP
                } else {
                    let factor = 1u64 << k;
                    self.mul(&Self::singleton(factor))
                }
            }
            (
                _,
                Self::Class {
                    stride: _s2,
                    offset: min_k,
                },
            ) => {
                // If s2 > 0, k >= min_k, so 2^min_k divides 2^k when min_k > 0.
                if min_k == 0 || min_k >= 64 {
                    Self::TOP
                } else {
                    Self::new(1u64 << min_k, 0)
                }
            }
        }
    }

    /// Equality test over congruences: returns `False` if the two classes have empty meet.
    #[inline]
    pub fn beq(&self, other: &Self) -> AbstractBool {
        match (*self, *other) {
            (Self::Bottom, _) | (_, Self::Bottom) => AbstractBool::Bottom,
            (
                Self::Class {
                    stride: 0,
                    offset: o1,
                },
                Self::Class {
                    stride: 0,
                    offset: o2,
                },
            ) => {
                if o1 == o2 {
                    AbstractBool::True
                } else {
                    AbstractBool::False
                }
            }
            _ => {
                if self.meet(other).is_bottom() {
                    AbstractBool::False
                } else {
                    AbstractBool::Top
                }
            }
        }
    }
}

/// Mutual Granger reduction `rho(interval, congruence)` (Cousot 2021 Ch. 38 & Ch. 40):
/// Tightens `[min, max]` to the smallest sub-interval whose endpoints satisfy `congruence`,
/// and refines `congruence` to a singleton whenever the tightened interval is a point `[c, c]`.
/// Returns `None` if the intersection is empty (unreachable state).
pub fn reduce_interval_congruence(
    iv: IntervalBound,
    cg: NatCongruence,
) -> Option<(IntervalBound, NatCongruence)> {
    if iv.min > iv.max || iv.max < 0 {
        return None;
    }
    let lo = iv.min.max(0) as u64;
    let hi_is_inf = iv.max >= INF;
    let hi = iv.max.max(0) as u64;

    match cg {
        NatCongruence::Bottom => None,
        NatCongruence::Class { stride: 0, offset } => {
            if offset < lo {
                return None;
            }
            if !hi_is_inf && offset > hi {
                return None;
            }
            let clamped = if offset >= INF as u64 {
                INF
            } else {
                offset as i64
            };
            Some((IntervalBound::point(clamped), cg))
        }
        NatCongruence::Class { stride, offset } => {
            let rem = offset % stride;
            // Smallest x >= lo with x == rem (mod stride)
            let lo_rem = lo % stride;
            let delta_lo = if rem >= lo_rem {
                rem - lo_rem
            } else {
                stride - (lo_rem - rem)
            };
            let new_lo_u64 = lo.checked_add(delta_lo)?;
            if !hi_is_inf && new_lo_u64 > hi {
                return None;
            }
            let new_lo = if new_lo_u64 >= INF as u64 {
                INF
            } else {
                new_lo_u64 as i64
            };

            let new_hi = if hi_is_inf {
                INF
            } else {
                // Largest x <= hi with x == rem (mod stride)
                let hi_rem = hi % stride;
                let delta_hi = if hi_rem >= rem {
                    hi_rem - rem
                } else {
                    stride - (rem - hi_rem)
                };
                if hi < delta_hi {
                    return None;
                }
                let h = hi - delta_hi;
                if h < new_lo_u64 {
                    return None;
                }
                h as i64
            };

            let tightened_iv = IntervalBound::new(new_lo, new_hi);
            let tightened_cg = if new_lo == new_hi && new_hi != INF {
                NatCongruence::singleton(new_lo as u64)
            } else {
                NatCongruence::new(stride, rem)
            };
            Some((tightened_iv, tightened_cg))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_congruence_lattice_laws() {
        let even = NatCongruence::new(2, 0);
        let odd = NatCongruence::new(2, 1);
        let mod4_1 = NatCongruence::new(4, 1);
        let mod6_4 = NatCongruence::new(6, 4);

        // Disjoint classes meet to Bottom and join to Top
        assert_eq!(even.meet(&odd), NatCongruence::Bottom);
        assert_eq!(even.join(&odd), NatCongruence::TOP);

        // Subsumption: 1 (mod 4) <= 1 (mod 2)
        assert!(mod4_1.is_le(&odd));
        assert!(!odd.is_le(&mod4_1));
        assert_eq!(mod4_1.join(&odd), odd);
        assert_eq!(mod4_1.meet(&odd), mod4_1);

        // CRT meet: x == 1 (mod 4) and x == 4 (mod 6) -> impossible since 1 != 4 (mod gcd(4,6)=2)
        assert_eq!(mod4_1.meet(&mod6_4), NatCongruence::Bottom);

        // CRT meet: x == 2 (mod 4) and x == 4 (mod 6) -> x == 10 (mod 12)
        let mod4_2 = NatCongruence::new(4, 2);
        let m = mod4_2.meet(&mod6_4);
        assert_eq!(m, NatCongruence::new(12, 10));
        for n in 0..200 {
            assert_eq!(m.contains(n), mod4_2.contains(n) && mod6_4.contains(n));
        }
    }

    #[test]
    fn test_granger_interval_congruence_reduction() {
        // Scaled-integer grid: values in [1, 299] with 0 (mod 100) -> [100, 200]
        let iv = IntervalBound::new(1, 299);
        let cg = NatCongruence::new(100, 0);
        let (r_iv, r_cg) = reduce_interval_congruence(iv, cg).expect("non-empty");
        assert_eq!(r_iv, IntervalBound::new(100, 200));
        assert_eq!(r_cg, NatCongruence::new(100, 0));

        // Narrowing to a single point [95, 105] intersect 0 (mod 100) -> point 100 and singleton {100}
        let iv_single = IntervalBound::new(95, 105);
        let (r_iv2, r_cg2) = reduce_interval_congruence(iv_single, cg).expect("non-empty");
        assert_eq!(r_iv2, IntervalBound::point(100));
        assert_eq!(r_cg2, NatCongruence::singleton(100));

        // Unreachable: [101, 199] intersect 0 (mod 100) -> None
        let iv_empty = IntervalBound::new(101, 199);
        assert!(reduce_interval_congruence(iv_empty, cg).is_none());
    }

    #[test]
    fn test_congruence_transfer_soundness_grid() {
        let classes = [
            NatCongruence::singleton(0),
            NatCongruence::singleton(1),
            NatCongruence::singleton(5),
            NatCongruence::new(2, 0),
            NatCongruence::new(2, 1),
            NatCongruence::new(3, 2),
            NatCongruence::new(4, 3),
            NatCongruence::new(100, 0),
            NatCongruence::TOP,
        ];
        for c1 in &classes {
            for c2 in &classes {
                let c_add = c1.add(c2);
                let c_mul = c1.mul(c2);
                let c_sub = c1.nat_sub(c2, false);
                let c_mod = c1.nat_mod(c2);
                for x in 0..40u64 {
                    if !c1.contains(x) {
                        continue;
                    }
                    assert!(c1.nat_succ().contains(x + 1));
                    assert!(c1.nat_pred().contains(x.saturating_sub(1)));
                    for y in 0..40u64 {
                        if !c2.contains(y) {
                            continue;
                        }
                        assert!(c_add.contains(x + y));
                        assert!(c_mul.contains(x * y));
                        assert!(c_sub.contains(x.saturating_sub(y)));
                        let m = if y == 0 { x } else { x % y };
                        assert!(c_mod.contains(m));
                    }
                }
            }
        }
    }
}
