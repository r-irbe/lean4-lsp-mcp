//! src/octagon.rs
//! Coherent Difference-Bound Matrix for the Octagon Relational Domain over `Nat`
//! (Mine 2006 "The Octagon Abstract Domain"; Cousot 2021 Ch. 42 & 51; Pelleau 2015 Ch. 3).
//!
//! Tracks relational sum and difference constraints of the form:
//! - `v_a - v_b <= c`
//! - `v_a + v_b <= c`
//! - `-v_a - v_b <= c` (i.e., `v_a + v_b >= -c`)
//! - unary bounds `2 * v_a <= 2 * hi` and `-2 * v_a <= -2 * lo`
//!
//! Variable encoding (Mine 2006 Section 3.1):
//! Each variable `v in 0..(MAX_OCT_VARS - 1)` is represented by two indices:
//! - `pos(v) = 2 * v`     representing `+v`
//! - `neg(v) = 2 * v + 1` representing `-v`
//! with bar involution `bar(i) = i ^ 1`.
//!
//! Matrix entry `m[i][j]` encodes the upper bound `x_i - x_j <= m[i][j]`:
//! - `v_a - v_b <= c`: `m[pos(a)][pos(b)] <= c` and `m[neg(b)][neg(a)] <= c`
//! - `v_a + v_b <= c`: `m[pos(a)][neg(b)] <= c` and `m[pos(b)][neg(a)] <= c`
//! - `v_a + v_b >= c`: `m[neg(a)][pos(b)] <= -c` and `m[neg(b)][pos(a)] <= -c`
//! - `v_a <= hi`:      `m[pos(a)][neg(a)] <= 2 * hi`
//! - `v_a >= lo`:      `m[neg(a)][pos(a)] <= -2 * lo`
//!
//! Strong closure over integers (Bagherzadeh / Mine integer tightening):
//! 1. Shortest-path Floyd-Warshall closure: `m[i][j] = min_k (m[i][k] + m[k][j])`
//! 2. Unary even-tightening: `m[i][bar(i)] = 2 * floor(m[i][bar(i)] / 2)`
//! 3. Strengthening: `m[i][j] = min(m[i][j], (m[i][bar(i)] + m[bar(j)][j]) / 2)`
//!
//! 

use crate::lattice::{AbstractBool, IntervalBound};
use crate::nat_interval::INF;

/// Maximum number of `Nat` variables tracked simultaneously in an Octagon (`0..MAX_OCT_VARS`).
pub const MAX_OCT_VARS: usize = 6;
const OCT_DIM: usize = 2 * MAX_OCT_VARS;

#[inline]
const fn pos(v: usize) -> usize {
    2 * v
}

#[inline]
const fn neg(v: usize) -> usize {
    2 * v + 1
}

#[inline]
const fn bar(i: usize) -> usize {
    i ^ 1
}

#[inline]
fn add_weight(a: i64, b: i64) -> i64 {
    if a >= INF || b >= INF {
        INF
    } else {
        let s = (a as i128) + (b as i128);
        if s >= INF as i128 {
            INF
        } else if s <= i64::MIN as i128 {
            i64::MIN
        } else {
            s as i64
        }
    }
}

#[inline]
fn floor_div2(x: i64) -> i64 {
    if x >= 0 {
        x / 2
    } else {
        (x - 1) / 2
    }
}

/// Coherent $2N \times 2N$ Octagon relational domain over up to `MAX_OCT_VARS` `Nat` variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NatOctagonDomain {
    m: [[i64; OCT_DIM]; OCT_DIM],
    is_bottom: bool,
}

impl Default for NatOctagonDomain {
    fn default() -> Self {
        Self::top()
    }
}

impl NatOctagonDomain {
    /// Top octagon over `Nat`: `0 <= v_a < +oo` for all `a in 0..MAX_OCT_VARS`.
    pub fn top() -> Self {
        let mut m = [[INF; OCT_DIM]; OCT_DIM];
        for i in 0..OCT_DIM {
            m[i][i] = 0;
        }
        // Every Nat variable v_a satisfies v_a >= 0, i.e., -2 * v_a <= 0 => m[neg(a)][pos(a)] <= 0.
        // Also for any two Nat variables, -v_a - v_b <= 0 => m[neg(a)][pos(b)] <= 0.
        for a in 0..MAX_OCT_VARS {
            for b in 0..MAX_OCT_VARS {
                m[neg(a)][pos(b)] = 0;
            }
        }
        Self {
            m,
            is_bottom: false,
        }
    }

    /// Unreachable (empty) octagon.
    pub const fn bottom() -> Self {
        Self {
            m: [[0; OCT_DIM]; OCT_DIM],
            is_bottom: true,
        }
    }

    #[inline]
    pub const fn is_bottom(&self) -> bool {
        self.is_bottom
    }

    /// Sets a coherent matrix entry `m[i][j] = min(m[i][j], c)` and `m[bar(j)][bar(i)] = min(..., c)`.
    #[inline]
    fn tighten_coherent(&mut self, i: usize, j: usize, c: i64) {
        if c < self.m[i][j] {
            self.m[i][j] = c;
        }
        let bj = bar(j);
        let bi = bar(i);
        if c < self.m[bj][bi] {
            self.m[bj][bi] = c;
        }
    }

    /// Computes integer strong closure (Mine 2006 / Bagherzadeh integer octagon closure).
    /// Returns `false` if a negative cycle or empty interval is detected (setting `self` to bottom).
    pub fn strong_close(&mut self) -> bool {
        if self.is_bottom {
            return false;
        }

        // 1. All-pairs shortest-path closure (Floyd-Warshall) preserving coherence.
        for k in 0..OCT_DIM {
            for i in 0..OCT_DIM {
                let mik = self.m[i][k];
                if mik >= INF {
                    continue;
                }
                for j in 0..OCT_DIM {
                    let mkj = self.m[k][j];
                    if mkj >= INF {
                        continue;
                    }
                    let via_k = add_weight(mik, mkj);
                    if via_k < self.m[i][j] {
                        self.m[i][j] = via_k;
                    }
                }
            }
        }

        // Check for negative diagonal cycles before unary tightening.
        for i in 0..OCT_DIM {
            if self.m[i][i] < 0 {
                *self = Self::bottom();
                return false;
            }
            self.m[i][i] = 0;
        }

        // 2. Integer unary tightening: `x_i - x_{bar(i)} = 2 * x_i <= c` implies `2 * x_i <= 2 * floor(c / 2)`.
        for i in 0..OCT_DIM {
            let bi = bar(i);
            let c = self.m[i][bi];
            if c < INF {
                let half = floor_div2(c);
                let even_c = add_weight(half, half);
                if even_c < self.m[i][bi] {
                    self.m[i][bi] = even_c;
                }
            }
        }

        // Check unary feasibility: `m[pos(a)][neg(a)] + m[neg(a)][pos(a)] >= 0`.
        for a in 0..MAX_OCT_VARS {
            let p = pos(a);
            let n = neg(a);
            if add_weight(self.m[p][n], self.m[n][p]) < 0 {
                *self = Self::bottom();
                return false;
            }
        }

        // 3. Strengthening step: `m[i][j] = min(m[i][j], floor((m[i][bar(i)] + m[bar(j)][j]) / 2))`.
        for i in 0..OCT_DIM {
            let bi = bar(i);
            let m_ibi = self.m[i][bi];
            if m_ibi >= INF {
                continue;
            }
            for j in 0..OCT_DIM {
                let bj = bar(j);
                let m_bjj = self.m[bj][j];
                if m_bjj >= INF {
                    continue;
                }
                let sum = add_weight(m_ibi, m_bjj);
                if sum < INF {
                    let bound = floor_div2(sum);
                    if bound < self.m[i][j] {
                        self.m[i][j] = bound;
                    }
                }
            }
        }

        // Re-check diagonal after strengthening.
        for i in 0..OCT_DIM {
            if self.m[i][i] < 0 {
                *self = Self::bottom();
                return false;
            }
            self.m[i][i] = 0;
        }

        true
    }

    /// Adds difference constraint `v_a - v_b <= c` and restores strong closure.
    pub fn add_diff_le(&mut self, a: usize, b: usize, c: i64) -> bool {
        if self.is_bottom || a >= MAX_OCT_VARS || b >= MAX_OCT_VARS {
            return !self.is_bottom;
        }
        self.tighten_coherent(pos(a), pos(b), c);
        self.strong_close()
    }

    /// Adds sum upper bound `v_a + v_b <= c` and restores strong closure.
    pub fn add_sum_le(&mut self, a: usize, b: usize, c: i64) -> bool {
        if self.is_bottom || a >= MAX_OCT_VARS || b >= MAX_OCT_VARS {
            return !self.is_bottom;
        }
        self.tighten_coherent(pos(a), neg(b), c);
        self.strong_close()
    }

    /// Adds sum lower bound `v_a + v_b >= c` (i.e., `-v_a - v_b <= -c`) and restores strong closure.
    pub fn add_sum_ge(&mut self, a: usize, b: usize, c: i64) -> bool {
        if self.is_bottom || a >= MAX_OCT_VARS || b >= MAX_OCT_VARS {
            return !self.is_bottom;
        }
        let neg_c = if c <= -INF { INF } else { -c };
        self.tighten_coherent(neg(a), pos(b), neg_c);
        self.strong_close()
    }

    /// Refines variable `a` with an `IntervalBound` `[lo, hi]` and restores strong closure.
    pub fn set_interval(&mut self, a: usize, iv: IntervalBound) -> bool {
        if self.is_bottom || a >= MAX_OCT_VARS {
            return !self.is_bottom;
        }
        if iv.min > iv.max || iv.max < 0 {
            *self = Self::bottom();
            return false;
        }
        let lo = iv.min.max(0);
        if iv.max < INF {
            self.tighten_coherent(pos(a), neg(a), add_weight(iv.max, iv.max));
        }
        if lo < INF {
            self.tighten_coherent(neg(a), pos(a), -add_weight(lo, lo));
        }
        self.strong_close()
    }

    /// Projects variable `a` (`0..MAX_OCT_VARS`) to its tightest `IntervalBound` `[lo, hi]`.
    pub fn get_interval(&self, a: usize) -> Option<IntervalBound> {
        if self.is_bottom || a >= MAX_OCT_VARS {
            return None;
        }
        let m_pn = self.m[pos(a)][neg(a)];
        let hi = if m_pn >= INF { INF } else { floor_div2(m_pn) };
        let m_np = self.m[neg(a)][pos(a)];
        let lo = if m_np >= INF {
            0
        } else {
            (-floor_div2(m_np)).max(0)
        };
        if lo > hi {
            None
        } else {
            Some(IntervalBound::new(lo, hi))
        }
    }

    /// Upper bound on `v_a - v_b` (`None` if bottom).
    pub fn diff_bound(&self, a: usize, b: usize) -> Option<i64> {
        if self.is_bottom || a >= MAX_OCT_VARS || b >= MAX_OCT_VARS {
            None
        } else {
            Some(self.m[pos(a)][pos(b)])
        }
    }

    /// Upper bound on `v_a + v_b` (`None` if bottom).
    pub fn sum_upper_bound(&self, a: usize, b: usize) -> Option<i64> {
        if self.is_bottom || a >= MAX_OCT_VARS || b >= MAX_OCT_VARS {
            None
        } else {
            Some(self.m[pos(a)][neg(b)])
        }
    }

    /// Lower bound on `v_a + v_b` (`None` if bottom).
    pub fn sum_lower_bound(&self, a: usize, b: usize) -> Option<i64> {
        if self.is_bottom || a >= MAX_OCT_VARS || b >= MAX_OCT_VARS {
            None
        } else {
            let v = self.m[neg(a)][pos(b)];
            if v >= INF {
                Some(0)
            } else {
                Some((-v).max(0))
            }
        }
    }

    /// Pointwise join (least upper bound) of two strongly closed octagons.
    pub fn join(&self, other: &Self) -> Self {
        if self.is_bottom {
            return *other;
        }
        if other.is_bottom {
            return *self;
        }
        let mut out = Self::top();
        for i in 0..OCT_DIM {
            for j in 0..OCT_DIM {
                out.m[i][j] = self.m[i][j].max(other.m[i][j]);
            }
        }
        out
    }

    /// Pointwise meet (greatest lower bound) followed by strong closure.
    pub fn meet(&self, other: &Self) -> Self {
        if self.is_bottom || other.is_bottom {
            return Self::bottom();
        }
        let mut out = *self;
        for i in 0..OCT_DIM {
            for j in 0..OCT_DIM {
                if other.m[i][j] < out.m[i][j] {
                    out.m[i][j] = other.m[i][j];
                }
            }
        }
        out.strong_close();
        out
    }

    /// Standard octagon widening (`self \nabla next`): keeps bounds that do not grow, drops growing bounds to `INF`.
    pub fn widen(&self, next: &Self) -> Self {
        if self.is_bottom {
            return *next;
        }
        if next.is_bottom {
            return *self;
        }
        let mut out = *self;
        for i in 0..OCT_DIM {
            for j in 0..OCT_DIM {
                if next.m[i][j] > self.m[i][j] {
                    out.m[i][j] = INF;
                }
            }
        }
        out
    }

    /// Evaluates whether a simplex sum bound `v_a + v_b <= cap` holds across the octagon.
    pub fn check_sum_le(&self, a: usize, b: usize, cap: i64) -> AbstractBool {
        if self.is_bottom || a >= MAX_OCT_VARS || b >= MAX_OCT_VARS {
            return AbstractBool::Bottom;
        }
        let hi = self.m[pos(a)][neg(b)];
        let lo = self.sum_lower_bound(a, b).unwrap_or(0);
        if hi <= cap {
            AbstractBool::True
        } else if lo > cap {
            AbstractBool::False
        } else {
            AbstractBool::Top
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_octagon_simplex_conservation_tightens_intervals() {
        // Two simplex weights p0, p1 >= 0 with p0 + p1 == 100 and p0 >= 30
        // Strong closure must deduce p0 in [30, 100] and p1 in [0, 70]!
        let mut oct = NatOctagonDomain::top();
        assert!(oct.add_sum_le(0, 1, 100));
        assert!(oct.add_sum_ge(0, 1, 100));
        assert!(oct.set_interval(0, IntervalBound::new(30, 100)));

        let iv0 = oct.get_interval(0).unwrap();
        let iv1 = oct.get_interval(1).unwrap();
        assert_eq!(iv0, IntervalBound::new(30, 100));
        assert_eq!(iv1, IntervalBound::new(0, 70));
        assert_eq!(oct.check_sum_le(0, 1, 100), AbstractBool::True);
        assert_eq!(oct.check_sum_le(0, 1, 99), AbstractBool::False);
    }

    #[test]
    fn test_octagon_sum_and_diff_parity_tightening() {
        // v0 + v1 <= 10 and v0 - v1 <= 4 => 2 * v0 <= 14 => v0 <= 7.
        // Even with odd bounds: v0 + v1 <= 9 and v0 - v1 <= 4 => 2 * v0 <= 13 => 2 * v0 <= 12 => v0 <= 6!
        let mut oct = NatOctagonDomain::top();
        assert!(oct.add_sum_le(0, 1, 9));
        assert!(oct.add_diff_le(0, 1, 4));
        let iv0 = oct.get_interval(0).unwrap();
        assert_eq!(iv0, IntervalBound::new(0, 6));
    }

    #[test]
    fn test_octagon_infeasible_sum_detects_bottom() {
        let mut oct = NatOctagonDomain::top();
        assert!(oct.set_interval(0, IntervalBound::new(60, 80)));
        assert!(oct.set_interval(1, IntervalBound::new(50, 70)));
        // Minimum sum is 110, so v0 + v1 <= 100 is infeasible!
        assert!(!oct.add_sum_le(0, 1, 100));
        assert!(oct.is_bottom());
    }

    #[test]
    fn test_octagon_join_meet_and_widen() {
        let mut a = NatOctagonDomain::top();
        a.add_sum_le(0, 1, 100);
        let mut b = NatOctagonDomain::top();
        b.add_sum_le(0, 1, 120);

        let j = a.join(&b);
        assert_eq!(j.sum_upper_bound(0, 1), Some(120));

        let m = a.meet(&b);
        assert_eq!(m.sum_upper_bound(0, 1), Some(100));

        let w = a.widen(&b);
        assert_eq!(w.sum_upper_bound(0, 1), Some(INF));
    }
}
