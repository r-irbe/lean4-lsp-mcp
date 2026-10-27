//! src/zone.rs
//! Compact Difference-Bound Matrix (Zone) relational abstract domain over `Nat`
//! (Mine 2001/2006; Cousot 2021 Ch. 51; Simon 2008 Ch. 8).
//!
//! Tracks relational difference constraints of the form:
//! - `v_i - v_j <= c` (for variables `1..=n`), and
//! - unary bounds `v_i - v_0 <= hi` (`v_i <= hi`) and `v_0 - v_i <= -lo` (`v_i >= lo`),
//! where index `0` is the special zero variable (`v_0 == 0`).
//!
//! Designed with zero heap allocation (`MAX_ZONE_VARS = 8`, 9x9 matrix of `i64` bounds)
//! for sub-millisecond incremental closure and discharge of Lean 4 termination obligations
//! (`decreasing_by` / `termination_by`, e.g., proving `n - (i + 1) < n - i` under `i < n`).
//!
//! 

use crate::lattice::{AbstractBool, IntervalBound};
use crate::nat_interval::INF;

/// Maximum number of local `Nat` variables tracked simultaneously in a Zone (`v_1 .. v_8`),
/// plus index `0` representing the constant `0`.
pub const MAX_ZONE_VARS: usize = 8;
const DIM: usize = MAX_ZONE_VARS + 1;

/// Saturated addition of two upper-bound weights in the DBM (`INF` = $+\infty$).
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

/// Difference-Bound Matrix over up to 8 `Nat` variables (`1..=MAX_ZONE_VARS`) plus `0` (`v_0 = 0`).
/// Entry `m[i][j]` encodes the invariant `v_i - v_j <= m[i][j]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NatZoneDomain {
    /// `m[i][j]` is the upper bound on `v_i - v_j` (`INF` if unbounded).
    m: [[i64; DIM]; DIM],
    /// True if the zone is provably empty (negative cycle detected).
    is_bottom: bool,
}

impl Default for NatZoneDomain {
    fn default() -> Self {
        Self::top()
    }
}

impl NatZoneDomain {
    /// Top zone over `Nat`: `0 <= v_i < +oo` for all variables `i in 1..=MAX_ZONE_VARS`.
    pub fn top() -> Self {
        let mut m = [[INF; DIM]; DIM];
        for i in 0..DIM {
            m[i][i] = 0;
            // Every variable in Nat is >= 0, i.e., v_0 - v_i <= 0.
            m[0][i] = 0;
        }
        Self {
            m,
            is_bottom: false,
        }
    }

    /// Unreachable (empty) zone.
    pub const fn bottom() -> Self {
        Self {
            m: [[0; DIM]; DIM],
            is_bottom: true,
        }
    }

    #[inline]
    pub const fn is_bottom(&self) -> bool {
        self.is_bottom
    }

    /// Raw upper bound on `v_i - v_j` (`None` if `self` is bottom).
    #[inline]
    pub fn diff_bound(&self, i: usize, j: usize) -> Option<i64> {
        if self.is_bottom || i >= DIM || j >= DIM {
            None
        } else {
            Some(self.m[i][j])
        }
    }

    /// Projects variable `v` (`1..=MAX_ZONE_VARS`) to its `IntervalBound` `[lo, hi]`.
    pub fn get_interval(&self, v: usize) -> Option<IntervalBound> {
        if self.is_bottom || v == 0 || v >= DIM {
            return None;
        }
        // v - v_0 <= m[v][0]  =>  v <= m[v][0]
        let hi = self.m[v][0];
        // v_0 - v <= m[0][v]  =>  -v <= m[0][v]  =>  v >= -m[0][v]
        let lo = if self.m[0][v] >= INF {
            0
        } else {
            (-self.m[0][v]).max(0)
        };
        if lo > hi {
            None
        } else {
            Some(IntervalBound::new(lo, hi))
        }
    }

    /// Adds a relational constraint `v_i - v_j <= c` and restores shortest-path closure.
    /// Variable indices are `1..=MAX_ZONE_VARS` (or `0` for the zero reference).
    pub fn add_constraint(&mut self, i: usize, j: usize, c: i64) -> bool {
        if self.is_bottom || i >= DIM || j >= DIM {
            return !self.is_bottom;
        }
        if c >= self.m[i][j] {
            return true;
        }
        self.m[i][j] = c;
        // Incremental single-edge shortest-path closure:
        // For all u, w: m[u][w] = min(m[u][w], m[u][i] + c + m[j][w])
        for u in 0..DIM {
            let ui = self.m[u][i];
            if ui >= INF {
                continue;
            }
            let uic = add_weight(ui, c);
            for w in 0..DIM {
                let jw = self.m[j][w];
                if jw >= INF {
                    continue;
                }
                let cand = add_weight(uic, jw);
                if cand < self.m[u][w] {
                    self.m[u][w] = cand;
                }
            }
        }
        for k in 0..DIM {
            if self.m[k][k] < 0 {
                self.is_bottom = true;
                return false;
            }
            self.m[k][k] = 0;
        }
        true
    }

    /// Full Floyd-Warshall shortest-path closure ($O(V^3)$ with $V = 9$).
    pub fn close(&mut self) -> bool {
        if self.is_bottom {
            return false;
        }
        for k in 0..DIM {
            for i in 0..DIM {
                let ik = self.m[i][k];
                if ik >= INF {
                    continue;
                }
                for j in 0..DIM {
                    let kj = self.m[k][j];
                    if kj >= INF {
                        continue;
                    }
                    let cand = add_weight(ik, kj);
                    if cand < self.m[i][j] {
                        self.m[i][j] = cand;
                    }
                }
            }
        }
        for k in 0..DIM {
            if self.m[k][k] < 0 {
                self.is_bottom = true;
                return false;
            }
            self.m[k][k] = 0;
        }
        true
    }

    /// Constrain `v` to lie within `iv = [lo, hi]`.
    pub fn constrain_interval(&mut self, v: usize, iv: IntervalBound) -> bool {
        if v == 0 || v >= DIM {
            return !self.is_bottom;
        }
        if iv.min > iv.max || iv.max < 0 {
            self.is_bottom = true;
            return false;
        }
        let lo = iv.min.max(0);
        if iv.max < INF && !self.add_constraint(v, 0, iv.max) {
            return false;
        }
        self.add_constraint(0, v, -lo)
    }

    /// Forget all information about variable `v` (`1..=MAX_ZONE_VARS`), resetting `v >= 0`.
    pub fn forget(&mut self, v: usize) {
        if self.is_bottom || v == 0 || v >= DIM {
            return;
        }
        for k in 0..DIM {
            self.m[v][k] = INF;
            self.m[k][v] = INF;
        }
        self.m[v][v] = 0;
        self.m[0][v] = 0;
    }

    /// Assignment `v_dst := v_src + offset` (with `offset >= 0` or guaranteed `v_src + offset >= 0`).
    pub fn assign_var_plus_const(&mut self, dst: usize, src: usize, offset: i64) -> bool {
        if self.is_bottom || dst == 0 || dst >= DIM || src >= DIM {
            return !self.is_bottom;
        }
        if dst == src {
            // Self-update v := v + offset
            for k in 0..DIM {
                if k != dst {
                    if self.m[dst][k] < INF {
                        self.m[dst][k] = add_weight(self.m[dst][k], offset);
                    }
                    if self.m[k][dst] < INF {
                        self.m[k][dst] = add_weight(self.m[k][dst], -offset);
                    }
                }
            }
            // Enforce Nat floor v >= 0
            if self.m[0][dst] > 0 {
                self.m[0][dst] = 0;
            }
            return self.close();
        }
        self.forget(dst);
        // v_dst - v_src <= offset  and  v_src - v_dst <= -offset
        if !self.add_constraint(dst, src, offset) {
            return false;
        }
        self.add_constraint(src, dst, -offset)
    }

    /// Pointwise join (least upper bound) of two closed zones.
    pub fn join(&self, other: &Self) -> Self {
        if self.is_bottom {
            return *other;
        }
        if other.is_bottom {
            return *self;
        }
        let mut m = [[INF; DIM]; DIM];
        for i in 0..DIM {
            for j in 0..DIM {
                m[i][j] = self.m[i][j].max(other.m[i][j]);
            }
        }
        Self {
            m,
            is_bottom: false,
        }
    }

    /// Meet (greatest lower bound) of two zones, followed by shortest-path closure.
    pub fn meet(&self, other: &Self) -> Self {
        if self.is_bottom || other.is_bottom {
            return Self::bottom();
        }
        let mut m = [[INF; DIM]; DIM];
        for i in 0..DIM {
            for j in 0..DIM {
                m[i][j] = self.m[i][j].min(other.m[i][j]);
            }
        }
        let mut res = Self {
            m,
            is_bottom: false,
        };
        res.close();
        res
    }

    /// Standard zone widening `self nabla other` (Mine 2001):
    /// Must NOT close `self nabla other` during widening iterations, or termination can fail;
    /// entry-wise `if other.m[i][j] > self.m[i][j] { INF } else { self.m[i][j] }`.
    pub fn widen(&self, other: &Self) -> Self {
        if self.is_bottom {
            return *other;
        }
        if other.is_bottom {
            return *self;
        }
        let mut m = [[INF; DIM]; DIM];
        for i in 0..DIM {
            for j in 0..DIM {
                m[i][j] = if other.m[i][j] > self.m[i][j] {
                    INF
                } else {
                    self.m[i][j]
                };
            }
            m[i][i] = 0;
            m[0][i] = m[0][i].min(0);
        }
        Self {
            m,
            is_bottom: false,
        }
    }

    /// Evaluates whether `v_i < v_j` is guaranteed (`True`), impossible (`False`), or unknown (`Top`).
    pub fn eval_lt(&self, i: usize, j: usize) -> AbstractBool {
        if self.is_bottom || i >= DIM || j >= DIM {
            return AbstractBool::Bottom;
        }
        // v_i - v_j <= -1  =>  v_i < v_j is guaranteed True
        if self.m[i][j] <= -1 {
            AbstractBool::True
        } else if self.m[j][i] <= 0 {
            // v_j - v_i <= 0  =>  v_j <= v_i  =>  v_i < v_j is False
            AbstractBool::False
        } else {
            AbstractBool::Top
        }
    }

    /// Evaluates whether `v_i <= v_j` is guaranteed (`True`), impossible (`False`), or unknown (`Top`).
    pub fn eval_le(&self, i: usize, j: usize) -> AbstractBool {
        if self.is_bottom || i >= DIM || j >= DIM {
            return AbstractBool::Bottom;
        }
        if self.m[i][j] <= 0 {
            AbstractBool::True
        } else if self.m[j][i] <= -1 {
            AbstractBool::False
        } else {
            AbstractBool::Top
        }
    }

    /// Discharges a Lean 4 `Nat` subtraction termination measure `n - next_i < n - i`
    /// given variable indices `n_var`, `i_var`, and `next_i_var`.
    ///
    /// In Lean 4 `Nat` (where subtraction truncates at 0), `n - next_i < n - i` holds iff:
    /// 1. `i < n` (`v_i - v_n <= -1`), and
    /// 2. `i < next_i` (`v_i - v_next <= -1`).
    /// (Note: even if `next_i > n`, `n - next_i = 0 < 1 <= n - i` still holds whenever `i < n`!)
    pub fn check_nat_sub_decreasing(
        &self,
        n_var: usize,
        i_var: usize,
        next_i_var: usize,
    ) -> AbstractBool {
        if self.is_bottom {
            return AbstractBool::Bottom;
        }
        let i_lt_n = self.eval_lt(i_var, n_var);
        let i_lt_next = self.eval_lt(i_var, next_i_var);
        i_lt_n.and(i_lt_next)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zone_closure_and_contradiction() {
        let mut z = NatZoneDomain::top();
        // v1 <= 10, v2 >= 5, v1 < v2 (v1 - v2 <= -1)
        assert!(z.constrain_interval(1, IntervalBound::new(0, 10)));
        assert!(z.constrain_interval(2, IntervalBound::new(5, 20)));
        assert!(z.add_constraint(1, 2, -1));
        assert_eq!(z.eval_lt(1, 2), AbstractBool::True);
        assert_eq!(z.eval_le(2, 1), AbstractBool::False);

        // If we also require v2 <= 3, the zone becomes bottom because v2 >= 5
        assert!(!z.add_constraint(2, 0, 3));
        assert!(z.is_bottom());
    }

    #[test]
    fn test_zone_discharges_lean_decreasing_by_obligation() {
        // Models a recursive loop with fuel `n - i` under guard `i < n` where `i' = i + 1`:
        // v1 = n, v2 = i, v3 = i' = i + 1.
        let mut z = NatZoneDomain::top();
        // Guard: i < n  <=>  v2 - v1 <= -1
        assert!(z.add_constraint(2, 1, -1));
        // Step: i' := i + 1
        assert!(z.assign_var_plus_const(3, 2, 1));

        // Prove termination obligation `n - i' < n - i`:
        assert_eq!(z.check_nat_sub_decreasing(1, 2, 3), AbstractBool::True);
        // Also check transitive bound: i' <= n  (v3 - v1 <= 0)
        assert_eq!(z.eval_le(3, 1), AbstractBool::True);
        // And n >= 1 (since 0 <= i < n)
        let n_iv = z.get_interval(1).expect("reachable");
        assert_eq!(n_iv.min, 1);
    }

    #[test]
    fn test_zone_join_meet_widen_laws() {
        let mut z1 = NatZoneDomain::top();
        z1.constrain_interval(1, IntervalBound::point(0));
        let mut z2 = NatZoneDomain::top();
        z2.constrain_interval(1, IntervalBound::point(1));

        let joined = z1.join(&z2);
        assert_eq!(joined.get_interval(1), Some(IntervalBound::new(0, 1)));

        let widened = z1.widen(&joined);
        assert_eq!(widened.get_interval(1), Some(IntervalBound::new(0, INF)));
    }
}
