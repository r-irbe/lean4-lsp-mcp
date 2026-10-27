//! src/affine.rs
//! Karr-Style Affine Conservation & Two-Variable Weighted Linear Bounds over `Nat`
//! (Karr 1976 "Affine Relationships Among Variables of a Program";
//! Cousot 2021 Ch. 42 & 52; Pelleau 2015 Ch. 2; Simon 2008 Ch. 8).
//!
//! Specifically supports:
//! - $\times 100$ scaled-integer simplex conservation laws $\sum w_i x_i = 100$
//! - Two-variable weighted linear bounds $a x + b y \in [L, U]$ with positive integer weights
//!   $a, b > 0$ over natural-number intervals $x \in [x_{\min}, x_{\max}]$, $y \in [y_{\min}, y_{\max}]$.
//!
//! Tightening rules for $a x + b y \in [L, U]$ ($a, b > 0$, $x, y \ge 0$):
//! - Upper bound on $x$: $x_{\max}' = \min\bigl(x_{\max}, \lfloor (U - b y_{\min}) / a \rfloor\bigr)$
//! - Lower bound on $x$: $x_{\min}' = \max\bigl(x_{\min}, \lceil \max(0, L - b y_{\max}) / a \rceil\bigr)$
//! - Symmetrically for $y$:
//!   $y_{\max}' = \min\bigl(y_{\max}, \lfloor (U - a x_{\min}) / b \rfloor\bigr)$
//!   $y_{\min}' = \max\bigl(y_{\min}, \lceil \max(0, L - a x_{\max}) / b \rceil\bigr)$
//! - Iterated to a fixed point (at most 2 passes for 2 variables) and checked for feasibility:
//!   $\max(L, a x_{\min}' + b y_{\min}') \le \min(U, a x_{\max}' + b y_{\max}')$.

use crate::lattice::{AbstractBool, IntervalBound};
use crate::nat_interval::INF;

/// Maximum number of variables in a bounded Karr/simplex affine conservation constraint.
pub const MAX_AFFINE_VARS: usize = 8;

#[inline]
fn ceil_div_nonneg(num: i128, den: i128) -> i128 {
    if num <= 0 || den <= 0 {
        0
    } else {
        (num + den - 1) / den
    }
}

#[inline]
fn clamp_i64(val: i128) -> i64 {
    if val >= INF as i128 {
        INF
    } else if val <= 0 {
        0
    } else {
        val as i64
    }
}

/// Two-variable weighted linear interval propagation over `Nat`:
/// Given $a x + b y \in [L, U]$ with $a, b > 0$ and initial bounds
/// $x \in [x_{\min}, x_{\max}]$, $y \in [y_{\min}, y_{\max}]$, returns the tightened
/// intervals `Some((x_iv', y_iv'))` or `None` if the linear constraint is infeasible (`Bottom`).
pub fn reduce_weighted_linear_two_vars(
    a: i64,
    b: i64,
    sum_min: i64,
    sum_max: i64,
    x_iv: IntervalBound,
    y_iv: IntervalBound,
) -> Option<(IntervalBound, IntervalBound)> {
    if a <= 0 || b <= 0 {
        return None;
    }
    if x_iv.min > x_iv.max || x_iv.max < 0 || y_iv.min > y_iv.max || y_iv.max < 0 {
        return None;
    }
    let l = sum_min.max(0) as i128;
    let u_is_inf = sum_max >= INF;
    let u = sum_max as i128;
    if !u_is_inf && l > u {
        return None;
    }

    let a128 = a as i128;
    let b128 = b as i128;

    let mut x_lo = x_iv.min.max(0) as i128;
    let mut x_hi_inf = x_iv.max >= INF;
    let mut x_hi = x_iv.max as i128;

    let mut y_lo = y_iv.min.max(0) as i128;
    let mut y_hi_inf = y_iv.max >= INF;
    let mut y_hi = y_iv.max as i128;

    for _ in 0..3 {
        // 1. Tighten x_hi <= floor((U - b * y_lo) / a)
        if !u_is_inf {
            let rem_u = u - b128 * y_lo;
            if rem_u < 0 {
                return None;
            }
            let bound_x_hi = rem_u / a128;
            if x_hi_inf || bound_x_hi < x_hi {
                x_hi = bound_x_hi;
                x_hi_inf = false;
            }
        }

        // 2. Tighten x_lo >= ceil(max(0, L - b * y_hi) / a)
        if !y_hi_inf && l > 0 {
            let rem_l = (l - b128 * y_hi).max(0);
            let bound_x_lo = ceil_div_nonneg(rem_l, a128);
            if bound_x_lo > x_lo {
                x_lo = bound_x_lo;
            }
        }

        if !x_hi_inf && x_lo > x_hi {
            return None;
        }

        // 3. Tighten y_hi <= floor((U - a * x_lo) / b)
        if !u_is_inf {
            let rem_u = u - a128 * x_lo;
            if rem_u < 0 {
                return None;
            }
            let bound_y_hi = rem_u / b128;
            if y_hi_inf || bound_y_hi < y_hi {
                y_hi = bound_y_hi;
                y_hi_inf = false;
            }
        }

        // 4. Tighten y_lo >= ceil(max(0, L - a * x_hi) / b)
        if !x_hi_inf && l > 0 {
            let rem_l = (l - a128 * x_hi).max(0);
            let bound_y_lo = ceil_div_nonneg(rem_l, b128);
            if bound_y_lo > y_lo {
                y_lo = bound_y_lo;
            }
        }

        if !y_hi_inf && y_lo > y_hi {
            return None;
        }
    }

    // Final feasibility check on achieved weighted sum interval:
    let min_possible = a128 * x_lo + b128 * y_lo;
    if !u_is_inf && min_possible > u {
        return None;
    }
    if !x_hi_inf && !y_hi_inf {
        let max_possible = a128 * x_hi + b128 * y_hi;
        if max_possible < l {
            return None;
        }
    }

    let out_x = IntervalBound::new(
        clamp_i64(x_lo),
        if x_hi_inf { INF } else { clamp_i64(x_hi) },
    );
    let out_y = IntervalBound::new(
        clamp_i64(y_lo),
        if y_hi_inf { INF } else { clamp_i64(y_hi) },
    );
    Some((out_x, out_y))
}

/// Karr-style affine conservation & weighted simplex domain over up to `MAX_AFFINE_VARS` `Nat` variables:
/// $\sum_{i=0}^{n-1} w_i x_i \in [\text{sum\_min}, \text{sum\_max}]$.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NatAffineConservation {
    pub arity: usize,
    pub weights: [i64; MAX_AFFINE_VARS],
    pub intervals: [IntervalBound; MAX_AFFINE_VARS],
    pub sum_min: i64,
    pub sum_max: i64,
    pub is_bottom: bool,
}

impl NatAffineConservation {
    /// Creates a weighted affine conservation domain $\sum_{i=0}^{k-1} w_i x_i \in [\text{sum\_min}, \text{sum\_max}]$.
    pub fn new(weights: &[i64], sum_min: i64, sum_max: i64) -> Self {
        let arity = weights.len().min(MAX_AFFINE_VARS);
        let mut w_arr = [0i64; MAX_AFFINE_VARS];
        let mut iv_arr = [IntervalBound::new(0, INF); MAX_AFFINE_VARS];
        let mut invalid = sum_min > sum_max || sum_max < 0;
        for i in 0..arity {
            if weights[i] <= 0 {
                invalid = true;
            }
            w_arr[i] = weights[i];
            iv_arr[i] = IntervalBound::new(0, INF);
        }
        let mut dom = Self {
            arity,
            weights: w_arr,
            intervals: iv_arr,
            sum_min: sum_min.max(0),
            sum_max,
            is_bottom: invalid,
        };
        if !dom.is_bottom {
            dom.propagate();
        }
        dom
    }

    /// Creates a standard $\times 100$ scaled-integer simplex conservation law $\sum_{i=0}^{k-1} x_i = 100$.
    pub fn simplex_100(arity: usize) -> Self {
        let k = arity.min(MAX_AFFINE_VARS);
        let weights = [1i64; MAX_AFFINE_VARS];
        Self::new(&weights[..k], 100, 100)
    }

    /// Refines the interval of variable `idx` and propagates weighted affine bounds across all variables.
    pub fn set_interval(&mut self, idx: usize, iv: IntervalBound) -> bool {
        if self.is_bottom || idx >= self.arity {
            return !self.is_bottom;
        }
        let lo = self.intervals[idx].min.max(iv.min).max(0);
        let hi = self.intervals[idx].max.min(iv.max);
        if lo > hi || hi < 0 {
            self.is_bottom = true;
            return false;
        }
        self.intervals[idx] = IntervalBound::new(lo, hi);
        self.propagate()
    }

    /// Runs Karr-style weighted interval propagation across all active variables.
    /// Returns `false` if the conservation law becomes infeasible (`is_bottom = true`).
    pub fn propagate(&mut self) -> bool {
        if self.is_bottom {
            return false;
        }
        if self.arity == 0 {
            if self.sum_min > 0 {
                self.is_bottom = true;
                return false;
            }
            return true;
        }
        if self.arity == 2 {
            match reduce_weighted_linear_two_vars(
                self.weights[0],
                self.weights[1],
                self.sum_min,
                self.sum_max,
                self.intervals[0],
                self.intervals[1],
            ) {
                Some((iv0, iv1)) => {
                    self.intervals[0] = iv0;
                    self.intervals[1] = iv1;
                    return true;
                }
                None => {
                    self.is_bottom = true;
                    return false;
                }
            }
        }

        let l = self.sum_min.max(0) as i128;
        let u_is_inf = self.sum_max >= INF;
        let u = self.sum_max as i128;

        for _pass in 0..3 {
            for i in 0..self.arity {
                let wi = self.weights[i] as i128;
                if wi <= 0 {
                    self.is_bottom = true;
                    return false;
                }
                let mut other_min_sum: i128 = 0;
                let mut other_max_sum: i128 = 0;
                let mut other_max_inf = false;

                for j in 0..self.arity {
                    if i == j {
                        continue;
                    }
                    let wj = self.weights[j] as i128;
                    let ivj = self.intervals[j];
                    other_min_sum += wj * (ivj.min.max(0) as i128);
                    if ivj.max >= INF {
                        other_max_inf = true;
                    } else if !other_max_inf {
                        other_max_sum += wj * (ivj.max as i128);
                    }
                }

                let mut xi_lo = self.intervals[i].min.max(0) as i128;
                let mut xi_hi_inf = self.intervals[i].max >= INF;
                let mut xi_hi = self.intervals[i].max as i128;

                if !u_is_inf {
                    let rem_u = u - other_min_sum;
                    if rem_u < 0 {
                        self.is_bottom = true;
                        return false;
                    }
                    let bound_hi = rem_u / wi;
                    if xi_hi_inf || bound_hi < xi_hi {
                        xi_hi = bound_hi;
                        xi_hi_inf = false;
                    }
                }

                if !other_max_inf && l > 0 {
                    let rem_l = (l - other_max_sum).max(0);
                    let bound_lo = ceil_div_nonneg(rem_l, wi);
                    if bound_lo > xi_lo {
                        xi_lo = bound_lo;
                    }
                }

                if !xi_hi_inf && xi_lo > xi_hi {
                    self.is_bottom = true;
                    return false;
                }

                self.intervals[i] = IntervalBound::new(
                    clamp_i64(xi_lo),
                    if xi_hi_inf { INF } else { clamp_i64(xi_hi) },
                );
            }
        }

        let mut total_min: i128 = 0;
        let mut total_max: i128 = 0;
        let mut total_max_inf = false;
        for i in 0..self.arity {
            let wi = self.weights[i] as i128;
            total_min += wi * (self.intervals[i].min.max(0) as i128);
            if self.intervals[i].max >= INF {
                total_max_inf = true;
            } else if !total_max_inf {
                total_max += wi * (self.intervals[i].max as i128);
            }
        }
        if (!u_is_inf && total_min > u) || (!total_max_inf && total_max < l) {
            self.is_bottom = true;
            return false;
        }
        true
    }

    /// Checks whether a weighted upper bound $a x_i + b x_j \le c$ is certified by the current domain.
    pub fn check_weighted_pair_le(
        &self,
        i: usize,
        a: i64,
        j: usize,
        b: i64,
        cap: i64,
    ) -> AbstractBool {
        if self.is_bottom || i >= self.arity || j >= self.arity || a < 0 || b < 0 {
            return AbstractBool::Bottom;
        }
        let iv_i = self.intervals[i];
        let iv_j = self.intervals[j];
        let min_val = (a as i128) * (iv_i.min.max(0) as i128) + (b as i128) * (iv_j.min.max(0) as i128);
        if min_val > (cap as i128) {
            return AbstractBool::False;
        }
        if iv_i.max < INF && iv_j.max < INF {
            let max_val = (a as i128) * (iv_i.max as i128) + (b as i128) * (iv_j.max as i128);
            if max_val <= (cap as i128) {
                return AbstractBool::True;
            }
        }
        if i != j && a == self.weights[i] && b == self.weights[j] && self.sum_max <= cap {
            return AbstractBool::True;
        }
        AbstractBool::Top
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_weighted_linear_two_vars_floor_and_ceil_tightening() {
        // 2 * x + 3 * y == 100, with x in [10, 100], y in [0, 100]
        // y_min = 0 => x_max <= floor((100 - 0) / 2) = 50
        // x_min = 10 => y_max <= floor((100 - 20) / 3) = 26
        // With y_max = 26 => x_min >= ceil((100 - 3 * 26) / 2) = ceil(22 / 2) = 11!
        let (rx, ry) = reduce_weighted_linear_two_vars(
            2,
            3,
            100,
            100,
            IntervalBound::new(10, 100),
            IntervalBound::new(0, 100),
        )
        .expect("feasible weighted simplex");
        assert_eq!(rx, IntervalBound::new(11, 50));
        assert_eq!(ry, IntervalBound::new(0, 26));
    }

    #[test]
    fn test_weighted_linear_infeasible_returns_none() {
        // 4 * x + 5 * y <= 30 with x >= 5, y >= 3 => min sum = 20 + 15 = 35 > 30
        let res = reduce_weighted_linear_two_vars(
            4,
            5,
            0,
            30,
            IntervalBound::new(5, 20),
            IntervalBound::new(3, 20),
        );
        assert!(res.is_none());
    }

    #[test]
    fn test_nat_affine_conservation_simplex_100_three_vars() {
        // x0 + x1 + x2 == 100 with x0 in [40, 60], x1 in [35, 50] => x2 in [0, 25] and x2 >= 100 - 110 = 0
        // If x0 in [40, 45] and x1 in [35, 40], then x0 + x1 in [75, 85], so x2 in [15, 25]!
        let mut dom = NatAffineConservation::simplex_100(3);
        assert!(dom.set_interval(0, IntervalBound::new(40, 45)));
        assert!(dom.set_interval(1, IntervalBound::new(35, 40)));
        assert_eq!(dom.intervals[2], IntervalBound::new(15, 25));
        assert_eq!(dom.check_weighted_pair_le(0, 1, 1, 1, 85), AbstractBool::True);
        assert_eq!(dom.check_weighted_pair_le(0, 1, 1, 1, 70), AbstractBool::False);
    }
}
