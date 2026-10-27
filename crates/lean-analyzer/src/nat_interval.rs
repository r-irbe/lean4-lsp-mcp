//! src/nat_interval.rs
//! Natural-number interval transfer functions (Lean 4 semantics).
//! Convention: `i64::MAX` means +infinity. A bound equal to INF stands for
//! "any value >= i64::MAX". Validated against a Lean-generated oracle table.
//! 

use crate::lattice::{AbstractBool, IntervalBound};

/// +infinity marker for natural-number bounds.
pub const INF: i64 = i64::MAX;

#[inline]
fn clamp_u128(v: u128) -> i64 {
    if v >= INF as u128 {
        INF
    } else {
        v as i64
    }
}

fn sat_pow(x: i64, k: i64) -> i64 {
    if x == 0 {
        return if k == 0 { 1 } else { 0 };
    }
    if x == 1 || k == 0 {
        return 1;
    }
    if x == INF || k >= 63 {
        return INF;
    }
    match x.checked_pow(k as u32) {
        Some(v) => v,
        None => INF,
    }
}

/// Warren's Hacker's Delight (Ch. 4) exact minimum of `x & y` for `x in [a, b]`, `y in [c, d]`.
fn min_and_u64(mut a: u64, b: u64, mut c: u64, d: u64) -> u64 {
    let mut m: u64 = 1u64 << 63;
    while m != 0 {
        if (!a & !c & m) != 0 {
            let mut temp = (a | m) & m.wrapping_neg();
            if temp <= b {
                a = temp;
                break;
            }
            temp = (c | m) & m.wrapping_neg();
            if temp <= d {
                c = temp;
                break;
            }
        }
        m >>= 1;
    }
    a & c
}

/// Warren's Hacker's Delight (Ch. 4) exact maximum of `x & y` for `x in [a, b]`, `y in [c, d]`.
fn max_and_u64(a: u64, mut b: u64, c: u64, mut d: u64) -> u64 {
    let mut m: u64 = 1u64 << 63;
    while m != 0 {
        if (b & !d & m) != 0 {
            let temp = (b & !m) | (m - 1);
            if temp >= a {
                b = temp;
                break;
            }
        } else if (!b & d & m) != 0 {
            let temp = (d & !m) | (m - 1);
            if temp >= c {
                d = temp;
                break;
            }
        }
        m >>= 1;
    }
    b & d
}

/// Warren's Hacker's Delight (Ch. 4) exact minimum of `x | y` for `x in [a, b]`, `y in [c, d]`.
fn min_or_u64(mut a: u64, b: u64, mut c: u64, d: u64) -> u64 {
    let mut m: u64 = 1u64 << 63;
    while m != 0 {
        if (!a & c & m) != 0 {
            let temp = (a | m) & m.wrapping_neg();
            if temp <= b {
                a = temp;
                break;
            }
        } else if (a & !c & m) != 0 {
            let temp = (c | m) & m.wrapping_neg();
            if temp <= d {
                c = temp;
                break;
            }
        }
        m >>= 1;
    }
    a | c
}

/// Warren's Hacker's Delight (Ch. 4) exact maximum of `x | y` for `x in [a, b]`, `y in [c, d]`.
fn max_or_u64(a: u64, mut b: u64, c: u64, mut d: u64) -> u64 {
    let mut m: u64 = 1u64 << 63;
    while m != 0 {
        if (b & d & m) != 0 {
            let mut temp = (b - m) | (m - 1);
            if temp >= a {
                b = temp;
                break;
            }
            temp = (d - m) | (m - 1);
            if temp >= c {
                d = temp;
                break;
            }
        }
        m >>= 1;
    }
    b | d
}

/// Warren's Hacker's Delight (Ch. 4) exact minimum of `x ^ y` for `x in [a, b]`, `y in [c, d]`.
fn min_xor_u64(mut a: u64, mut b: u64, mut c: u64, mut d: u64) -> u64 {
    let mut m: u64 = 1u64 << 63;
    while m != 0 {
        if (!a & c & m) != 0 {
            let temp = (a | m) & m.wrapping_neg();
            if temp <= b {
                a = temp;
            }
        } else if (a & !c & m) != 0 {
            let temp = (c | m) & m.wrapping_neg();
            if temp <= d {
                c = temp;
            }
        }
        if (b & !d & m) != 0 {
            let temp = (b - m) | (m - 1);
            if temp >= a {
                b = temp;
            }
        } else if (!b & d & m) != 0 {
            let temp = (d - m) | (m - 1);
            if temp >= c {
                d = temp;
            }
        }
        m >>= 1;
    }
    (a ^ c).min(b ^ d)
}

/// Warren's Hacker's Delight (Ch. 4) exact maximum of `x ^ y` for `x in [a, b]`, `y in [c, d]`.
fn max_xor_u64(mut a: u64, mut b: u64, mut c: u64, mut d: u64) -> u64 {
    let mut m: u64 = 1u64 << 63;
    while m != 0 {
        if (b & d & m) != 0 {
            let temp = (b - m) | (m - 1);
            if temp >= a {
                b = temp;
            } else {
                let temp2 = (d - m) | (m - 1);
                if temp2 >= c {
                    d = temp2;
                }
            }
        }
        if (!a & !c & m) != 0 {
            let temp = (a | m) & m.wrapping_neg();
            if temp <= b {
                a = temp;
            } else {
                let temp2 = (c | m) & m.wrapping_neg();
                if temp2 <= d {
                    c = temp2;
                }
            }
        }
        m >>= 1;
    }
    (a ^ d).max(b ^ c)
}

impl IntervalBound {
    pub fn nat_succ(&self) -> Self {
        Self::new(self.min.saturating_add(1), self.max.saturating_add(1))
    }

    pub fn nat_pred(&self) -> Self {
        let lo = (self.min - 1).max(0);
        let hi = if self.max == INF { INF } else { (self.max - 1).max(0) };
        Self::new(lo, hi)
    }

    pub fn nat_sub(&self, o: &Self) -> Self {
        let lo = if o.max == INF { 0 } else { (self.min - o.max).max(0) };
        let hi = if self.max == INF { INF } else { (self.max - o.min).max(0) };
        Self::new(lo, hi)
    }

    pub fn nat_div(&self, o: &Self) -> Self {
        if o.max == 0 || self.max == 0 {
            return Self::point(0);
        }
        let lo = if o.min == 0 || o.max == INF { 0 } else { self.min / o.max };
        let hi = if self.max == INF { INF } else { self.max / o.min.max(1) };
        Self::new(lo, hi)
    }

    pub fn nat_mod(&self, o: &Self) -> Self {
        if o.max == 0 {
            return *self;
        }
        if self.max != INF && self.max < o.min {
            return *self;
        }
        // Single quotient bucket with constant divisor: x % k is strictly increasing on [min, max].
        if self.max != INF && o.min == o.max && o.min > 0 && o.max != INF {
            let k = o.min;
            if self.min / k == self.max / k {
                return Self::new(self.min % k, self.max % k);
            }
        }
        let mut hi = self.max;
        if o.min > 0 && o.max != INF {
            hi = hi.min(o.max - 1);
        }
        Self::new(0, hi)
    }

    pub fn nat_min(&self, o: &Self) -> Self {
        Self::new(self.min.min(o.min), self.max.min(o.max))
    }

    pub fn nat_max(&self, o: &Self) -> Self {
        Self::new(self.min.max(o.min), self.max.max(o.max))
    }

    pub fn nat_pow(&self, o: &Self) -> Self {
        if o.max == 0 {
            return Self::point(1);
        }
        let mut lo = i64::MAX;
        let mut hi = 0;
        for &x in &[self.min, self.max] {
            for &k in &[o.min, o.max] {
                let v = sat_pow(x, k);
                lo = lo.min(v);
                hi = hi.max(v);
            }
        }
        if self.min == 0 && o.max >= 1 {
            lo = 0;
        }
        if self.min <= 1 && self.max >= 1 {
            lo = lo.min(1);
        }
        Self::new(lo, hi)
    }

    pub fn nat_land(&self, o: &Self) -> Self {
        if self.max != INF && o.max != INF {
            let a = self.min.max(0) as u64;
            let b = self.max.max(0) as u64;
            let c = o.min.max(0) as u64;
            let d = o.max.max(0) as u64;
            let lo = clamp_u128(min_and_u64(a, b, c, d) as u128);
            let hi = clamp_u128(max_and_u64(a, b, c, d) as u128);
            return Self::new(lo, hi);
        }
        Self::new(0, self.max.min(o.max))
    }

    pub fn nat_lor(&self, o: &Self) -> Self {
        if self.max != INF && o.max != INF {
            let a = self.min.max(0) as u64;
            let b = self.max.max(0) as u64;
            let c = o.min.max(0) as u64;
            let d = o.max.max(0) as u64;
            let lo = clamp_u128(min_or_u64(a, b, c, d) as u128);
            let hi = clamp_u128(max_or_u64(a, b, c, d) as u128);
            return Self::new(lo, hi);
        }
        Self::new(self.min.max(o.min), INF)
    }

    pub fn nat_xor(&self, o: &Self) -> Self {
        if self.max != INF && o.max != INF {
            let a = self.min.max(0) as u64;
            let b = self.max.max(0) as u64;
            let c = o.min.max(0) as u64;
            let d = o.max.max(0) as u64;
            let lo = clamp_u128(min_xor_u64(a, b, c, d) as u128);
            let hi = clamp_u128(max_xor_u64(a, b, c, d) as u128);
            return Self::new(lo, hi);
        }
        Self::new(0, INF)
    }

    pub fn nat_shl(&self, o: &Self) -> Self {
        let lo = if self.min == 0 {
            0
        } else if o.min >= 64 {
            INF
        } else {
            clamp_u128((self.min as u128) << o.min)
        };
        let hi = if self.max == 0 {
            0
        } else if self.max == INF || o.max >= 64 {
            INF
        } else {
            clamp_u128((self.max as u128) << o.max)
        };
        Self::new(lo, hi)
    }

    pub fn nat_shr(&self, o: &Self) -> Self {
        let lo = if o.max >= 64 { 0 } else { self.min >> o.max };
        let hi = if self.max == INF {
            INF
        } else if o.min >= 64 {
            0
        } else {
            self.max >> o.min
        };
        Self::new(lo, hi)
    }

    pub fn ble(&self, o: &Self) -> AbstractBool {
        if self.max != INF && self.max <= o.min {
            AbstractBool::True
        } else if o.max != INF && self.min > o.max {
            AbstractBool::False
        } else {
            AbstractBool::Top
        }
    }

    pub fn blt(&self, o: &Self) -> AbstractBool {
        if self.max != INF && self.max < o.min {
            AbstractBool::True
        } else if o.max != INF && self.min >= o.max {
            AbstractBool::False
        } else {
            AbstractBool::Top
        }
    }

    pub fn bge(&self, o: &Self) -> AbstractBool {
        o.ble(self)
    }

    pub fn bgt(&self, o: &Self) -> AbstractBool {
        o.blt(self)
    }

    pub fn beq(&self, o: &Self) -> AbstractBool {
        let finite = self.max != INF && o.max != INF;
        if finite && self.min == self.max && o.min == o.max && self.min == o.min {
            AbstractBool::True
        } else if (self.max != INF && self.max < o.min) || (o.max != INF && o.max < self.min) {
            AbstractBool::False
        } else {
            AbstractBool::Top
        }
    }

    pub fn bne(&self, o: &Self) -> AbstractBool {
        self.beq(o).not()
    }
}
