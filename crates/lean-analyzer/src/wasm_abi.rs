//! src/wasm_abi.rs
//! Zero-overhead C and WebAssembly FFI bindings for lean-analyzer.
//! 

use crate::lattice::{AbstractBool, AbstractSign, IntervalBound};

#[no_mangle]
pub extern "C" fn lean_analyzer_version() -> u32 {
    100 // Version 1.0.0
}

/// Bitset Join (Least Upper Bound) across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_join_signs(a: u8, b: u8) -> u8 {
    let sign_a = AbstractSign::from_u8(a);
    let sign_b = AbstractSign::from_u8(b);
    sign_a.join(sign_b).as_u8()
}

/// Bitset Meet (Greatest Lower Bound) across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_meet_signs(a: u8, b: u8) -> u8 {
    let sign_a = AbstractSign::from_u8(a);
    let sign_b = AbstractSign::from_u8(b);
    sign_a.meet(sign_b).as_u8()
}

/// Interval addition across WASM boundary.
/// Writes [out_min, out_max] into out_buf (must hold at least 2 i64s = 16 bytes).
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_add(
    min1: i64,
    max1: i64,
    min2: i64,
    max2: i64,
    out_buf: *mut i64,
) -> u8 {
    if out_buf.is_null() {
        return 0;
    }
    let i1 = IntervalBound::new(min1, max1);
    let i2 = IntervalBound::new(min2, max2);
    let res = i1.add(&i2);

    unsafe {
        *out_buf = res.min;
        *out_buf.add(1) = res.max;
    }
    1
}

/// Saturated natural subtraction across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_sub(
    min1: i64,
    max1: i64,
    min2: i64,
    max2: i64,
    out_buf: *mut i64,
) -> u8 {
    if out_buf.is_null() {
        return 0;
    }
    let i1 = IntervalBound::new(min1, max1);
    let i2 = IntervalBound::new(min2, max2);
    let res = i1.nat_sub(&i2);

    unsafe {
        *out_buf = res.min;
        *out_buf.add(1) = res.max;
    }
    1
}

/// Interval multiplication across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_mul(
    min1: i64,
    max1: i64,
    min2: i64,
    max2: i64,
    out_buf: *mut i64,
) -> u8 {
    if out_buf.is_null() {
        return 0;
    }
    let i1 = IntervalBound::new(min1, max1);
    let i2 = IntervalBound::new(min2, max2);
    let res = i1.mul(&i2);

    unsafe {
        *out_buf = res.min;
        *out_buf.add(1) = res.max;
    }
    1
}

/// Interval exponentiation across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_pow(
    min1: i64,
    max1: i64,
    min2: i64,
    max2: i64,
    out_buf: *mut i64,
) -> u8 {
    if out_buf.is_null() {
        return 0;
    }
    let i1 = IntervalBound::new(min1, max1);
    let i2 = IntervalBound::new(min2, max2);
    let res = i1.nat_pow(&i2);

    unsafe {
        *out_buf = res.min;
        *out_buf.add(1) = res.max;
    }
    1
}

/// Interval min and max evaluation across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_min_max(
    min1: i64,
    max1: i64,
    min2: i64,
    max2: i64,
    out_min_buf: *mut i64,
    out_max_buf: *mut i64,
) -> u8 {
    let i1 = IntervalBound::new(min1, max1);
    let i2 = IntervalBound::new(min2, max2);
    let r_min = i1.nat_min(&i2);
    let r_max = i1.nat_max(&i2);

    unsafe {
        if !out_min_buf.is_null() {
            *out_min_buf = r_min.min;
            *out_min_buf.add(1) = r_min.max;
        }
        if !out_max_buf.is_null() {
            *out_max_buf = r_max.min;
            *out_max_buf.add(1) = r_max.max;
        }
    }
    1
}

/// Parallel join of two 16-slot packed vectors in 1 CPU cycle across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_packed_join(v1: u64, v2: u64) -> u64 {
    v1 | v2
}

/// Parallel meet of two 16-slot packed vectors in 1 CPU cycle across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_packed_meet(v1: u64, v2: u64) -> u64 {
    v1 & v2
}

/// Parse an .ilean JSON buffer in WASM.
/// Returns 1 on success, 0 on failure.
#[no_mangle]
pub extern "C" fn lean_analyzer_parse_ilean_meta(
    ptr: *const u8,
    len: usize,
    out_version: *mut u32,
    out_decls_count: *mut u32,
    out_imports_count: *mut u32,
    out_refs_count: *mut u32,
) -> u8 {
    if ptr.is_null() || len == 0 {
        return 0;
    }
    let slice = unsafe { std::slice::from_raw_parts(ptr, len) };
    let mut parser = crate::ilean_parser::ILeanParser::new(slice);
    if let Some(summary) = parser.parse() {
        unsafe {
            if !out_version.is_null() {
                *out_version = summary.version;
            }
            if !out_decls_count.is_null() {
                *out_decls_count = summary.decls.len() as u32;
            }
            if !out_imports_count.is_null() {
                *out_imports_count = summary.direct_imports.len() as u32;
            }
            if !out_refs_count.is_null() {
                *out_refs_count = summary.references_count as u32;
            }
        }
        1
    } else {
        0
    }
}

/// Instant lookup: finds the declaration at (line, col) in an .ilean buffer.
/// Writes declaration name into out_name_buf (up to max_buf_len bytes).
/// Returns written length, or 0 if not found.
#[no_mangle]
pub extern "C" fn lean_analyzer_find_decl_at(
    ptr: *const u8,
    len: usize,
    line: u32,
    col: u32,
    out_name_buf: *mut u8,
    max_buf_len: usize,
) -> u32 {
    if ptr.is_null() || len == 0 || out_name_buf.is_null() || max_buf_len == 0 {
        return 0;
    }
    let slice = unsafe { std::slice::from_raw_parts(ptr, len) };
    let mut parser = crate::ilean_parser::ILeanParser::new(slice);
    if let Some(summary) = parser.parse() {
        if let Some(decl) = crate::ilean_parser::ILeanParser::find_decl_at(&summary, line, col) {
            let name_bytes = decl.name.as_bytes();
            let write_len = name_bytes.len().min(max_buf_len);
            unsafe {
                std::ptr::copy_nonoverlapping(name_bytes.as_ptr(), out_name_buf, write_len);
            }
            return write_len as u32;
        }
    }
    0
}

static mut WASM_SCRATCH_BUF: [u8; 1024 * 1024] = [0u8; 1024 * 1024];

/// Returns pointer to 1MB internal scratch buffer in WASM linear memory.
#[no_mangle]
pub extern "C" fn lean_analyzer_get_scratch_ptr() -> *mut u8 {
    core::ptr::addr_of_mut!(WASM_SCRATCH_BUF) as *mut u8
}

/// Returns capacity of internal scratch buffer (1MB = 1048576 bytes).
#[no_mangle]
pub extern "C" fn lean_analyzer_get_scratch_len() -> usize {
    1024 * 1024
}

/// Interval division across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_div(
    min1: i64,
    max1: i64,
    min2: i64,
    max2: i64,
    out_buf: *mut i64,
) -> u8 {
    if out_buf.is_null() {
        return 0;
    }
    let i1 = IntervalBound::new(min1, max1);
    let i2 = IntervalBound::new(min2, max2);
    let res = i1.nat_div(&i2);

    unsafe {
        *out_buf = res.min;
        *out_buf.add(1) = res.max;
    }
    1
}

/// Interval modulo across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_mod(
    min1: i64,
    max1: i64,
    min2: i64,
    max2: i64,
    out_buf: *mut i64,
) -> u8 {
    if out_buf.is_null() {
        return 0;
    }
    let i1 = IntervalBound::new(min1, max1);
    let i2 = IntervalBound::new(min2, max2);
    let res = i1.nat_mod(&i2);

    unsafe {
        *out_buf = res.min;
        *out_buf.add(1) = res.max;
    }
    1
}

/// Relational <= comparison across WASM boundary.
/// Returns AbstractBool as u8: Bottom=0, False=1, True=2, Top=3.
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_ble(min1: i64, max1: i64, min2: i64, max2: i64) -> u8 {
    let i1 = IntervalBound::new(min1, max1);
    let i2 = IntervalBound::new(min2, max2);
    i1.ble(&i2).as_u8()
}

/// Relational < comparison across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_blt(min1: i64, max1: i64, min2: i64, max2: i64) -> u8 {
    let i1 = IntervalBound::new(min1, max1);
    let i2 = IntervalBound::new(min2, max2);
    i1.blt(&i2).as_u8()
}

/// Relational == comparison across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_beq(min1: i64, max1: i64, min2: i64, max2: i64) -> u8 {
    let i1 = IntervalBound::new(min1, max1);
    let i2 = IntervalBound::new(min2, max2);
    i1.beq(&i2).as_u8()
}

/// Abstract boolean join across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_join_bools(a: u8, b: u8) -> u8 {
    let b_a = AbstractBool::from_u8(a);
    let b_b = AbstractBool::from_u8(b);
    b_a.join(b_b).as_u8()
}

/// Abstract boolean meet across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_meet_bools(a: u8, b: u8) -> u8 {
    let b_a = AbstractBool::from_u8(a);
    let b_b = AbstractBool::from_u8(b);
    b_a.meet(b_b).as_u8()
}

/// Abstract boolean NOT across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_bool_not(a: u8) -> u8 {
    let b = AbstractBool::from_u8(a);
    b.not().as_u8()
}

/// Abstract boolean AND across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_bool_and(a: u8, b: u8) -> u8 {
    let b_a = AbstractBool::from_u8(a);
    let b_b = AbstractBool::from_u8(b);
    b_a.and(b_b).as_u8()
}

/// Abstract boolean OR across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_bool_or(a: u8, b: u8) -> u8 {
    let b_a = AbstractBool::from_u8(a);
    let b_b = AbstractBool::from_u8(b);
    b_a.or(b_b).as_u8()
}

/// Abstract interval widening operator across WASM boundary: packed (min << 32) | (max & 0xFFFFFFFF)
#[no_mangle]
pub extern "C" fn lean_analyzer_widen_interval(min1: i64, max1: i64, min2: i64, max2: i64, out_max: *mut i64) -> i64 {
    let i1 = IntervalBound::new(min1, max1);
    let i2 = IntervalBound::new(min2, max2);
    let res = i1.widen(&i2);
    if !out_max.is_null() {
        unsafe { *out_max = res.max; }
    }
    res.min
}

/// Abstract interval narrowing operator across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_narrow_interval(min1: i64, max1: i64, min2: i64, max2: i64, out_max: *mut i64) -> i64 {
    let i1 = IntervalBound::new(min1, max1);
    let i2 = IntervalBound::new(min2, max2);
    let res = i1.narrow(&i2);
    if !out_max.is_null() {
        unsafe { *out_max = res.max; }
    }
    res.min
}

/// Threshold interval widening operator across WASM boundary.
/// Reads `thresholds_len` i64 values from `thresholds_ptr` and writes `[min, max]` into `out_buf`.
#[no_mangle]
pub extern "C" fn lean_analyzer_widen_with_thresholds(
    min1: i64,
    max1: i64,
    min2: i64,
    max2: i64,
    thresholds_ptr: *const i64,
    thresholds_len: usize,
    out_buf: *mut i64,
) -> u8 {
    if out_buf.is_null() {
        return 0;
    }
    let thresholds: &[i64] = if thresholds_ptr.is_null() || thresholds_len == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(thresholds_ptr, thresholds_len) }
    };
    let i1 = IntervalBound::new(min1, max1);
    let i2 = IntervalBound::new(min2, max2);
    let res = i1.widen_with_thresholds(&i2, thresholds);
    unsafe {
        *out_buf = res.min;
        *out_buf.add(1) = res.max;
    }
    1
}

/// Indexes an in-memory .ilean buffer and returns the number of declarations found.
#[no_mangle]
pub extern "C" fn lean_analyzer_batch_scan_buffer(ptr: *const u8, len: usize) -> u32 {
    if ptr.is_null() || len == 0 {
        return 0;
    }
    let slice = unsafe { std::slice::from_raw_parts(ptr, len) };
    let mut parser = crate::ilean_parser::ILeanParser::new(slice);
    if let Some(summary) = parser.parse() {
        summary.decls.len() as u32
    } else {
        0
    }
}

/// Bitwise AND interval evaluation across WASM boundary (Warren Ch. 4).
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_land(
    min1: i64,
    max1: i64,
    min2: i64,
    max2: i64,
    out_buf: *mut i64,
) -> u8 {
    if out_buf.is_null() {
        return 0;
    }
    let res = IntervalBound::new(min1, max1).nat_land(&IntervalBound::new(min2, max2));
    unsafe {
        *out_buf = res.min;
        *out_buf.add(1) = res.max;
    }
    1
}

/// Bitwise OR interval evaluation across WASM boundary (Warren Ch. 4).
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_lor(
    min1: i64,
    max1: i64,
    min2: i64,
    max2: i64,
    out_buf: *mut i64,
) -> u8 {
    if out_buf.is_null() {
        return 0;
    }
    let res = IntervalBound::new(min1, max1).nat_lor(&IntervalBound::new(min2, max2));
    unsafe {
        *out_buf = res.min;
        *out_buf.add(1) = res.max;
    }
    1
}

/// Bitwise XOR interval evaluation across WASM boundary (Warren Ch. 4).
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_xor(
    min1: i64,
    max1: i64,
    min2: i64,
    max2: i64,
    out_buf: *mut i64,
) -> u8 {
    if out_buf.is_null() {
        return 0;
    }
    let res = IntervalBound::new(min1, max1).nat_xor(&IntervalBound::new(min2, max2));
    unsafe {
        *out_buf = res.min;
        *out_buf.add(1) = res.max;
    }
    1
}

/// Bitwise shift-left interval evaluation across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_shl(
    min1: i64,
    max1: i64,
    min2: i64,
    max2: i64,
    out_buf: *mut i64,
) -> u8 {
    if out_buf.is_null() {
        return 0;
    }
    let res = IntervalBound::new(min1, max1).nat_shl(&IntervalBound::new(min2, max2));
    unsafe {
        *out_buf = res.min;
        *out_buf.add(1) = res.max;
    }
    1
}

/// Bitwise shift-right interval evaluation across WASM boundary.
#[no_mangle]
pub extern "C" fn lean_analyzer_eval_nat_shr(
    min1: i64,
    max1: i64,
    min2: i64,
    max2: i64,
    out_buf: *mut i64,
) -> u8 {
    if out_buf.is_null() {
        return 0;
    }
    let res = IntervalBound::new(min1, max1).nat_shr(&IntervalBound::new(min2, max2));
    unsafe {
        *out_buf = res.min;
        *out_buf.add(1) = res.max;
    }
    1
}

/// Mutual Granger reduction of interval `[min, max]` against congruence `offset (mod stride)`.
/// Writes `[tight_min, tight_max, tight_stride, tight_offset]` into `out_buf` (4 x i64) and returns 1,
/// or returns 0 if the intersection is empty (Bottom) or `out_buf` is null.
#[no_mangle]
pub extern "C" fn lean_analyzer_reduce_interval_congruence(
    min: i64,
    max: i64,
    stride: u64,
    offset: u64,
    out_buf: *mut i64,
) -> u8 {
    if out_buf.is_null() {
        return 0;
    }
    let iv = IntervalBound::new(min, max);
    let cg = crate::congruence::NatCongruence::new(stride, offset);
    match crate::congruence::reduce_interval_congruence(iv, cg) {
        Some((r_iv, crate::congruence::NatCongruence::Class { stride: s, offset: o })) => {
            unsafe {
                *out_buf = r_iv.min;
                *out_buf.add(1) = r_iv.max;
                *out_buf.add(2) = s as i64;
                *out_buf.add(3) = o as i64;
            }
            1
        }
        _ => 0,
    }
}

/// Checks whether the termination measure `n - (i + step) < n - i` is guaranteed in a Zone
/// under guard `i - n <= guard_diff` (e.g. `guard_diff = -1` for `i < n`) and `step` (`i' = i + step`).
/// Returns `AbstractBool` as `u8` (`Bottom=0, False=1, True=2, Top=3`).
#[no_mangle]
pub extern "C" fn lean_analyzer_zone_check_sub_decreasing(
    guard_i_minus_n_ub: i64,
    step: i64,
) -> u8 {
    let mut z = crate::zone::NatZoneDomain::top();
    if !z.add_constraint(2, 1, guard_i_minus_n_ub) {
        return AbstractBool::Bottom.as_u8();
    }
    if !z.assign_var_plus_const(3, 2, step) {
        return AbstractBool::Bottom.as_u8();
    }
    z.check_nat_sub_decreasing(1, 2, 3).as_u8()
}

/// Octagon two-variable relational reduction (`v0 in [min0, max0]`, `v1 in [min1, max1]`,
/// `sum_lo <= v0 + v1 <= sum_hi`, `v0 - v1 <= diff_hi`).
/// Writes `[min0', max0', min1', max1']` into `out_buf` (4 `i64` elements) and returns `1`,
/// or returns `0` if the octagon is infeasible (`Bottom`).
#[no_mangle]
pub extern "C" fn lean_analyzer_octagon_reduce_two_vars(
    min0: i64,
    max0: i64,
    min1: i64,
    max1: i64,
    sum_lo: i64,
    sum_hi: i64,
    diff_hi: i64,
    out_buf: *mut i64,
) -> u8 {
    if out_buf.is_null() {
        return 0;
    }
    let mut oct = crate::octagon::NatOctagonDomain::top();
    if !oct.set_interval(0, IntervalBound::new(min0, max0)) {
        return 0;
    }
    if !oct.set_interval(1, IntervalBound::new(min1, max1)) {
        return 0;
    }
    if sum_lo > 0 && !oct.add_sum_ge(0, 1, sum_lo) {
        return 0;
    }
    if sum_hi < crate::nat_interval::INF && !oct.add_sum_le(0, 1, sum_hi) {
        return 0;
    }
    if diff_hi < crate::nat_interval::INF && !oct.add_diff_le(0, 1, diff_hi) {
        return 0;
    }
    match (oct.get_interval(0), oct.get_interval(1)) {
        (Some(iv0), Some(iv1)) => {
            unsafe {
                *out_buf = iv0.min;
                *out_buf.add(1) = iv0.max;
                *out_buf.add(2) = iv1.min;
                *out_buf.add(3) = iv1.max;
            }
            1
        }
        _ => 0,
    }
}

/// Two-variable weighted linear / Karr affine conservation reduction (`a * x + b * y in [sum_min, sum_max]`)
/// over `Nat` intervals `x in [x_min, x_max]` and `y in [y_min, y_max]`.
/// Writes `[x_min', x_max', y_min', y_max']` into `out_buf` (4 `i64` elements) and returns `1`,
/// or returns `0` if infeasible (`Bottom`) or `out_buf` is null.
#[no_mangle]
pub extern "C" fn lean_analyzer_weighted_linear_reduce(
    a: i64,
    b: i64,
    sum_min: i64,
    sum_max: i64,
    x_min: i64,
    x_max: i64,
    y_min: i64,
    y_max: i64,
    out_buf: *mut i64,
) -> u32 {
    if out_buf.is_null() {
        return 0;
    }
    match crate::affine::reduce_weighted_linear_two_vars(
        a,
        b,
        sum_min,
        sum_max,
        IntervalBound::new(x_min, x_max),
        IntervalBound::new(y_min, y_max),
    ) {
        Some((rx, ry)) => {
            unsafe {
                *out_buf = rx.min;
                *out_buf.add(1) = rx.max;
                *out_buf.add(2) = ry.min;
                *out_buf.add(3) = ry.max;
            }
            1
        }
        None => 0,
    }
}

/// Alias for `lean_analyzer_weighted_linear_reduce` supporting $\times 100$ weighted simplex reduction.
#[no_mangle]
#[allow(non_snake_case)]
pub extern "C" fn lean_analyzer_WeightedSimplexReduce(
    a: i64,
    b: i64,
    sum_min: i64,
    sum_max: i64,
    x_min: i64,
    x_max: i64,
    y_min: i64,
    y_max: i64,
    out_buf: *mut i64,
) -> u32 {
    lean_analyzer_weighted_linear_reduce(a, b, sum_min, sum_max, x_min, x_max, y_min, y_max, out_buf)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wasm_abi_wave5_exports() {
        let mut out2 = [0i64; 2];
        assert_eq!(lean_analyzer_eval_nat_land(0, 15, 6, 6, out2.as_mut_ptr()), 1);
        assert_eq!(out2, [0, 6]);

        assert_eq!(lean_analyzer_eval_nat_lor(1, 2, 4, 4, out2.as_mut_ptr()), 1);
        assert_eq!(out2, [5, 6]);

        assert_eq!(lean_analyzer_eval_nat_xor(3, 3, 5, 5, out2.as_mut_ptr()), 1);
        assert_eq!(out2, [6, 6]);

        assert_eq!(lean_analyzer_eval_nat_shl(3, 5, 2, 2, out2.as_mut_ptr()), 1);
        assert_eq!(out2, [12, 20]);

        assert_eq!(lean_analyzer_eval_nat_shr(12, 20, 2, 2, out2.as_mut_ptr()), 1);
        assert_eq!(out2, [3, 5]);

        let mut out4 = [0i64; 4];
        assert_eq!(
            lean_analyzer_reduce_interval_congruence(10, 22, 5, 3, out4.as_mut_ptr()),
            1
        );
        assert_eq!(out4, [13, 18, 5, 3]);
        assert_eq!(
            lean_analyzer_reduce_interval_congruence(14, 17, 5, 3, out4.as_mut_ptr()),
            0
        );

        // Zone termination: i - n <= -1 (i < n), step = 1 => True (2)
        assert_eq!(lean_analyzer_zone_check_sub_decreasing(-1, 1), 2);
        // Step = 0 => False (1)
        assert_eq!(lean_analyzer_zone_check_sub_decreasing(-1, 0), 1);

        // Octagon: v0 in [30, 100], v1 in [0, 100], v0 + v1 == 100 => v0 in [30, 100], v1 in [0, 70]
        assert_eq!(
            lean_analyzer_octagon_reduce_two_vars(
                30,
                100,
                0,
                100,
                100,
                100,
                crate::nat_interval::INF,
                out4.as_mut_ptr()
            ),
            1
        );
        assert_eq!(out4, [30, 100, 0, 70]);

        // Weighted linear / Karr simplex: 2 * x + 3 * y == 100, x in [10, 100], y in [0, 100]
        // => x in [11, 50], y in [0, 26]
        assert_eq!(
            lean_analyzer_weighted_linear_reduce(
                2,
                3,
                100,
                100,
                10,
                100,
                0,
                100,
                out4.as_mut_ptr()
            ),
            1
        );
        assert_eq!(out4, [11, 50, 0, 26]);
        assert_eq!(
            lean_analyzer_WeightedSimplexReduce(
                2,
                3,
                100,
                100,
                10,
                100,
                0,
                100,
                out4.as_mut_ptr()
            ),
            1
        );
        assert_eq!(out4, [11, 50, 0, 26]);
    }
}


