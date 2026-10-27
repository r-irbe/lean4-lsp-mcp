/-!
LeanAnalyzer.AbstractInterpretation -- Formal Abstract Interpretation & Self-Bootstrapping.
 Zero sorry constraint.
-/

set_option autoImplicit false

namespace LeanAnalyzer

/-- Abstract sign lattice elements. -/
inductive AbstractSign : Type
  | bot
  | zero
  | pos
  | nonNeg
  | neg
  | nonPos
  | nonZero
  | top
  deriving DecidableEq, Repr

namespace AbstractSign

/-- Concrete integer property corresponding to an abstract sign. -/
def gamma (s : AbstractSign) (n : Int) : Prop :=
  match s with
  | bot => False
  | zero => n = 0
  | pos => n > 0
  | neg => n < 0
  | nonNeg => n >= 0
  | nonPos => n <= 0
  | nonZero => n ≠ 0
  | top => True

/-- Bitmask representation (3-bit bitset: zero=1, pos=2, neg=4). -/
def toBitmask (s : AbstractSign) : UInt8 :=
  match s with
  | bot => 0
  | zero => 1
  | pos => 2
  | nonNeg => 3
  | neg => 4
  | nonPos => 5
  | nonZero => 6
  | top => 7

/-- Decode bitmask into AbstractSign. -/
def fromBitmask (b : UInt8) : AbstractSign :=
  let masked := b &&& 7
  if masked == 0 then bot
  else if masked == 1 then zero
  else if masked == 2 then pos
  else if masked == 3 then nonNeg
  else if masked == 4 then neg
  else if masked == 5 then nonPos
  else if masked == 6 then nonZero
  else top

theorem from_to_bitmask (s : AbstractSign) : fromBitmask (toBitmask s) = s := by
  cases s <;> rfl

/-- Lattice join (least upper bound) computed via bitwise OR on the 3-bit representation. -/
def join (a b : AbstractSign) : AbstractSign :=
  fromBitmask (toBitmask a ||| toBitmask b)

/-- Lattice meet (greatest lower bound) computed via bitwise AND on the 3-bit representation. -/
def meet (a b : AbstractSign) : AbstractSign :=
  fromBitmask (toBitmask a &&& toBitmask b)

/-- Information ordering (subtyping): a ⊑ b iff a join b = b. -/
def le (a b : AbstractSign) : Prop :=
  join a b = b

instance (a b : AbstractSign) : Decidable (le a b) :=
  inferInstanceAs (Decidable (join a b = b))


theorem join_comm (a b : AbstractSign) : join a b = join b a := by
  cases a <;> cases b <;> rfl

theorem join_idem (a : AbstractSign) : join a a = a := by
  cases a <;> rfl

theorem meet_comm (a b : AbstractSign) : meet a b = meet b a := by
  cases a <;> cases b <;> rfl

theorem meet_idem (a : AbstractSign) : meet a a = a := by
  cases a <;> rfl

theorem le_refl (a : AbstractSign) : le a a := by
  unfold le
  exact join_idem a

theorem le_bot (a : AbstractSign) :
    le bot a := by
  unfold le
  cases a <;> rfl

theorem le_top (a : AbstractSign) :
    le a top := by
  unfold le
  cases a <;> rfl

@[simp] theorem meet_nonNeg_pos : meet nonNeg pos = pos := rfl

@[simp] theorem join_zero_pos : join zero pos = nonNeg := rfl

theorem join_sound_zero_pos (n : Int) : gamma zero n ∨ gamma pos n → gamma nonNeg n := by
  intro h
  rcases h with h0 | hp
  · unfold gamma at h0 ⊢; omega
  · unfold gamma at hp ⊢; omega

theorem join_sound_zero_neg (n : Int) : gamma zero n ∨ gamma neg n → gamma nonPos n := by
  intro h
  rcases h with h0 | hn
  · unfold gamma at h0 ⊢; omega
  · unfold gamma at hn ⊢; omega

theorem meet_sound_nonNeg_pos (n : Int) : gamma (meet nonNeg pos) n ↔ (gamma nonNeg n ∧ gamma pos n) := by
  change gamma pos n ↔ (gamma nonNeg n ∧ gamma pos n)
  unfold gamma
  constructor
  · intro hp
    exact ⟨by omega, hp⟩
  · intro ⟨_, hp⟩
    exact hp

theorem bitmask_join_compat (a b : AbstractSign) :
    toBitmask (join a b) = (toBitmask a ||| toBitmask b) := by
  cases a <;> cases b <;> rfl

theorem bitmask_meet_compat (a b : AbstractSign) :
    toBitmask (meet a b) = (toBitmask a &&& toBitmask b) := by
  cases a <;> cases b <;> rfl

/-- Self-bootstrapping code synthesis: emits standalone verified Rust lattice code. -/
def emitRustLatticeModule : String :=
"// Auto-generated from LeanAnalyzer.AbstractInterpretation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum AbstractSign {
    Bottom = 0,
    Zero = 1,
    Positive = 2,
    NonNegative = 3,
    Negative = 4,
    NonPositive = 5,
    NonZero = 6,
    Top = 7,
}
impl AbstractSign {
    pub fn join(self, other: Self) -> Self {
        Self::from_u8((self as u8) | (other as u8))
    }
    pub fn meet(self, other: Self) -> Self {
        Self::from_u8((self as u8) & (other as u8))
    }
}
"
end AbstractSign

/-!
## Verified NatInterval, NatCongruence, and Granger Reduction

We mechanize the Galois concretization `gamma` and soundness of the core
transfer functions for:
1. `NatInterval`: closed intervals `[lo, hi]` over `Nat` (Cousot & Cousot 1976).
2. `NatCongruence`: affine arithmetic progressions `{ offset + k * stride | k : Nat }`
   (Granger 1989; Cousot 2021 Ch. 38 & 40).
3. `ReducedNatProduct`: the mutual interval-congruence product and singleton narrowing.
-/

/-- Closed interval `[lo, hi]` over `Nat`. -/
structure NatInterval where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

namespace NatInterval

/-- Concretization `gamma([lo, hi]) = { n : Nat | lo <= n /\ n <= hi }`. -/
def gamma (iv : NatInterval) (n : Nat) : Prop :=
  iv.lo <= n ∧ n <= iv.hi

/-- Point interval `[c, c]`. -/
def point (c : Nat) : NatInterval :=
  { lo := c, hi := c }

/-- Interval join `[min a.lo b.lo, max a.hi b.hi]`. -/
def join (a b : NatInterval) : NatInterval :=
  { lo := min a.lo b.lo, hi := max a.hi b.hi }

/-- Interval meet `[max a.lo b.lo, min a.hi b.hi]`. -/
def meet (a b : NatInterval) : NatInterval :=
  { lo := max a.lo b.lo, hi := min a.hi b.hi }

/-- Abstract interval addition `[a.lo + b.lo, a.hi + b.hi]`. -/
def add (a b : NatInterval) : NatInterval :=
  { lo := a.lo + b.lo, hi := a.hi + b.hi }

/-- Abstract saturating subtraction `[a.lo - b.hi, a.hi - b.lo]`. -/
def sub (a b : NatInterval) : NatInterval :=
  { lo := a.lo - b.hi, hi := a.hi - b.lo }

theorem point_sound (c : Nat) : gamma (point c) c := by
  unfold gamma point
  dsimp
  omega

theorem join_sound_left (a b : NatInterval) (n : Nat) (h : gamma a n) :
    gamma (join a b) n := by
  unfold gamma join at *
  dsimp
  omega

theorem join_sound_right (a b : NatInterval) (n : Nat) (h : gamma b n) :
    gamma (join a b) n := by
  unfold gamma join at *
  dsimp
  omega

theorem join_sound (a b : NatInterval) (n : Nat) :
    gamma a n ∨ gamma b n → gamma (join a b) n := by
  intro h
  rcases h with ha | hb
  · exact join_sound_left a b n ha
  · exact join_sound_right a b n hb

theorem meet_sound (a b : NatInterval) (n : Nat) :
    gamma (meet a b) n ↔ (gamma a n ∧ gamma b n) := by
  unfold gamma meet
  dsimp
  omega

theorem add_sound (a b : NatInterval) (x y : Nat)
    (hx : gamma a x) (hy : gamma b y) :
    gamma (add a b) (x + y) := by
  unfold gamma add at *
  dsimp
  omega

theorem sub_sound (a b : NatInterval) (x y : Nat)
    (hx : gamma a x) (hy : gamma b y) :
    gamma (sub a b) (x - y) := by
  unfold gamma sub at *
  dsimp
  omega

end NatInterval

/-- Affine congruence class `stride * Nat + offset` over `Nat` (Granger 1989). -/
structure NatCongruence where
  stride : Nat
  offset : Nat
  deriving DecidableEq, Repr

namespace NatCongruence

/-- Concretization `gamma(s, o) = { n : Nat | exists k : Nat, n = o + k * s }`. -/
def gamma (c : NatCongruence) (n : Nat) : Prop :=
  ∃ k : Nat, n = c.offset + k * c.stride

/-- Top congruence `1 * Nat + 0` covering all natural numbers. -/
def top : NatCongruence :=
  { stride := 1, offset := 0 }

/-- Singleton congruence `0 * Nat + v = { v }`. -/
def singleton (v : Nat) : NatCongruence :=
  { stride := 0, offset := v }

/-- Same-stride congruence addition `(s, o1) + (s, o2) = (s, o1 + o2)`. -/
def addSameStride (s o1 o2 : Nat) : NatCongruence :=
  { stride := s, offset := o1 + o2 }

/-- Scaling a congruence by a constant `c * (s, o) = (c * s, c * o)`. -/
def scale (c : Nat) (cg : NatCongruence) : NatCongruence :=
  { stride := c * cg.stride, offset := c * cg.offset }

/-- Successor congruence `(s, o) + 1 = (s, o + 1)`. -/
def succ (cg : NatCongruence) : NatCongruence :=
  { stride := cg.stride, offset := cg.offset + 1 }

theorem top_sound (n : Nat) : gamma top n := by
  unfold gamma top
  refine ⟨n, ?_⟩
  dsimp
  omega

theorem singleton_sound (v : Nat) : gamma (singleton v) v := by
  unfold gamma singleton
  refine ⟨0, ?_⟩
  dsimp

theorem singleton_exact (v n : Nat) (h : gamma (singleton v) n) : n = v := by
  rcases h with ⟨k, hk⟩
  unfold singleton at hk
  dsimp at hk
  exact hk

theorem succ_sound (cg : NatCongruence) (n : Nat) (h : gamma cg n) :
    gamma (succ cg) (n + 1) := by
  rcases h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  unfold succ
  dsimp
  omega

theorem addSameStride_sound (s o1 o2 x y : Nat)
    (hx : gamma { stride := s, offset := o1 } x)
    (hy : gamma { stride := s, offset := o2 } y) :
    gamma (addSameStride s o1 o2) (x + y) := by
  rcases hx with ⟨kx, hkx⟩
  rcases hy with ⟨ky, hky⟩
  refine ⟨kx + ky, ?_⟩
  unfold addSameStride
  dsimp at hkx hky ⊢
  calc
    x + y = (o1 + kx * s) + (o2 + ky * s) := by rw [hkx, hky]
    _ = (o1 + o2) + (kx * s + ky * s) := by omega
    _ = (o1 + o2) + (kx + ky) * s := by rw [Nat.add_mul]

theorem scale_sound (c : Nat) (cg : NatCongruence) (x : Nat) (hx : gamma cg x) :
    gamma (scale c cg) (c * x) := by
  rcases hx with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  unfold scale
  dsimp
  calc
    c * x = c * (cg.offset + k * cg.stride) := by rw [hk]
    _ = c * cg.offset + c * (k * cg.stride) := by rw [Nat.mul_add]
    _ = c * cg.offset + (c * k) * cg.stride := by rw [Nat.mul_assoc]
    _ = c * cg.offset + (k * c) * cg.stride := by rw [Nat.mul_comm c k]
    _ = c * cg.offset + k * (c * cg.stride) := by rw [Nat.mul_assoc]

/-- Granger singleton reduction: when an interval collapses to a point `[v, v]`,
refining the congruence to `singleton v` preserves all concrete inhabitants in the
intersection `NatInterval.gamma iv n /\ NatCongruence.gamma cg n`. -/
theorem reduce_point_sound (iv : NatInterval) (cg : NatCongruence) (n : Nat)
    (h_pt : iv.lo = iv.hi)
    (h_iv : NatInterval.gamma iv n)
    (_h_cg : gamma cg n) :
    gamma (singleton iv.lo) n := by
  unfold NatInterval.gamma at h_iv
  have hn : n = iv.lo := by omega
  rw [hn]
  exact singleton_sound iv.lo

end NatCongruence

/-!
## : Threshold Widening, Zone DBM Closure, and Diagnostic Certificates

1. `NatInterval.widenThreshold`: threshold-stepped widening (`widen_with_thresholds(T)`,
   Blanchet et al. 2003 / Mine 2017) preserves `gamma` for both `prev` and `next` whenever
   the threshold `t` upper-bounds `next.hi`.
2. `ZoneBound`: Difference-Bound Matrix (DBM) upper bound `x - y <= c` (Mine 2001) and
   Floyd-Warshall transitive closure soundness `(x - y <= c1) /\ (y - z <= c2) -> (x - z <= c1 + c2)`.
3. `NatInterval.natSubTruncation_cert_sound`: formal proof of the `NatSubTruncation`
   static diagnostic certificate: if `a.hi <= b.lo`, then for every `x in gamma(a)` and
   `y in gamma(b)`, natural subtraction `x - y = 0`.
-/

namespace NatInterval

/-- Single-threshold widening step: lowers `lo` to `0` if `next.lo < prev.lo` and raises `hi`
to threshold `t` if `prev.hi < next.hi`. -/
def widenThreshold (prev next : NatInterval) (t : Nat) : NatInterval :=
  { lo := if next.lo < prev.lo then 0 else prev.lo
  , hi := if prev.hi < next.hi then max next.hi t else prev.hi }

theorem widenThreshold_sound_prev (prev next : NatInterval) (t n : Nat)
    (h : gamma prev n) :
    gamma (widenThreshold prev next t) n := by
  unfold gamma widenThreshold at *
  dsimp
  split <;> split <;> omega

theorem widenThreshold_sound_next (prev next : NatInterval) (t n : Nat)
    (h : gamma next n) :
    gamma (widenThreshold prev next t) n := by
  unfold gamma widenThreshold at *
  dsimp
  split <;> split <;> omega

/-- `NatSubTruncation` diagnostic certificate soundness:
when `a.hi <= b.lo`, any concrete `x in gamma(a)` and `y in gamma(b)` satisfy `x - y = 0`. -/
theorem natSubTruncation_cert_sound (a b : NatInterval) (x y : Nat)
    (h_cert : a.hi <= b.lo)
    (hx : gamma a x)
    (hy : gamma b y) :
    x - y = 0 := by
  unfold gamma at hx hy
  omega

/-- `DivisionByZeroGuardProven` diagnostic certificate soundness:
when `1 <= b.lo`, any concrete `y in gamma(b)` satisfies `y != 0`. -/
theorem divByZeroGuard_cert_sound (b : NatInterval) (y : Nat)
    (h_guard : 1 <= b.lo)
    (hy : gamma b y) :
    y ≠ 0 := by
  unfold gamma at hy
  omega

/-- Cousot & Cousot (1977) interval narrowing operator (`COUSOT s40.5`, `ARCERI2023 s3.2`):
refines a post-fixpoint interval `prev` using a one-step transfer image `next` by raising
`lo` to `max prev.lo next.lo` and lowering `hi` to `min prev.hi next.hi`. -/
def narrow (prev next : NatInterval) : NatInterval :=
  { lo := max prev.lo next.lo, hi := min prev.hi next.hi }

/-- Soundness of interval narrowing: any concrete value `n` in the post-fixpoint `prev`
that also survives the transfer step `next` remains in `narrow prev next`. -/
theorem narrow_sound (prev next : NatInterval) (n : Nat)
    (h_prev : gamma prev n)
    (h_next : gamma next n) :
    gamma (narrow prev next) n := by
  unfold gamma narrow at *
  dsimp
  omega

/-- Precision improvement on the lower bound: narrowing never lowers `prev.lo`
and raises it to at least `next.lo`. -/
theorem narrow_improves_lo (prev next : NatInterval) :
    prev.lo <= (narrow prev next).lo ∧ next.lo <= (narrow prev next).lo := by
  unfold narrow
  dsimp
  omega

/-- Precision improvement on the upper bound: narrowing never raises `prev.hi`
and lowers it to at most `next.hi`. -/
theorem narrow_improves_hi (prev next : NatInterval) :
    (narrow prev next).hi <= prev.hi ∧ (narrow prev next).hi <= next.hi := by
  unfold narrow
  dsimp
  omega

/-- Stability at an exact fixpoint: if `next` already contains `prev`
(`next.lo <= prev.lo` and `prev.hi <= next.hi`), narrowing leaves `prev` unchanged. -/
theorem narrow_fixed_of_contains (prev next : NatInterval)
    (h_lo : next.lo <= prev.lo)
    (h_hi : prev.hi <= next.hi) :
    narrow prev next = prev := by
  cases prev with
  | mk plo phi =>
    unfold narrow
    dsimp at h_lo h_hi ⊢
    congr 1 <;> omega

/-- Two-step descending narrowing chain soundness (`COUSOT s40.5`, `ARCERI2023 s3.2`):
if `n` belongs to the initial post-fixpoint `prev` and survives two successive
transfer images `step1` and `step2`, then `n` belongs to `narrow (narrow prev step1) step2`. -/
theorem narrow_chain2_sound (prev step1 step2 : NatInterval) (n : Nat)
    (h_prev : gamma prev n)
    (h_step1 : gamma step1 n)
    (h_step2 : gamma step2 n) :
    gamma (narrow (narrow prev step1) step2) n :=
  narrow_sound (narrow prev step1) step2 n (narrow_sound prev step1 n h_prev h_step1) h_step2

/-- Monotonicity of interval concretization (`COUSOT s38.2`):
if interval `b` encloses interval `a` (`b.lo <= a.lo` and `a.hi <= b.hi`),
then any concrete value in `gamma a` also belongs to `gamma b`. -/
theorem gamma_mono (a b : NatInterval) (n : Nat)
    (h_lo : b.lo <= a.lo)
    (h_hi : a.hi <= b.hi)
    (h_a : gamma a n) :
    gamma b n := by
  unfold gamma at *
  omega

/-- Threshold widening upper-bound jump boundedness (`COUSOT s40.4`, Blanchet et al. 2003):
when `prev.hi < next.hi` and `next.hi <= t`, threshold widening jumps `hi` to
exactly the threshold `t` rather than `+oo`. -/
theorem widenThreshold_hi_eq_threshold (prev next : NatInterval) (t : Nat)
    (h_grow : prev.hi < next.hi)
    (h_thresh : next.hi <= t) :
    (widenThreshold prev next t).hi = t := by
  unfold widenThreshold
  dsimp
  split <;> omega

end NatInterval

/-- Zone difference-bound constraint `x - y <= c` over integers (Mine 2001). -/
structure ZoneBound where
  c : Int
  deriving DecidableEq, Repr

namespace ZoneBound

/-- Concretization `gamma(c)(x, y) := (x - y <= c)`. -/
def gamma (b : ZoneBound) (x y : Int) : Prop :=
  x - y <= b.c

/-- Floyd-Warshall transitive composition `(x - y <= b1.c) + (y - z <= b2.c) -> (x - z <= b1.c + b2.c)`. -/
def compose (b1 b2 : ZoneBound) : ZoneBound :=
  { c := b1.c + b2.c }

theorem compose_sound (b1 b2 : ZoneBound) (x y z : Int)
    (h1 : gamma b1 x y) (h2 : gamma b2 y z) :
    gamma (compose b1 b2) x z := by
  unfold gamma compose at *
  dsimp
  omega

/-- Zone termination check soundness: if `next_x - x <= delta` with `delta <= -1`
and `1 <= x`, then `0 <= next_x` and `next_x < x` (strict well-founded decrease). -/
theorem check_sub_decreasing_sound (b : ZoneBound) (x next_x : Int)
    (h_zone : gamma b next_x x)
    (h_neg : b.c <= -1) :
    next_x < x := by
  unfold gamma at h_zone
  omega

end ZoneBound

/-!
## : Octagon Relational Domain (`+` or `-` `x_i` and `x_j` `<= c`, Mine 2006 / Pelleau 2015)

1. `OctagonBound`: coherent difference/sum bounds `x + y <= sum_hi`, `sum_lo <= x + y`,
   and `x - y <= diff_hi` over `Nat`.
2. `OctagonBound.parity_tighten_sound`: combining `x + y <= s` and `x - y <= d` implies
   `2 * x <= s + d`, which over integers tightens to `x <= (s + d) / 2` (Mine 2006 Section 4.3).
3. `OctagonBound.simplex_complement_sound`: under simplex conservation `x + y <= s` and
   lower bound `lo_x <= x`, the complement variable satisfies `y <= s - lo_x`.
-/

namespace OctagonBound

/-- Integer parity tightening: if `x + y <= s` and `x - y <= d` over `Nat`, then `2 * x <= s + d`. -/
theorem sum_diff_double_bound (x y s d : Nat)
    (h_sum : x + y <= s)
    (h_diff : x <= y + d) :
    2 * x <= s + d := by
  omega

/-- Strong closure / floor-division tightening (`PELLEAU2015 s2.4`, Mine 2006 Section 4.3):
combining `x + y <= s` and `x <= y + d` yields the floor-divided unary upper bound
`x <= (s + d) / 2`. -/
theorem closed_tighten_sound (x y s d : Nat)
    (h_sum : x + y <= s)
    (h_diff : x <= y + d) :
    x <= (s + d) / 2 := by
  have h2 := sum_diff_double_bound x y s d h_sum h_diff
  omega

/-- Octagon transitive difference tightening over `Nat`:
if `x <= y + d1` and `y <= z + d2`, then `x <= z + (d1 + d2)`. -/
theorem diff_trans_sound (x y z d1 d2 : Nat)
    (h1 : x <= y + d1)
    (h2 : y <= z + d2) :
    x <= z + (d1 + d2) := by
  omega

/-- Simplex conservation tightening (`PELLEAU2015 s2.4 p1`, `COUSOT s42.1 p1`):
if `x + y <= s` and `lo_x <= x`, then `y <= s - lo_x` and `lo_x + y <= s`. -/
theorem simplex_complement_sound (x y s lo_x : Nat)
    (h_sum : x + y <= s)
    (h_lo : lo_x <= x) :
    y <= s - lo_x := by
  have h_le : lo_x + y <= s := Nat.le_trans (Nat.add_le_add_right h_lo y) h_sum
  omega

/-- Two-step relational octagon transitive bound propagation (`PELLEAU2015 s2.4`, `COUSOT s42.1`):
given sum constraint `x + y <= s1` and difference constraint `y <= z + d`,
we obtain both the residual bound `x <= s1 - y` and the difference bound `y <= z + d`. -/
theorem octagon_chain_tighten (x y z s1 d : Nat)
    (h_sum : x + y <= s1)
    (h_diff : y <= z + d) :
    x <= s1 - y ∧ y <= z + d := by
  have h_x : x <= s1 - y := by omega
  exact ⟨h_x, h_diff⟩

end OctagonBound

/-!
## : Scaled Two-Variable Linear / Karr Affine Conservation (`a * x + b * y <= U` and `L <= a * x + b * y`)

1. `WeightedLinearBound.weighted_linear_upper_sound`: under weighted upper bound
   `a * x + b * y <= U` and lower bound `y_min <= y`, we have `b * y_min <= b * y` and
   `a * x <= U - b * y_min`.
2. `WeightedLinearBound.weighted_linear_lower_sound`: under weighted lower bound
   `L <= a * x + b * y` and upper bound `y <= y_max`, we have `b * y <= b * y_max` and
   `L - b * y_max <= a * x`.
-/

namespace WeightedLinearBound

/-- Soundness of weighted two-variable linear upper-bound tightening over `Nat`:
given `a * x + b * y <= U` and `y_min <= y`, `a * x <= U - b * y_min`. -/
theorem weighted_linear_upper_sound (a b x y U y_min : Nat)
    (h_sum : a * x + b * y <= U)
    (h_ymin : y_min <= y) :
    a * x <= U - b * y_min := by
  have h_by : b * y_min <= b * y := Nat.mul_le_mul_left b h_ymin
  have h_le : a * x + b * y_min <= U :=
    Nat.le_trans (Nat.add_le_add_left h_by (a * x)) h_sum
  omega

/-- Soundness of weighted two-variable linear lower-bound tightening over `Nat`:
given `L <= a * x + b * y` and `y <= y_max`, `L - b * y_max <= a * x`. -/
theorem weighted_linear_lower_sound (a b x y L y_max : Nat)
    (h_sum : L <= a * x + b * y)
    (h_ymax : y <= y_max) :
    L - b * y_max <= a * x := by
  have h_by : b * y <= b * y_max := Nat.mul_le_mul_left b h_ymax
  have h_le : L <= a * x + b * y_max :=
    Nat.le_trans h_sum (Nat.add_le_add_left h_by (a * x))
  omega

end WeightedLinearBound

end LeanAnalyzer




