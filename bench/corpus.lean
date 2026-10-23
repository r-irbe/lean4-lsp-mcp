-- bench/corpus.lean - the six-statement benchmark fixture (tranche-4 protocol).
-- Two small idiomatic, two numeric, one known-true heavy (list), one
-- abstract control (expected unsupported). Proof bodies are irrelevant:
-- the verb extracts only the declaration header.
import Mathlib

theorem s1_add_comm (a b : Nat) : a + b = b + a := by omega
theorem s2_lt_three (n : Nat) : n < 3 := by omega
theorem s3_two_mul (n : Nat) : 2 * n ≠ n + 1 := by omega
theorem s4_pow_bound (n : Nat) : n <= 2 ^ n := by omega
theorem s5_reverse_reverse (l : List Int) : l.reverse.reverse = l := by simp
theorem s6_abstract (p : Nat -> Prop) : p 0 -> p 0 := by tauto

theorem far_stmt (n : Nat) : n < 150 := by sorry
