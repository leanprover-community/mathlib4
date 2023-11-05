/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Parity
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.ForSqrt

#align_import data.nat.sqrt from "leanprover-community/mathlib"@"ba2245edf0c8bb155f1569fd9b9492a9b384cde6"

/-!
# Square root of natural numbers

This file defines an efficient implementation of the square root function that returns the
unique `r` such that `r * r ≤ n < (r + 1) * (r + 1)`.

## Reference

See [Wikipedia, *Methods of computing square roots*]
(https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_system_(base_2)).
-/


namespace Nat

-- Porting note: the implementation òf `Nat.sqrt` in `Std` no longer needs `sqrt_aux`.
#noalign nat.sqrt_aux_dec
#noalign nat.sqrt_aux
#noalign nat.sqrt_aux_0
#noalign nat.sqrt_aux_1
#noalign nat.sqrt_aux_2
private def IsSqrt (n q : ℕ) : Prop :=
  q * q ≤ n ∧ n < (q + 1) * (q + 1)
-- Porting note: as the definition of square root has changed,
-- the proof of `sqrt_isSqrt` is attempted from scratch.
/-
Sketch of proof:
Up to rounding, in terms of the definition of `sqrt.iter`,

* By AM-GM inequality, `next² ≥ n` giving one of the bounds.
* When we terminated, we have `guess ≥ next` from which we deduce the other bound `n ≥ next²`.

To turn this into a lean proof we need to manipulate, use properties of natural number division etc.
-/
private theorem sqrt_isSqrt (n : ℕ) : IsSqrt n (sqrt n) := by
  match n with
  | 0 => simp [IsSqrt]
  | 1 => simp [IsSqrt]
  | n + 2 =>
    have h : ¬ (n + 2) ≤ 1 := by simp
    simp only [IsSqrt, sqrt, h, ite_false]
    refine ⟨sqrt.iter_sq_le _ _, sqrt.lt_iter_succ_sq _ _ ?_⟩
    simp only [mul_add, add_mul, one_mul, mul_one, ← add_assoc]
    rw [lt_add_one_iff, add_assoc, ← mul_two]
    refine le_trans (div_add_mod' (n + 2) 2).ge ?_
    rw [add_comm, add_le_add_iff_right, add_mod_right]
    simp only [zero_lt_two, add_div_right, succ_mul_succ_eq]
    refine le_trans (b := 1) ?_ ?_
    · exact (lt_succ.1 $ mod_lt n zero_lt_two)
    · simp only [le_add_iff_nonneg_left]; exact zero_le _

theorem sqrt_le (n : ℕ) : sqrt n * sqrt n ≤ n :=
  (sqrt_isSqrt n).left

theorem sqrt_le' (n : ℕ) : sqrt n ^ 2 ≤ n :=
  Eq.trans_le (sq (sqrt n)) (sqrt_le n)

theorem lt_succ_sqrt (n : ℕ) : n < succ (sqrt n) * succ (sqrt n) :=
  (sqrt_isSqrt n).right

theorem lt_succ_sqrt' (n : ℕ) : n < succ (sqrt n) ^ 2 :=
  (sq (succ (sqrt n))).symm ▸ (lt_succ_sqrt n)

theorem sqrt_le_add (n : ℕ) : n ≤ sqrt n * sqrt n + sqrt n + sqrt n := by
  rw [← succ_mul]; exact le_of_lt_succ (lt_succ_sqrt n)

theorem le_sqrt {m n : ℕ} : m ≤ sqrt n ↔ m * m ≤ n :=
  ⟨fun h => le_trans (mul_self_le_mul_self h) (sqrt_le n),
   fun h => le_of_lt_succ <| mul_self_lt_mul_self_iff.2 <| lt_of_le_of_lt h (lt_succ_sqrt n)⟩

theorem le_sqrt' {m n : ℕ} : m ≤ sqrt n ↔ m ^ 2 ≤ n := by simpa only [pow_two] using le_sqrt

theorem sqrt_lt {m n : ℕ} : sqrt m < n ↔ m < n * n :=
  lt_iff_lt_of_le_iff_le le_sqrt

theorem sqrt_lt' {m n : ℕ} : sqrt m < n ↔ m < n ^ 2 :=
  lt_iff_lt_of_le_iff_le le_sqrt'

theorem sqrt_le_self (n : ℕ) : sqrt n ≤ n :=
  le_trans (le_mul_self _) (sqrt_le n)

theorem sqrt_le_sqrt {m n : ℕ} (h : m ≤ n) : sqrt m ≤ sqrt n :=
  le_sqrt.2 (le_trans (sqrt_le _) h)

@[simp]
theorem sqrt_zero : sqrt 0 = 0 := rfl

theorem sqrt_eq_zero {n : ℕ} : sqrt n = 0 ↔ n = 0 :=
  ⟨fun h =>
      Nat.eq_zero_of_le_zero <| le_of_lt_succ <| (@sqrt_lt n 1).1 <| by rw [h]; decide,
    by rintro rfl; simp⟩

theorem eq_sqrt {n q} : q = sqrt n ↔ q * q ≤ n ∧ n < (q + 1) * (q + 1) :=
  ⟨fun e => e.symm ▸ sqrt_isSqrt n,
   fun ⟨h₁, h₂⟩ => le_antisymm (le_sqrt.2 h₁) (le_of_lt_succ <| sqrt_lt.2 h₂)⟩

theorem eq_sqrt' {n q} : q = sqrt n ↔ q ^ 2 ≤ n ∧ n < (q + 1) ^ 2 := by
  simpa only [pow_two] using eq_sqrt

theorem le_three_of_sqrt_eq_one {n : ℕ} (h : sqrt n = 1) : n ≤ 3 :=
  le_of_lt_succ <| (@sqrt_lt n 2).1 <| by rw [h]; decide

theorem sqrt_lt_self {n : ℕ} (h : 1 < n) : sqrt n < n :=
  sqrt_lt.2 <| by have := Nat.mul_lt_mul_of_pos_left h (lt_of_succ_lt h); rwa [mul_one] at this

theorem sqrt_pos {n : ℕ} : 0 < sqrt n ↔ 0 < n :=
  le_sqrt

theorem sqrt_add_eq (n : ℕ) {a : ℕ} (h : a ≤ n + n) : sqrt (n * n + a) = n :=
  le_antisymm
    (le_of_lt_succ <|
      sqrt_lt.2 <| by
        rw [succ_mul, mul_succ, add_succ, add_assoc];
          exact lt_succ_of_le (Nat.add_le_add_left h _))
    (le_sqrt.2 <| Nat.le_add_right _ _)

theorem sqrt_add_eq' (n : ℕ) {a : ℕ} (h : a ≤ n + n) : sqrt (n ^ 2 + a) = n :=
  (congr_arg (fun i => sqrt (i + a)) (sq n)).trans (sqrt_add_eq n h)

theorem sqrt_eq (n : ℕ) : sqrt (n * n) = n :=
  sqrt_add_eq n (zero_le _)

theorem sqrt_eq' (n : ℕ) : sqrt (n ^ 2) = n :=
  sqrt_add_eq' n (zero_le _)

@[simp]
theorem sqrt_one : sqrt 1 = 1 :=
  sqrt_eq 1

theorem sqrt_succ_le_succ_sqrt (n : ℕ) : sqrt n.succ ≤ n.sqrt.succ :=
  le_of_lt_succ <| sqrt_lt.2 <| lt_succ_of_le <|
  succ_le_succ <| le_trans (sqrt_le_add n) <| add_le_add_right
    (by refine' add_le_add (Nat.mul_le_mul_right _ _) _ <;> exact Nat.le_add_right _ 2) _

theorem exists_mul_self (x : ℕ) : (∃ n, n * n = x) ↔ sqrt x * sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq], fun h => ⟨sqrt x, h⟩⟩

theorem exists_mul_self' (x : ℕ) : (∃ n, n ^ 2 = x) ↔ sqrt x ^ 2 = x := by
  simpa only [pow_two] using exists_mul_self x

/-- `IsSquare` can be decided on `ℕ` by checking against the square root. -/
instance : DecidablePred (IsSquare : ℕ → Prop) :=
  fun m => decidable_of_iff' (Nat.sqrt m * Nat.sqrt m = m) <| by
    simp_rw [←Nat.exists_mul_self m, IsSquare, eq_comm]

theorem sqrt_mul_sqrt_lt_succ (n : ℕ) : sqrt n * sqrt n < n + 1 :=
  lt_succ_iff.mpr (sqrt_le _)

theorem sqrt_mul_sqrt_lt_succ' (n : ℕ) : sqrt n ^ 2 < n + 1 :=
  lt_succ_iff.mpr (sqrt_le' _)

theorem succ_le_succ_sqrt (n : ℕ) : n + 1 ≤ (sqrt n + 1) * (sqrt n + 1) :=
  le_of_pred_lt (lt_succ_sqrt _)

theorem succ_le_succ_sqrt' (n : ℕ) : n + 1 ≤ (sqrt n + 1) ^ 2 :=
  le_of_pred_lt (lt_succ_sqrt' _)

/-- There are no perfect squares strictly between m² and (m+1)² -/
theorem not_exists_sq {n m : ℕ} (hl : m * m < n) (hr : n < (m + 1) * (m + 1)) :
    ¬∃ t, t * t = n := by
  rintro ⟨t, rfl⟩
  have h1 : m < t := Nat.mul_self_lt_mul_self_iff.mpr hl
  have h2 : t < m + 1 := Nat.mul_self_lt_mul_self_iff.mpr hr
  exact (not_lt_of_ge <| le_of_lt_succ h2) h1

theorem not_exists_sq' {n m : ℕ} (hl : m ^ 2 < n) (hr : n < (m + 1) ^ 2) : ¬∃ t, t ^ 2 = n := by
  simpa only [pow_two] using
    not_exists_sq (by simpa only [pow_two] using hl) (by simpa only [pow_two] using hr)

end Nat
