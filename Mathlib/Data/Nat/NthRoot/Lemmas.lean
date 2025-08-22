/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Nat.NthRoot.Defs
import Mathlib.Tactic.Rify

/-!
# Lemmas about `Nat.nthRoot`

In this file we prove that `Nat.nthRoot n a` is indeed the floor of `ⁿ√a`.

## TODO

Rewrite proofs to avoid dependencies on real numbers,
so that we can move this file to Batteries.
-/

namespace Nat

@[simp] theorem nthRoot_zero_left (a : ℕ) : nthRoot 0 a = 1 := rfl

@[simp] theorem nthRoot_one_left : nthRoot 1 = id := rfl

theorem nthRoot.pow_go_le (n a b : ℕ) : (go n a b) ^ (n + 2) ≤ a := by
  induction b using Nat.strongRecOn with
  | ind b ihb =>
    rw [go]
    split_ifs with h
    case pos =>
      exact ihb _ h
    case neg =>
      have : b ≤ a / b^(n + 1) := by linarith only [Nat.mul_le_of_le_div _ _ _ (not_lt.1 h)]
      replace := Nat.mul_le_of_le_div _ _ _ this
      rwa [← Nat.pow_succ'] at this

variable {n a b : ℕ}

theorem nthRoot.lt_pow_go_succ_aux (h : a < b ^ (n + 1)) :
    a < ((a / b ^ n + n * b) / (n + 1) + 1) ^ (n + 1) := by
  rcases eq_or_ne b 0 with rfl | hb; · simp at h
  rcases Nat.eq_zero_or_pos n with rfl | hn; · simp
  rw [← Nat.add_mul_div_left a, Nat.div_div_eq_div_mul] <;> try positivity
  rify
  calc
    (a : ℝ) = ((a / b ^ n) ^ (1 / (n + 1) : ℝ) * b ^ (n / (n + 1) : ℝ)) ^ (n + 1) := by
      rw [mul_pow, ← Real.rpow_mul_natCast, ← Real.rpow_mul_natCast] <;> try positivity
      field_simp
    _ ≤ ((1 / (n + 1)) * (a / b ^ n) + (n / (n + 1)) * b) ^ (n + 1) := by
      gcongr
      apply Real.geom_mean_le_arith_mean2_weighted <;> try positivity
      field_simp [add_comm]
    _ = ((a + b ^ n * (n * b)) / (b ^ n * (n + 1))) ^ (n + 1) := by
      congr 1
      field_simp
      ring
    _ < _ := by
      gcongr ?_ ^ _
      convert lt_floor_add_one (R := ℝ) _ using 1
      norm_cast
      rw [Nat.floor_div_natCast, Nat.floor_natCast]

theorem nthRoot.lt_pow_go_succ (hb : a < (b + 1) ^ (n + 2)) : a < (go n a b + 1) ^ (n + 2) := by
  induction b using Nat.strongRecOn with
  | ind b ihb =>
    rw [go]
    split_ifs with h
    case pos =>
      rcases eq_or_ne b 0 with rfl | hb
      · simp at *
      apply ihb _ h
      replace h : a < b ^ (n + 2) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)] at h
        replace h : a / b ^ (n + 1) < b := by linarith only [h]
        rwa [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_succ'] at h
      exact Nat.nthRoot.lt_pow_go_succ_aux h
    case neg =>
      assumption

theorem pow_nthRoot_le (hn : n ≠ 0) (a : ℕ) : (nthRoot n a) ^ n ≤ a := by
  match n, hn with
  | 1, _ => simp
  | n + 2, _ =>
    simp only [nthRoot]
    split_ifs with h
    case pos => interval_cases a <;> simp
    case neg => apply nthRoot.pow_go_le

theorem lt_pow_nthRoot_add_one (hn : n ≠ 0) (a : ℕ) : a < (nthRoot n a + 1) ^ n := by
  match n, hn with
  | 1, _ => simp
  | n + 2, hn =>
    simp only [nthRoot]
    split_ifs with h
    case pos => interval_cases a <;> simp
    case neg =>
      apply nthRoot.lt_pow_go_succ
      exact a.lt_succ_self.trans_le (Nat.le_self_pow hn _)

@[simp]
theorem le_nthRoot_iff (hn : n ≠ 0) : a ≤ nthRoot n b ↔ a ^ n ≤ b := by
  cases le_or_gt a (nthRoot n b) with
  | inl hle =>
    simp only [hle, true_iff]
    refine le_trans ?_ (pow_nthRoot_le hn b)
    gcongr
  | inr hlt =>
    simp only [hlt.not_ge, false_iff, not_le]
    refine (lt_pow_nthRoot_add_one hn b).trans_le ?_
    gcongr
    assumption

@[simp]
theorem nthRoot_lt_iff (hn : n ≠ 0) : nthRoot n a < b ↔ a < b ^ n := by
  simp only [← not_le, le_nthRoot_iff hn]

@[simp]
theorem nthRoot_pow (hn : n ≠ 0) (a : ℕ) : nthRoot n (a ^ n) = a := by
  refine eq_of_forall_le_iff fun b ↦ ?_
  rw [le_nthRoot_iff hn]
  exact (Nat.pow_left_strictMono hn).le_iff_le

theorem nthRoot_eq_of_le_of_lt (h₁ : a ^ n ≤ b) (h₂ : b < (a + 1) ^ n) :
    nthRoot n b = a := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero] at *; omega
  simp only [← le_nthRoot_iff hn, ← nthRoot_lt_iff hn] at h₁ h₂
  omega

theorem exists_pow_eq_iff' (hn : n ≠ 0) : (∃ x, x ^ n = a) ↔ (nthRoot n a) ^ n = a := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [nthRoot_pow hn]
  · exact fun h ↦ ⟨_, h⟩

theorem exists_pow_eq_iff :
    (∃ x, x ^ n = a) ↔ ((n = 0 ∧ a = 1) ∨ (n ≠ 0 ∧ (nthRoot n a) ^ n = a)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [eq_comm]
  · simp [exists_pow_eq_iff', hn]

instance instDecidableExistsPowEq : Decidable (∃ x, x ^ n = a) :=
  decidable_of_iff' _ exists_pow_eq_iff

end Nat
