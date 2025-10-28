/-
Copyright (c) 2025 Francesco Vercellesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Vercellesi
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Log
import Mathlib.Tactic.Rify
import Mathlib.Topology.Instances.CantorSet.Basic

/-!
# Lemmas about the Ternary Cantor Set

This file proves a few properties of the ternary Cantor set.

## Main results

* `empty_interior_cantorSet`: The ternary Cantor has empty interior.
-/

/-- Numbers of the form `n / (2 * 3 ^ k)` with odd `n`.
These are dense over the reals and never in the ternary Cantor set -/
def HalfTriadic (x : ℝ) :=
  ∃ n : ℤ, ∃ k : ℕ, x = n / (2 * 3 ^ k) ∧ Int.gcd n 2 = 1

/-- Half Triadics are not in the ternary Cantor set -/
lemma half_triadic_not_in_cantorSet (x : ℝ) (h : HalfTriadic x) : x ∉ cantorSet := by
  have ⟨n, k, ⟨h₁, h₂⟩⟩ := h
  rw [h₁]
  revert n x
  induction k with
  | zero =>
    intro _ _ n h₁ h₂
    simp only [pow_zero, mul_one]
    rcases lt_trichotomy n 1 with _ | h | _
    · apply (LE.le.eq_or_lt' (by omega : n ≤ 0)).elim
      · intro a
        simp [←a] at h₂
      · intro h abs
        have : (n : ℝ) / 2 < 0 := by rify at h; linarith
        have := (cantorSet_subset_unitInterval abs).left
        linarith
    · simp [cantorSet, h]
      use 1
      simp
      exact ⟨fun _ _ _ ↦ by linarith, fun _ _ _ ↦ by linarith⟩
    · apply (LE.le.eq_or_lt' (by omega : n ≥ 2)).elim
      · intro
        simp_all
      · intro h abs
        have : (n : ℝ) / 2 > 1 := by rify at h; linarith
        have := (cantorSet_subset_unitInterval abs).right
        linarith
  | succ k ih =>
    conv at ih =>
      intro _ _ _ h
      rw [←h]
    intro x hx n h₁ h₂
    rw [←h₁]
    let p₀ := x * 3
    let p₁ := x * 3 - 2
    have abs₀ := by
      refine ih p₀ ?_ n ?g1 ?g2
      use n, k
      refine ⟨?g3, ?g4⟩
      case g1 | g3 =>
        simp only [p₀, h₁]
        ring_nf
      case g2 | g4 =>
        assumption
    have abs₁ := by
      refine ih p₁ ?_ (n - 4 * (3 ^ k)) ?g1 ?g2
      use (n - 4 * (3 ^ k)), k
      refine ⟨?g3, ?g4⟩
      case g1 | g3 =>
        simp [p₁, h₁]
        field_simp
        ring_nf
      case g2 | g4 =>
        rw [←h₂]
        apply Int.gcd_sub_right_left_of_dvd
        omega
    intro abs
    exact (cantorSet_scaled_mem abs).elim abs₀ abs₁

/-- Half Triadics are dense over the reals -/
lemma triadic_dense : Dense HalfTriadic := by
  apply dense_of_exists_between
  intro a b h
  rw [←sub_pos] at h
  have big_k {x : ℝ} : x > 0 → ∃ k : ℕ, 1 / (3 ^ k) < x := by
    intro h
    use (Int.log 3 (1 / x) + 1).toNat
    calc
      _ = 1 / (3 : ℝ) ^ ((Int.log 3 (1 / x) + 1).toNat : ℤ) := by rfl
      _ ≤ 1 / (3 : ℝ) ^ (Int.log 3 (1 / x) + 1) := by
        rw [←one_div_zpow, ←one_div_zpow]
        apply (zpow_le_zpow_iff_right_of_lt_one₀ (by linarith) (by linarith)).mpr
        exact Int.self_le_toNat _
      _ < 1 / (1 / x) := by
        apply one_div_lt_one_div_of_lt
        · exact one_div_pos.mpr h
        · apply Int.lt_zpow_succ_log_self (by norm_cast)
      _ = _ := by simp
  have ⟨k, hk⟩ := big_k h
  let n := ⌊(a * (2 * 3 ^ k) - 1) / 2⌋ + 1
  use (2 * n + 1) / (2 * 3 ^ k)
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨2 * n + 1, k, by simp⟩
  · simp only [Int.cast_add, Int.cast_one, n]
    apply (lt_div_iff₀ (by norm_cast; simp : ((2 : ℝ) * 3 ^ k) > 0)).mpr
    ring_nf
    calc
      _ > (3 : ℝ) + (-1 / 2 + a * 3 ^ k - 1) * 2 := by simp
      _ ≥ _ := by ring_nf; simp
  · have : (2 * n + 1) / (2 * 3 ^ k) - a < b - a := calc
      _ ≤ 1 / (3 ^ k) := by
        simp only [Int.cast_add, Int.cast_one, n]
        rw [OrderedSub.tsub_le_iff_right]
        apply (div_le_iff₀ (by norm_cast; simp : ((2 : ℝ) * 3 ^ k) > 0)).mpr
        ring_nf
        calc
          _ ≤ 3 + (-1 / 2 + a * 3 ^ k) * 2 := by
            simp
            exact Int.floor_le _
          _ ≤ _ := by simp; ring_nf; simp
      _ < _ := hk
    simp_all

/-- The ternary Cantor has empty interior -/
theorem empty_interior_cantorSet : interior cantorSet = ∅ := by
  apply interior_eq_empty_iff_dense_compl.mpr
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  calc
    _ ⊇ _ := closure_mono half_triadic_not_in_cantorSet
    _ = _ := dense_iff_closure_eq.mp triadic_dense
