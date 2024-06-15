/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Data.Set.Function

#align_import analysis.sum_integral_comparisons from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Comparing sums and integrals

## Summary

It is often the case that error terms in analysis can be computed by comparing
an infinite sum to the improper integral of an antitone function. This file will eventually enable
that.

At the moment it contains four lemmas in this direction: `AntitoneOn.integral_le_sum`,
`AntitoneOn.sum_le_integral` and versions for monotone functions, which can all be paired
with a `Filter.Tendsto` to estimate some errors.

`TODO`: Add more lemmas to the API to directly address limiting issues

## Main Results

* `AntitoneOn.integral_le_sum`: The integral of an antitone function is at most the sum of its
  values at integer steps aligning with the left-hand side of the interval
* `AntitoneOn.sum_le_integral`: The sum of an antitone function along integer steps aligning with
  the right-hand side of the interval is at most the integral of the function along that interval
* `MonotoneOn.integral_le_sum`: The integral of a monotone function is at most the sum of its
  values at integer steps aligning with the right-hand side of the interval
* `MonotoneOn.sum_le_integral`: The sum of a monotone function along integer steps aligning with
  the left-hand side of the interval is at most the integral of the function along that interval

## Tags

analysis, comparison, asymptotics
-/


open Set MeasureTheory.MeasureSpace

variable {x₀ : ℝ} {a b : ℕ} {f : ℝ → ℝ}

theorem AntitoneOn.integral_le_sum (hf : AntitoneOn f (Icc x₀ (x₀ + a))) :
    (∫ x in x₀..x₀ + a, f x) ≤ ∑ i ∈ Finset.range a, f (x₀ + i) := by
  have hint : ∀ k : ℕ, k < a → IntervalIntegrable f volume (x₀ + k) (x₀ + (k + 1 : ℕ)) := by
    intro k hk
    refine (hf.mono ?_).intervalIntegrable
    rw [uIcc_of_le]
    · apply Icc_subset_Icc
      · simp only [le_add_iff_nonneg_right, Nat.cast_nonneg]
      · simp only [add_le_add_iff_left, Nat.cast_le, Nat.succ_le_of_lt hk]
    · simp only [add_le_add_iff_left, Nat.cast_le, Nat.le_succ]
  calc
    ∫ x in x₀..x₀ + a, f x = ∑ i ∈ Finset.range a, ∫ x in x₀ + i..x₀ + (i + 1 : ℕ), f x := by
      convert (intervalIntegral.sum_integral_adjacent_intervals hint).symm
      simp only [Nat.cast_zero, add_zero]
    _ ≤ ∑ i ∈ Finset.range a, ∫ _ in x₀ + i..x₀ + (i + 1 : ℕ), f (x₀ + i) := by
      apply Finset.sum_le_sum fun i hi => ?_
      have ia : i < a := Finset.mem_range.1 hi
      refine intervalIntegral.integral_mono_on (by simp) (hint _ ia) (by simp) fun x hx => ?_
      apply hf _ _ hx.1
      · simp only [ia.le, mem_Icc, le_add_iff_nonneg_right, Nat.cast_nonneg, add_le_add_iff_left,
          Nat.cast_le, and_self_iff]
      · refine mem_Icc.2 ⟨le_trans (by simp) hx.1, le_trans hx.2 ?_⟩
        simp only [add_le_add_iff_left, Nat.cast_le, Nat.succ_le_of_lt ia]
    _ = ∑ i ∈ Finset.range a, f (x₀ + i) := by simp
#align antitone_on.integral_le_sum AntitoneOn.integral_le_sum

theorem AntitoneOn.integral_le_sum_Ico (hab : a ≤ b) (hf : AntitoneOn f (Set.Icc a b)) :
    (∫ x in a..b, f x) ≤ ∑ x ∈ Finset.Ico a b, f x := by
  rw [(Nat.sub_add_cancel hab).symm, Nat.cast_add]
  conv =>
    congr
    congr
    · skip
    · skip
    rw [add_comm]
    · skip
    · skip
    congr
    congr
    rw [← zero_add a]
  rw [← Finset.sum_Ico_add, Nat.Ico_zero_eq_range]
  conv =>
    rhs
    congr
    · skip
    ext
    rw [Nat.cast_add]
  apply AntitoneOn.integral_le_sum
  simp only [hf, hab, Nat.cast_sub, add_sub_cancel]
#align antitone_on.integral_le_sum_Ico AntitoneOn.integral_le_sum_Ico

theorem AntitoneOn.sum_le_integral (hf : AntitoneOn f (Icc x₀ (x₀ + a))) :
    (∑ i ∈ Finset.range a, f (x₀ + (i + 1 : ℕ))) ≤ ∫ x in x₀..x₀ + a, f x := by
  have hint : ∀ k : ℕ, k < a → IntervalIntegrable f volume (x₀ + k) (x₀ + (k + 1 : ℕ)) := by
    intro k hk
    refine (hf.mono ?_).intervalIntegrable
    rw [uIcc_of_le]
    · apply Icc_subset_Icc
      · simp only [le_add_iff_nonneg_right, Nat.cast_nonneg]
      · simp only [add_le_add_iff_left, Nat.cast_le, Nat.succ_le_of_lt hk]
    · simp only [add_le_add_iff_left, Nat.cast_le, Nat.le_succ]
  calc
    (∑ i ∈ Finset.range a, f (x₀ + (i + 1 : ℕ))) =
        ∑ i ∈ Finset.range a, ∫ _ in x₀ + i..x₀ + (i + 1 : ℕ), f (x₀ + (i + 1 : ℕ)) := by simp
    _ ≤ ∑ i ∈ Finset.range a, ∫ x in x₀ + i..x₀ + (i + 1 : ℕ), f x := by
      apply Finset.sum_le_sum fun i hi => ?_
      have ia : i + 1 ≤ a := Finset.mem_range.1 hi
      refine intervalIntegral.integral_mono_on (by simp) (by simp) (hint _ ia) fun x hx => ?_
      apply hf _ _ hx.2
      · refine mem_Icc.2 ⟨le_trans ((le_add_iff_nonneg_right _).2 (Nat.cast_nonneg _)) hx.1,
          le_trans hx.2 ?_⟩
        simp only [Nat.cast_le, add_le_add_iff_left, ia]
      · refine mem_Icc.2 ⟨(le_add_iff_nonneg_right _).2 (Nat.cast_nonneg _), ?_⟩
        simp only [add_le_add_iff_left, Nat.cast_le, ia]
    _ = ∫ x in x₀..x₀ + a, f x := by
      convert intervalIntegral.sum_integral_adjacent_intervals hint
      simp only [Nat.cast_zero, add_zero]
#align antitone_on.sum_le_integral AntitoneOn.sum_le_integral

theorem AntitoneOn.sum_le_integral_Ico (hab : a ≤ b) (hf : AntitoneOn f (Set.Icc a b)) :
    (∑ i ∈ Finset.Ico a b, f (i + 1 : ℕ)) ≤ ∫ x in a..b, f x := by
  rw [(Nat.sub_add_cancel hab).symm, Nat.cast_add]
  conv =>
    congr
    congr
    congr
    rw [← zero_add a]
    · skip
    · skip
    · skip
    rw [add_comm]
  rw [← Finset.sum_Ico_add, Nat.Ico_zero_eq_range]
  conv =>
    lhs
    congr
    congr
    · skip
    ext
    rw [add_assoc, Nat.cast_add]
  apply AntitoneOn.sum_le_integral
  simp only [hf, hab, Nat.cast_sub, add_sub_cancel]
#align antitone_on.sum_le_integral_Ico AntitoneOn.sum_le_integral_Ico

theorem MonotoneOn.sum_le_integral (hf : MonotoneOn f (Icc x₀ (x₀ + a))) :
    (∑ i ∈ Finset.range a, f (x₀ + i)) ≤ ∫ x in x₀..x₀ + a, f x := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.integral_le_sum
#align monotone_on.sum_le_integral MonotoneOn.sum_le_integral

theorem MonotoneOn.sum_le_integral_Ico (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b)) :
    ∑ x ∈ Finset.Ico a b, f x ≤ ∫ x in a..b, f x := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.integral_le_sum_Ico hab
#align monotone_on.sum_le_integral_Ico MonotoneOn.sum_le_integral_Ico

theorem MonotoneOn.integral_le_sum (hf : MonotoneOn f (Icc x₀ (x₀ + a))) :
    (∫ x in x₀..x₀ + a, f x) ≤ ∑ i ∈ Finset.range a, f (x₀ + (i + 1 : ℕ)) := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral
#align monotone_on.integral_le_sum MonotoneOn.integral_le_sum

theorem MonotoneOn.integral_le_sum_Ico (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b)) :
    (∫ x in a..b, f x) ≤ ∑ i ∈ Finset.Ico a b, f (i + 1 : ℕ) := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral_Ico hab
#align monotone_on.integral_le_sum_Ico MonotoneOn.integral_le_sum_Ico
