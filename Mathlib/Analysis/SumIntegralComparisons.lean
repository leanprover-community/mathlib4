/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Set.Function

/-!
# Comparing sums and integrals

## Summary

It is often the case that error terms in analysis can be computed by comparing
an infinite sum to the improper integral of an antitone function. This file will eventually enable
that.

At the moment it contains several lemmas in this direction, for antitone or monotone functions
(or products of antitone and monotone functions), formulated for sums on `range i` or `Ico a b`.

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
* `sum_mul_Ico_le_integral_of_monotone_antitone`: the sum of `f i * g i` on an interval is bounded
  by the integral of `f x * g (x - 1)` if `f` is monotone and `g` is antitone.
* `integral_le_sum_mul_Ico_of_antitone_monotone`: the sum of `f i * g i` on an interval is bounded
  below by the integral of `f x * g (x - 1)` if `f` is antitone and `g` is monotone.

## Tags

analysis, comparison, asymptotics
-/


open Set MeasureTheory MeasureSpace

variable {x₀ : ℝ} {a b : ℕ} {f g : ℝ → ℝ}

lemma sum_Ico_le_integral_of_le
    (hab : a ≤ b) (h : ∀ i ∈ Ico a b, ∀ x ∈ Ico (i : ℝ) (i + 1 : ℕ), f i ≤ g x)
    (hg : IntegrableOn g (Set.Ico a b)) :
    ∑ i ∈ Finset.Ico a b, f i ≤ ∫ x in a..b, g x := by
  have A i (hi : i ∈ Finset.Ico a b) : IntervalIntegrable g volume i (i + 1 : ℕ) := by
    rw [intervalIntegrable_iff_integrableOn_Ico_of_le (by simp)]
    apply hg.mono _ le_rfl
    rintro x ⟨hx, h'x⟩
    simp only [Finset.mem_Ico, mem_Ico] at hi ⊢
    exact ⟨le_trans (mod_cast hi.1) hx, h'x.trans_le (mod_cast hi.2)⟩
  calc
  ∑ i ∈ Finset.Ico a b, f i
  _ = ∑ i ∈ Finset.Ico a b, (∫ x in (i : ℝ)..(i + 1 : ℕ), f i) := by simp
  _ ≤ ∑ i ∈ Finset.Ico a b, (∫ x in (i : ℝ)..(i + 1 : ℕ), g x) := by
    gcongr with i hi
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by simp) (by simp) (A _ hi) (fun x hx ↦ ?_)
    exact h _ (by simpa using hi) _ (Ioo_subset_Ico_self hx)
  _ = ∫ x in a..b, g x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun i ↦ i) hab]
    intro i hi
    exact A _ (by simpa using hi)

lemma integral_le_sum_Ico_of_le
    (hab : a ≤ b) (h : ∀ i ∈ Ico a b, ∀ x ∈ Ico (i : ℝ) (i + 1 : ℕ), g x ≤ f i)
    (hg : IntegrableOn g (Set.Ico a b)) :
    ∫ x in a..b, g x ≤ ∑ i ∈ Finset.Ico a b, f i := by
  convert neg_le_neg (sum_Ico_le_integral_of_le (f := -f) (g := -g) hab
    (fun i hi x hx ↦ neg_le_neg (h i hi x hx)) hg.neg) <;> simp

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
      · refine mem_Icc.2 ⟨le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) hx.1,
          le_trans hx.2 ?_⟩
        simp only [Nat.cast_le, add_le_add_iff_left, ia]
      · refine mem_Icc.2 ⟨le_add_of_nonneg_right (Nat.cast_nonneg _), ?_⟩
        simp only [add_le_add_iff_left, Nat.cast_le, ia]
    _ = ∫ x in x₀..x₀ + a, f x := by
      convert intervalIntegral.sum_integral_adjacent_intervals hint
      simp only [Nat.cast_zero, add_zero]

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

theorem MonotoneOn.sum_le_integral (hf : MonotoneOn f (Icc x₀ (x₀ + a))) :
    (∑ i ∈ Finset.range a, f (x₀ + i)) ≤ ∫ x in x₀..x₀ + a, f x := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.integral_le_sum

theorem MonotoneOn.sum_le_integral_Ico (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b)) :
    ∑ x ∈ Finset.Ico a b, f x ≤ ∫ x in a..b, f x := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.integral_le_sum_Ico hab

theorem MonotoneOn.integral_le_sum (hf : MonotoneOn f (Icc x₀ (x₀ + a))) :
    (∫ x in x₀..x₀ + a, f x) ≤ ∑ i ∈ Finset.range a, f (x₀ + (i + 1 : ℕ)) := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral

theorem MonotoneOn.integral_le_sum_Ico (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b)) :
    (∫ x in a..b, f x) ≤ ∑ i ∈ Finset.Ico a b, f (i + 1 : ℕ) := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral_Ico hab

lemma sum_mul_Ico_le_integral_of_monotone_antitone
    (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) (hg : AntitoneOn g (Icc (a - 1) (b - 1)))
    (fpos : 0 ≤ f a) (gpos : 0 ≤ g (b - 1)) :
    ∑ i ∈ Finset.Ico a b, f i * g i ≤ ∫ x in a..b, f x * g (x - 1) := by
  apply sum_Ico_le_integral_of_le (f := fun x ↦ f x * g x) hab
  · intro i hi x hx
    simp only [Nat.cast_add, Nat.cast_one, mem_Ico] at hx hi
    have I0 : (i : ℝ) ≤ b - 1 := by
      simp only [le_sub_iff_add_le]
      norm_cast
      omega
    have I1 : (i : ℝ) ∈ Icc (a - 1 : ℝ) (b - 1) := by
      simp only [mem_Icc, tsub_le_iff_right]
      exact ⟨by norm_cast; cutsat, I0⟩
    have I2 : x ∈ Icc (a : ℝ) b := by
      refine ⟨le_trans (mod_cast hi.1) hx.1, hx.2.le.trans ?_⟩
      norm_cast
      omega
    apply mul_le_mul
    · apply hf
      · simp only [mem_Icc, Nat.cast_le]
        exact ⟨hi.1, hi.2.le⟩
      · exact I2
      · exact hx.1
    · apply hg
      · simp only [mem_Icc, tsub_le_iff_right, sub_add_cancel]
        refine ⟨le_trans (mod_cast hi.1) hx.1, hx.2.le.trans ?_⟩
        norm_cast
        cutsat
      · exact I1
      · simpa [sub_le_iff_le_add] using hx.2.le
    · apply gpos.trans
      apply hg I1 (by simp [hab]) I0
    · apply fpos.trans
      apply hf (by simp [hab]) I2
      exact le_trans (mod_cast hi.1) hx.1
  · apply Integrable.mono_measure _ (Measure.restrict_mono_set _ Ico_subset_Icc_self)
    apply Integrable.mul_of_top_left
    · exact hf.integrableOn_isCompact isCompact_Icc
    · apply AntitoneOn.memLp_isCompact isCompact_Icc
      intro x hx y hy hxy
      apply hg
      · simpa using hx
      · simpa using hy
      · simpa using hxy

lemma integral_le_sum_mul_Ico_of_antitone_monotone
    (hab : a ≤ b) (hf : AntitoneOn f (Icc a b)) (hg : MonotoneOn g (Icc (a - 1) (b - 1)))
    (fpos : 0 ≤ f b) (gpos : 0 ≤ g (a - 1)) :
    ∫ x in a..b, f x * g (x - 1) ≤ ∑ i ∈ Finset.Ico a b, f i * g i := by
  apply integral_le_sum_Ico_of_le (f := fun x ↦ f x * g x) hab
  · intro i hi x hx
    simp only [Nat.cast_add, Nat.cast_one, mem_Ico] at hx hi
    have I0 : (i : ℝ) ≤ b - 1 := by
      simp only [le_sub_iff_add_le]
      norm_cast
      omega
    have I1 : (i : ℝ) ∈ Icc (a - 1 : ℝ) (b - 1) := by
      simp only [mem_Icc, tsub_le_iff_right]
      exact ⟨by norm_cast; cutsat, I0⟩
    have I2 : x ∈ Icc (a : ℝ) b := by
      refine ⟨le_trans (mod_cast hi.1) hx.1, hx.2.le.trans ?_⟩
      norm_cast
      omega
    apply mul_le_mul
    · apply hf
      · simp only [mem_Icc, Nat.cast_le]
        exact ⟨hi.1, hi.2.le⟩
      · exact I2
      · exact hx.1
    · apply hg
      · simp only [mem_Icc, tsub_le_iff_right, sub_add_cancel]
        refine ⟨le_trans (mod_cast hi.1) hx.1, hx.2.le.trans ?_⟩
        norm_cast
        cutsat
      · exact I1
      · simpa [sub_le_iff_le_add] using hx.2.le
    · apply gpos.trans
      apply hg (by simp [hab]) (by simpa using I2) (by simpa using I2.1)
    · apply fpos.trans
      apply hf ⟨mod_cast hi.1, mod_cast hi.2.le⟩ (by simpa using hab) (mod_cast hi.2.le)
  · apply Integrable.mono_measure _ (Measure.restrict_mono_set _ Ico_subset_Icc_self)
    apply Integrable.mul_of_top_left
    · exact hf.integrableOn_isCompact isCompact_Icc
    · apply MonotoneOn.memLp_isCompact isCompact_Icc
      intro x hx y hy hxy
      apply hg
      · simpa using hx
      · simpa using hy
      · simpa using hxy
