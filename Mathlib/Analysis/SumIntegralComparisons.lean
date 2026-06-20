/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

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
  values at integer steps aligning with the left-hand side of the interval.
* `AntitoneOn.sum_le_integral`: The sum of an antitone function along integer steps aligning with
  the right-hand side of the interval is at most the integral of the function along that interval
* `MonotoneOn.integral_le_sum`: The integral of a monotone function is at most the sum of its
  values at integer steps aligning with the right-hand side of the interval.
* `MonotoneOn.sum_le_integral`: The sum of a monotone function along integer steps aligning with
  the left-hand side of the interval is at most the integral of the function along that interval
* `sum_mul_Ico_le_integral_of_monotone_antitone`: the sum of `f i * g i` on an interval is bounded
  by the integral of `f x * g (x - 1)` if `f` is monotone and `g` is antitone.
* `integral_le_sum_mul_Ico_of_antitone_monotone`: the sum of `f i * g i` on an interval is bounded
  below by the integral of `f x * g (x - 1)` if `f` is antitone and `g` is monotone.

## Tags

analysis, comparison, asymptotics
-/

public section

open Set MeasureTheory MeasureSpace intervalIntegral

variable {x₀ : ℝ} {a b : ℕ} {f g : ℝ → ℝ}

lemma sum_Ico_le_integral_of_le (hab : a ≤ b)
    (h : ∀ i ∈ Ico a b, ∀ x ∈ Ico (i : ℝ) ↑(i + 1), f i ≤ g x)
    (hg : IntegrableOn g (Ico a b)) : ∑ i ∈ .Ico a b, f i ≤ ∫ x in a..b, g x := by
  have A i (hi : i ∈ Finset.Ico a b) : IntervalIntegrable g volume i ↑(i + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ico_of_le (by simp)]
    simp only [Finset.mem_Ico, ← Nat.add_one_le_iff] at hi
    rify at hi
    exact hg.mono (by grind) le_rfl
  calc
  _ = ∑ i ∈ .Ico a b, (∫ x in (i : ℝ)..↑(i + 1), f i) := by simp
  _ ≤ ∑ i ∈ .Ico a b, (∫ x in (i : ℝ)..↑(i + 1), g x) := by
    gcongr with i hi
    apply integral_mono_on_of_le_Ioo (by simp) (by simp) (A _ hi) (fun x hx ↦ ?_)
    exact h _ (by simpa using hi) _ (Ioo_subset_Ico_self hx)
  _ = _ := by rw [sum_integral_adjacent_intervals_Ico (a := (↑·)) hab]; grind

lemma integral_le_sum_Ico_of_le (hab : a ≤ b)
    (h : ∀ i ∈ Ico a b, ∀ x ∈ Ico (i : ℝ) ↑(i + 1), g x ≤ f i)
    (hg : IntegrableOn g (Ico a b)) : ∫ x in a..b, g x ≤ ∑ i ∈ .Ico a b, f i := by
  convert! neg_le_neg (sum_Ico_le_integral_of_le (f := -f) (g := -g) hab
    (fun i hi x hx ↦ neg_le_neg (h i hi x hx)) hg.neg) <;> simp

private theorem AntitoneOn.intervalIntegrable_subset (hf : AntitoneOn f (Icc x₀ (x₀ + a)))
    (k : ℕ) (hk : k + 1 ≤ a) : IntervalIntegrable f volume (x₀ + k) (x₀ + ↑(k + 1)) := by
  refine (hf.mono ?_).intervalIntegrable
  rw [uIcc_of_le (by simp)]
  apply Icc_subset_Icc <;> simp [-Nat.cast_add, hk]

theorem AntitoneOn.integral_le_sum (hf : AntitoneOn f (Icc x₀ (x₀ + a))) :
    ∫ x in x₀..x₀ + a, f x ≤ ∑ i ∈ .range a, f (x₀ + i) := calc
  _ = ∑ i ∈ .range a, ∫ x in x₀ + i..x₀ + ↑(i + 1), f x := by
    convert! (sum_integral_adjacent_intervals hf.intervalIntegrable_subset).symm
    simp
  _ ≤ ∑ i ∈ .range a, ∫ _ in x₀ + i..x₀ + ↑(i + 1), f (x₀ + i) := by
    gcongr with i hi
    rw [Finset.mem_range, ← Nat.add_one_le_iff] at hi
    have := hf.intervalIntegrable_subset _ hi
    rify at hi this ⊢
    refine integral_mono_on (by simp) this (by simp) fun _ _ ↦ by apply hf <;> grind
  _ = _ := by simp

theorem AntitoneOn.integral_le_sum_Ico (hab : a ≤ b) (hf : AntitoneOn f (Set.Icc a b)) :
    ∫ x in a..b, f x ≤ ∑ x ∈ .Ico a b, f x := by
  suffices ∫ x in a..a + ↑(b - a), f x ≤ ∑ x ∈ .Ico (0 + a) (b - a + a), f x by simp_all
  rw [← Finset.sum_Ico_add, Nat.Ico_zero_eq_range]
  suffices ∫ x in a..a + ↑(b - a), f x ≤ ∑ x ∈ .range (b - a), f (a + x) by simp_all
  exact AntitoneOn.integral_le_sum (by simp only [hf, hab, Nat.cast_sub, add_sub_cancel])

theorem AntitoneOn.sum_le_integral (hf : AntitoneOn f (Icc x₀ (x₀ + a))) :
    ∑ i ∈ .range a, f (x₀ + ↑(i + 1)) ≤ ∫ x in x₀..x₀ + a, f x := calc
  _ = ∑ i ∈ .range a, ∫ _ in x₀ + i..x₀ + ↑(i + 1), f (x₀ + ↑(i + 1)) := by simp
  _ ≤ ∑ i ∈ .range a, ∫ x in x₀ + i..x₀ + ↑(i + 1), f x := by
    gcongr with i hi
    rw [Finset.mem_range, ← Nat.add_one_le_iff] at hi
    have := hf.intervalIntegrable_subset _ hi
    rify at hi this ⊢
    exact integral_mono_on (by simp) (by simp) this fun _ _ ↦ by apply hf <;> grind
  _ = _ := by
    convert! sum_integral_adjacent_intervals hf.intervalIntegrable_subset
    simp [-Nat.cast_add]

theorem AntitoneOn.sum_le_integral_Ico (hab : a ≤ b) (hf : AntitoneOn f (Icc a b)) :
    ∑ i ∈ .Ico a b, f ↑(i + 1) ≤ ∫ x in a..b, f x := by
  suffices ∑ i ∈ .Ico (0 + a) (b - a + a), f ↑(i + 1) ≤ ∫ x in a..a + ↑(b - a), f x by simp_all
  simp_rw [← Finset.sum_Ico_add, Nat.Ico_zero_eq_range, add_assoc]
  suffices ∑ x ∈ .range (b - a), f (a + ↑(x + 1)) ≤ ∫ x in a..a + ↑(b - a), f x by simp_all
  exact AntitoneOn.sum_le_integral (by simp [hf, hab])

theorem MonotoneOn.sum_le_integral (hf : MonotoneOn f (Icc x₀ (x₀ + a))) :
    ∑ i ∈ .range a, f (x₀ + i) ≤ ∫ x in x₀..x₀ + a, f x := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.integral_le_sum

theorem MonotoneOn.sum_le_integral_Ico (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b)) :
    ∑ x ∈ .Ico a b, f x ≤ ∫ x in a..b, f x := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.integral_le_sum_Ico hab

theorem MonotoneOn.integral_le_sum (hf : MonotoneOn f (Icc x₀ (x₀ + a))) :
    ∫ x in x₀..x₀ + a, f x ≤ ∑ i ∈ .range a, f (x₀ + ↑(i + 1)) := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral

theorem MonotoneOn.integral_le_sum_Ico (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b)) :
    ∫ x in a..b, f x ≤ ∑ i ∈ .Ico a b, f ↑(i + 1) := by
  rw [← neg_le_neg_iff, ← Finset.sum_neg_distrib, ← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral_Ico hab

lemma sum_mul_Ico_le_integral_of_monotone_antitone
    (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) (hg : AntitoneOn g (Icc (a - 1) (b - 1)))
    (fpos : 0 ≤ f a) (gpos : 0 ≤ g (b - 1)) :
    ∑ i ∈ .Ico a b, f i * g i ≤ ∫ x in a..b, f x * g (x - 1) := by
  apply sum_Ico_le_integral_of_le (f := fun x ↦ f x * g x) hab
  · intro i hi x hx
    simp only [Nat.cast_add, Nat.cast_one, mem_Ico, ← Nat.add_one_le_iff] at hx hi
    rify at hi
    gcongr
    · grw [gpos]; apply hg <;> grind
    · grw [fpos]; apply hf <;> grind
    · apply hf <;> grind
    · apply hg <;> grind
  · apply Integrable.mono_measure _ (volume.restrict_mono_set Ico_subset_Icc_self)
    apply (hf.integrableOn_isCompact isCompact_Icc).mul_of_top_left
    apply AntitoneOn.memLp_isCompact isCompact_Icc
    intro _ _ _ _ _
    apply hg <;> grind

lemma integral_le_sum_mul_Ico_of_antitone_monotone
    (hab : a ≤ b) (hf : AntitoneOn f (Icc a b)) (hg : MonotoneOn g (Icc (a - 1) (b - 1)))
    (fpos : 0 ≤ f b) (gpos : 0 ≤ g (a - 1)) :
    ∫ x in a..b, f x * g (x - 1) ≤ ∑ i ∈ .Ico a b, f i * g i := by
  apply integral_le_sum_Ico_of_le (f := fun x ↦ f x * g x) hab
  · intro i hi x hx
    simp only [Nat.cast_add, Nat.cast_one, mem_Ico, ← Nat.add_one_le_iff] at hx hi
    rify at hi
    gcongr
    · grw [gpos]; apply hg <;> grind
    · grw [fpos]; apply hf <;> grind
    · apply hf <;> grind
    · apply hg <;> grind
  · apply Integrable.mono_measure _ (volume.restrict_mono_set Ico_subset_Icc_self)
    apply (hf.integrableOn_isCompact isCompact_Icc).mul_of_top_left
    apply MonotoneOn.memLp_isCompact isCompact_Icc
    intro _ _ _ _ _
    apply hg <;> grind
