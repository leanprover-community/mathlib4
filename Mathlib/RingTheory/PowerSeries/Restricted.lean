/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/

import Mathlib.Algebra.Group.NatPowAssoc
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.RCLike.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Restricted power series

We say a powerseries over a normed ring `R` is restricted for a parameter `c` if
`‖coeff R i f‖ * c^i → 0`.

-/

namespace PowerSeries

open PowerSeries Filter
open scoped Topology

/-- A power series over `R` is restricted of paramerter `c` if we have the following limit. -/
def IsRestricted {R : Type*} [NormedRing R] (c : ℝ) (f : PowerSeries R) :=
  Tendsto (fun (i : ℕ) => (norm (coeff R i f)) * c^i) atTop (𝓝 0)

namespace Restricted

variable {R : Type*} [NormedRing R] (c : ℝ)

lemma isRestricted_iff (f : PowerSeries R) : IsRestricted c f ↔ IsRestricted |c| f := by
  simp_rw [IsRestricted, NormedAddCommGroup.tendsto_atTop, sub_zero, norm_mul, norm_norm, norm_pow,
    Real.norm_eq_abs, abs_abs]

lemma zero : IsRestricted c (0 : PowerSeries R) := by
  simp_rw [IsRestricted, map_zero, norm_zero, zero_mul, tendsto_const_nhds_iff]

lemma one : IsRestricted c (1 : PowerSeries R) := by
  simp_rw [IsRestricted, coeff_one, NormedAddCommGroup.tendsto_atTop, sub_zero, norm_mul, norm_norm,
    norm_pow, Real.norm_eq_abs]
  intro ε hε
  refine ⟨1, fun n hn => ?_ ⟩
  split
  · next h =>
    by_contra
    rw [h] at hn
    exact Nat.not_succ_le_zero 0 hn
  simpa only [norm_zero, zero_mul]

lemma add {f g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f + g) := by
  simp only [IsRestricted, map_add, NormedAddCommGroup.tendsto_atTop] at hf hg ⊢
  intro ε hε
  obtain ⟨fN, hfN⟩ := hf (ε/2) (half_pos hε)
  obtain ⟨gN, hgN⟩ := hg (ε/2) (half_pos hε)
  simp only [sub_zero, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm] at hfN hgN
  refine ⟨max fN gN, fun n hn => ?_ ⟩
  simp only [sub_zero, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm]
  exact lt_of_le_of_lt  (by simpa only [right_distrib] using (mul_le_mul_of_nonneg_right
    (norm_add_le (coeff R n f) (coeff R n g)) (pow_nonneg (abs_nonneg c) n)))
    (by simpa only [add_halves] using (add_lt_add (hfN n (le_of_max_le_left hn))
    (hgN n (le_of_max_le_right hn))))

lemma neg {f : PowerSeries R} (hf : IsRestricted c f) : IsRestricted c (-f) := by
  simpa only [IsRestricted, map_neg, norm_neg] using hf

/-- The set of `‖coeff R i f‖ * c^i` for a given power series `f` and parameter `c`. -/
def convergenceSet (f : PowerSeries R) : Set ℝ :=
  {‖coeff R i f‖ * c^i | i : ℕ}

lemma BddAbove {f : PowerSeries R} (hf : IsRestricted c f) : BddAbove (convergenceSet c f) := by
  simp_rw [IsRestricted, NormedAddCommGroup.tendsto_atTop] at hf
  obtain ⟨N, hf⟩ := by simpa only [zero_lt_one, sub_zero, norm_mul, norm_norm, norm_pow,
    Real.norm_eq_abs, forall_const, abs_norm] using (hf 1)
  simp_rw [bddAbove_def, convergenceSet]
  use max 1 (Finset.max' (Finset.image (fun i => ‖coeff R i f‖ * c^i) (Finset.range (N+1)))
    (by simp only [Finset.image_nonempty, Finset.nonempty_range_iff, ne_eq,
    AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
    not_false_eq_true]))
  simp only [Set.mem_setOf_eq, le_sup_iff, forall_exists_index, forall_apply_eq_imp_iff]
  intro i
  rcases (Nat.le_total i N) with h | h
  · right
    apply Finset.le_max'
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨i, by exact Order.lt_add_one_iff.mpr h, rfl⟩
  · exact Or.inl (le_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (by simpa only [abs_pow] using le_abs_self (c ^ i)) (norm_nonneg _)) (hf i h)))

lemma BddAbove_nneg {f : PowerSeries R} (hf : IsRestricted c f) :
     ∃ A, A > 0 ∧ ∀ i, ‖coeff R i f‖ * c^i ≤ A := by
  obtain ⟨n, hn⟩ := by simpa only [bddAbove_def] using (BddAbove c hf)
  simp_rw [convergenceSet, Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hn
  rcases (eq_zero_or_neZero n) with h | h
  · refine ⟨n + 1, ⟨by simp_rw [h, zero_add, gt_iff_lt, zero_lt_one], fun i => le_trans (hn i)
    (by simp_rw [h, zero_add, zero_le_one])⟩⟩
  · exact ⟨|n|, by simpa only [gt_iff_lt, abs_pos] using Ne.symm (NeZero.ne' n),
    fun i => le_trans (hn i) (le_abs_self n)⟩

variable [IsUltrametricDist R]

open IsUltrametricDist

lemma mul {f g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f * g) := by
  simp_rw [IsRestricted] at hf hg ⊢
  obtain ⟨a, ha, fBound1⟩ := BddAbove_nneg |c| ((isRestricted_iff c f).mp hf)
  obtain ⟨b, hb, gBound1⟩ := BddAbove_nneg |c| ((isRestricted_iff c g).mp hg)
  rw [NormedAddCommGroup.tendsto_atTop] at hf hg ⊢
  intro ε hε
  simp only [sub_zero, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm] at hf hg ⊢
  simp_rw [PowerSeries.coeff_mul]
  obtain ⟨Nf, fBound2⟩ := (hf (ε/ (max a b))) (div_pos hε (lt_sup_of_lt_left ha))
  obtain ⟨Ng, gBound2⟩ := (hg (ε/ (max a b))) (div_pos hε (lt_sup_of_lt_left ha))
  refine ⟨2 * max Nf Ng,  fun n hn => ?_⟩
  obtain ⟨i, hi, ultrametric⟩ := exists_norm_finset_sum_le (Finset.antidiagonal n)
    (fun a => (coeff R a.1) f * (coeff R a.2) g)
  have hi := by simpa only [Finset.mem_antidiagonal] using hi (⟨(0,n), by simp only
    [Finset.mem_antidiagonal, zero_add]⟩)
  have InterimBound1 := mul_le_mul_of_nonneg_right ultrametric (pow_nonneg (abs_nonneg c) n)
  have InterimBound2 := mul_le_mul_of_nonneg_right
    (NormedRing.norm_mul_le ((coeff R i.1) f) ((coeff R i.2) g)) (pow_nonneg (abs_nonneg c) n)
  have : ‖(coeff R i.1) f‖ * ‖(coeff R i.2) g‖ * |c|^n =
      ‖(coeff R i.1) f‖ * |c|^i.1 * (‖(coeff R i.2) g‖ * |c|^i.2) := by
    ring_nf
    simp_rw [mul_assoc, ← npow_add, hi]
  simp only [this] at InterimBound2
  have : i.1 ≥ max Nf Ng ∨ i.2 ≥ max Nf Ng := by
    omega
  rcases this with this | this
  · have FinalBound := mul_lt_mul_of_lt_of_le_of_nonneg_of_pos ((fBound2 i.1)
      (le_of_max_le_left this)) (gBound1 i.2) (Left.mul_nonneg (norm_nonneg ((coeff R i.1) f))
      (pow_nonneg (abs_nonneg c) i.1)) hb
    exact lt_of_lt_of_le (lt_of_le_of_lt (le_trans InterimBound1 InterimBound2) FinalBound)
      (by simpa only [div_mul_comm] using ((mul_le_iff_le_one_left hε).mpr
      ((div_le_one₀ (lt_sup_of_lt_left ha)).mpr (le_max_right a b))))
  · have FinalBound := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (fBound1 i.1) ((gBound2 i.2)
      (le_of_max_le_right this)) (Left.mul_nonneg (norm_nonneg ((coeff R i.2) g))
      (pow_nonneg (abs_nonneg c) i.2)) ha
    exact lt_of_lt_of_le (lt_of_le_of_lt (le_trans InterimBound1 InterimBound2) FinalBound)
      (by simpa only [mul_div_left_comm] using ((mul_le_iff_le_one_right hε).mpr
      ((div_le_one₀ (lt_sup_of_lt_left ha)).mpr (le_max_left a b))))

end Restricted
end PowerSeries
