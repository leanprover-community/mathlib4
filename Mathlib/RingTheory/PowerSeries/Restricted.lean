/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/

import Mathlib.Algebra.Group.NatPowAssoc
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.RCLike.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Bound

/-!
# Restricted power series

`IsRestricted` : We say a powerseries over a normed ring `R` is restricted for a parameter `c` if
`‖coeff R i f‖ * c ^ i → 0`.

-/

namespace PowerSeries

open PowerSeries Filter
open scoped Topology

/-- A power series over `R` is restricted of paramerter `c` if we have
  `‖coeff R i f‖ * c ^ i → 0`. -/
def IsRestricted {R : Type*} [NormedRing R] (c : ℝ) (f : PowerSeries R) :=
  Tendsto (fun (i : ℕ) => (norm (coeff R i f)) * c ^ i) atTop (𝓝 0)

namespace IsRestricted

variable {R : Type*} [NormedRing R] (c : ℝ)

lemma isRestricted_iff {f : PowerSeries R} : IsRestricted c f ↔
    ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ‖‖(coeff R n) f‖ * c ^ n‖ < ε := by
  simp [IsRestricted, NormedAddCommGroup.tendsto_atTop]

lemma isRestricted_iff_abs (f : PowerSeries R) : IsRestricted c f ↔ IsRestricted |c| f := by
  simp [isRestricted_iff]

lemma zero : IsRestricted c (0 : PowerSeries R) := by
  simp [IsRestricted]

lemma one : IsRestricted c (1 : PowerSeries R) := by
  simp only [isRestricted_iff, coeff_one, norm_mul, norm_pow, Real.norm_eq_abs]
  refine fun _ _ ↦ ⟨1, fun n hn => ?_ ⟩
  split
  · omega
  · simpa

lemma add {f g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f + g) := by
  simp only [isRestricted_iff, map_add, norm_mul, norm_pow, Real.norm_eq_abs] at ⊢ hf hg
  intro ε hε
  obtain ⟨fN, hfN⟩ := hf (ε / 2) (by positivity)
  obtain ⟨gN, hgN⟩ := hg (ε / 2) (by positivity)
  simp only [abs_norm] at hfN hgN ⊢
  refine ⟨max fN gN, fun n hn ↦ ?_ ⟩
  calc _ ≤ ‖(coeff R n) f‖ * |c| ^ n + ‖(coeff R n) g‖ * |c| ^ n := by grw [norm_add_le, add_mul]
       _ < ε / 2 + ε / 2 := by gcongr <;> grind
       _ = ε := by ring

lemma neg {f : PowerSeries R} (hf : IsRestricted c f) : IsRestricted c (-f) := by
  simpa [isRestricted_iff] using hf

/-- The set of `‖coeff R i f‖ * c^i` for a given power series `f` and parameter `c`. -/
def convergenceSet (f : PowerSeries R) : Set ℝ := {‖coeff R i f‖ * c^i | i : ℕ}

open Finset in
lemma convergenceSet_BddAbove {f : PowerSeries R} (hf : IsRestricted c f) :
  BddAbove (convergenceSet c f) := by
  simp_rw [isRestricted_iff] at hf
  obtain ⟨N, hf⟩ := by simpa using (hf 1)
  rw [bddAbove_def, convergenceSet]
  use max 1 (Finset.max' (Finset.image (fun i => ‖coeff R i f‖ * c^i) (range (N+1))) (by simp))
  simp only [Set.mem_setOf_eq, le_sup_iff, forall_exists_index, forall_apply_eq_imp_iff]
  intro i
  rcases le_total i N with h | h
  · right
    apply Finset.le_max'
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨i, Order.lt_add_one_iff.mpr h, rfl⟩
  · left
    calc _ ≤ ‖(coeff R i) f‖ * |c ^ i| := by bound
         _ ≤ 1 := by simpa using (hf i h).le

lemma convergenceSet_leNNeg {f : PowerSeries R} (hf : IsRestricted c f) :
    ∃ A > 0, ∀ i, ‖coeff R i f‖ * c ^ i ≤ A := by
  obtain ⟨n, hn⟩ := by simpa only [bddAbove_def] using (convergenceSet_BddAbove c hf)
  simp_rw [convergenceSet, Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hn
  rcases (eq_zero_or_neZero n) with h | h
  · exact ⟨n + 1, ⟨by aesop, fun i ↦ by linarith [hn i]⟩⟩
  · exact ⟨|n|, by aesop, fun i ↦ by linarith [hn i, le_abs_self n]⟩

variable [IsUltrametricDist R]

open IsUltrametricDist

lemma mul {f g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f * g) := by
  obtain ⟨a, ha, fBound1⟩ := convergenceSet_leNNeg |c| ((isRestricted_iff_abs c f).mp hf)
  obtain ⟨b, hb, gBound1⟩ := convergenceSet_leNNeg |c| ((isRestricted_iff_abs c g).mp hg)
  simp only [isRestricted_iff, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm,
    PowerSeries.coeff_mul] at ⊢ hf hg
  intro ε hε
  obtain ⟨Nf, fBound2⟩ := (hf (ε/ (max a b))) (div_pos hε (lt_sup_of_lt_left ha))
  obtain ⟨Ng, gBound2⟩ := (hg (ε/ (max a b))) (div_pos hε (lt_sup_of_lt_left ha))
  refine ⟨2 * max Nf Ng,  fun n hn => ?_⟩
  obtain ⟨i, hi, ultrametric⟩ := exists_norm_finset_sum_le (Finset.antidiagonal n)
    (fun a => (coeff R a.1) f * (coeff R a.2) g)
  have InterimBound1 := mul_le_mul_of_nonneg_right ultrametric (pow_nonneg (abs_nonneg c) n)
  have InterimBound2 := mul_le_mul_of_nonneg_right
    (NormedRing.norm_mul_le ((coeff R i.1) f) ((coeff R i.2) g)) (pow_nonneg (abs_nonneg c) n)
  have hi := by simpa only [Finset.mem_antidiagonal] using hi (⟨(0, n), by aesop⟩)
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

end IsRestricted
end PowerSeries
