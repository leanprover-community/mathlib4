/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Functional equations for L-functions on `ZMod N`
-/

open HurwitzZeta Complex ZMod Finset Classical

open scoped Real

namespace ZMod

variable {N : ℕ} [NeZero N]

lemma gammaFactor_dft {Φ : ZMod N → ℂ} : gammaFactor (𝓕 Φ) = gammaFactor Φ :=
  funext fun s ↦ by simp only [gammaFactor, ← dft_even]

/-- The `L`-function of the Fourier transform of `Φ`. -/
noncomputable def dualLFunction (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  ∑ j : ZMod N, Φ j * expZeta (toAddCircle (-j)) s

/-- Completed version of `dualLFunction Φ s`. -/
noncomputable def completedDualLFunction (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  if Φ.Even then ∑ j : ZMod N, Φ j * completedCosZeta (toAddCircle j) s
    else ∑ j : ZMod N, Φ j / I * completedSinZeta (toAddCircle j) s

lemma dualLFunction_def_signed {Φ : ZMod N → ℂ} (hΦ : Φ.Even ∨ Φ.Odd) (s : ℂ) :
    dualLFunction Φ s =
      if Φ.Even then ∑ j : ZMod N, Φ j * cosZeta (toAddCircle j) s
        else ∑ j : ZMod N, Φ j / I * sinZeta (toAddCircle j) s := by
  simp only [dualLFunction, ← mul_ite, expZeta, mul_add, sum_add_distrib]
  by_cases h : Φ.Even
  · simp only [map_neg, cosZeta_neg, sinZeta_neg, h, ↓reduceIte, add_right_eq_self, ←
    neg_eq_self ℂ, ← sum_neg_distrib]
    refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
    simp only [mul_neg, Equiv.neg_apply, h i, map_neg, sinZeta_neg]
  · have h' : Φ.Odd := by tauto
    simp only [map_neg, cosZeta_neg, sinZeta_neg, mul_neg, ← mul_assoc, ← sum_neg_distrib, h,
      ↓reduceIte, div_I, neg_mul, add_left_eq_self, ← neg_eq_self ℂ]
    refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
    simp only [Equiv.neg_apply, h' i, map_neg, cosZeta_neg, neg_mul]

lemma dualLFunction_eq_completed_div_gammaFactor {Φ : ZMod N → ℂ} (hΦ : Φ.Even ∨ Φ.Odd) (s : ℂ)
    (h : s ≠ 0 ∨ ∑ i, Φ i = 0) :
    dualLFunction Φ s = completedDualLFunction Φ s / gammaFactor Φ s := by
  rw [dualLFunction_def_signed hΦ, completedDualLFunction, gammaFactor]
  split_ifs with h' <;> simp only [sum_div, mul_div_assoc, cosZeta, sinZeta]
  rcases eq_or_ne s 0 with rfl | hs
  · simp only [Function.update_same, Gammaℝ, zero_div, Gamma_zero, mul_zero, div_zero,
      sum_const_zero, ← sum_mul, h.neg_resolve_left rfl, zero_mul]
  · simp only [Function.update_noteq (by tauto)]

/-- General form of functional equation (allowing non-primitive characters): equality between
`completedLFunction` at `1 - s` and `completedDualLFunction` at `s`. -/
lemma completedLFunction_one_sub_eq_dual (Φ : ZMod N → ℂ) (s : ℂ) :
    completedLFunction Φ (1 - s) =
      N ^ (s - 1) * I ^ (if Φ.Even then 0 else 1) * completedDualLFunction Φ s := by
  rw [completedLFunction, completedDualLFunction, neg_sub]
  split_ifs
  · simp only [completedHurwitzZetaEven_one_sub, pow_zero, mul_one]
  · simp only [completedHurwitzZetaOdd_one_sub, pow_one, mul_assoc, mul_sum _ _ I, ← mul_assoc I,
      mul_div_cancel₀ _ I_ne_zero]

/--
If `Φ 0 = 0` and `∑ i, Φ i = 0`, then the dual completed L-function is differentiable everywhere.
-/
lemma differentiableAt_completedDualLFunction (Φ : ZMod N → ℂ) (s : ℂ)
    (hΦs : s ≠ 0 ∨ ∑ i, Φ i = 0) (hΦs' : s ≠ 1 ∨ Φ 0 = 0) :
    DifferentiableAt ℂ (completedDualLFunction Φ) s := by
  unfold completedDualLFunction
  split_ifs
  · simp only [completedCosZeta_eq, mul_sub, sum_sub_distrib]
    refine (DifferentiableAt.sub ?_ ?_).sub ?_
    · exact (Differentiable.sum fun i _ ↦ (differentiable_completedCosZeta₀ _).const_mul _) s
    · rcases hΦs with h | h
      · simp only [mul_one_div, ← sum_div]
        exact (differentiableAt_const _).div differentiableAt_id h
      · simp only [← sum_mul, h, zero_mul, differentiableAt_const]
    · rcases hΦs' with h | h
      · simp only [← mul_div_assoc, ← sum_div]
        refine (differentiableAt_const _).div ?_ ?_
        · exact (differentiableAt_const _).sub differentiableAt_id
        · rwa [sub_ne_zero, ne_comm]
      · simp only [toAddCircle_eq_zero, div_eq_mul_inv, ite_mul, one_mul, zero_mul, mul_ite,
          mul_zero, sum_ite_eq', mem_univ, ↓reduceIte, h, differentiableAt_const]
  · exact (Differentiable.sum fun i _ ↦ (differentiable_completedSinZeta _).const_mul _) _

/-- If the modulus is `≠ 1`, then `dualLFunction Φ` is differentiable. -/
lemma differentiable_dualLFunction {Φ : ZMod N → ℂ} (hΦ' : Φ 0 = 0) :
    Differentiable ℂ (dualLFunction Φ) := by
  refine Differentiable.sum fun j _ ↦ ?_
  rcases eq_or_ne j 0 with rfl | hj
  · simp only [hΦ', zero_mul, differentiable_const]
  · refine (differentiable_expZeta_of_ne_zero fun h ↦ hj ?_).const_mul _
    rwa [← (toAddCircle (N := N)).map_zero, (toAddCircle_injective _).eq_iff, neg_eq_zero] at h

/--
On the half-space `1 < re s`, the dual L-function of `Φ` is equal to the L-function of `𝓕 Φ (-x).
-/
lemma dualLFunction_eq_LSeries_dft (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
    dualLFunction Φ s = LSeries (𝓕 Φ ·) s := by
  rw [dualLFunction, dft_def]
  simp only [toAddCircle_apply, ← fun a ↦ (LSeriesHasSum_exp a hs).LSeries_eq, LSeries,
    ← tsum_mul_left]
  rw [← tsum_sum (fun i _ ↦ Summable.mul_left _ (LSeriesHasSum_exp _ hs).LSeriesSummable)]
  congr 1 with n
  simp only [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), ← mul_div_assoc, ← sum_div,
    Submonoid.smul_def, smul_eq_mul, mul_comm _ (Φ _), mul_neg, neg_neg]
  congr 2 with i
  rw [mul_comm _ (n : ℂ), exp_nat_mul, ofReal_div, ofReal_natCast, ofReal_natCast,
    ← mul_div_assoc, ← toCircle_apply, mul_comm _ (n : ZMod N), ← nsmul_eq_mul, ← neg_nsmul,
    AddChar.map_nsmul_eq_pow, stdAddChar_apply]

/--
First step towards functional equation: prove equality of dual L-series with L-series of `Φ⁻¹`
in convergence range. Private because it is superseded by `dualLFunction_eq` below.
-/
private lemma dualLFunction_eq_of_one_lt (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
    dualLFunction Φ s = LFunction (𝓕 Φ) s := by
  simp only [dualLFunction_eq_LSeries_dft _ hs, LFunction_eq_LSeries _ hs]

/--
Second step towards functional equation: prove equality of completed dual L-series with completed
L-series of `Φ⁻¹` in convergence range. Private because it is superseded by
`completedDualLFunction_eq` below.
-/
private lemma completedDualLFunction_eq_of_one_lt {Φ : ZMod N → ℂ} (hΦ : Φ.Even ∨ Φ.Odd)
    {s : ℂ} (hs : 1 < re s) :
    completedDualLFunction Φ s = completedLFunction (𝓕 Φ) s := by
  have h := dualLFunction_eq_of_one_lt Φ hs
  rwa [dualLFunction_eq_completed_div_gammaFactor hΦ, LFunction_eq_completed_div_gammaFactor,
    gammaFactor_dft, div_left_inj'] at h
  · rw [gammaFactor] -- remains to show gammaFactor ≠ 0
    split_ifs <;>
    apply Gammaℝ_ne_zero_of_re_pos <;>
    [skip; rw [add_re, one_re]] <;>
    positivity
  · simpa only [← dft_even, ← dft_odd] using hΦ
  all_goals exact Or.inl (Complex.ne_zero_of_one_lt_re hs)

/--
The completed dual L-function of `Φ` is the completed L-function of its Fourier transform.
-/
lemma completedDualLFunction_eq {Φ : ZMod N → ℂ} (hΦ : Φ.Even ∨ Φ.Odd)
    (s : ℂ) (hΦs : s ≠ 0 ∨ ∑ i, Φ i = 0) (hΦs' : s ≠ 1 ∨ Φ 0 = 0) :
    completedDualLFunction Φ s = completedLFunction (𝓕 Φ) s := by
  revert s
  let U : Set ℂ := fun s ↦ (s ≠ 0 ∨ ∑ i, Φ i = 0) ∧ (s ≠ 1 ∨ Φ 0 = 0)
  have hUo : IsOpen U := by
    apply IsOpen.inter
    · by_cases h : ∑ i, Φ i = 0
      · simpa only [eq_true_intro h, or_true] using isOpen_univ
      · simpa only [eq_false_intro h, or_false] using isOpen_compl_iff.mpr isClosed_singleton
    · by_cases h : Φ 0 = 0
      · simpa only [eq_true_intro h, or_true] using isOpen_univ
      · simpa only [eq_false_intro h, or_false] using isOpen_compl_iff.mpr isClosed_singleton
  suffices U.EqOn _ _ from fun s hs hs' ↦ this <| Set.mem_setOf.mpr ⟨hs, hs'⟩
  apply AnalyticOn.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) (z₀ := 2)
  · constructor <;> norm_num
  · apply Filter.eventuallyEq_of_mem ?_ fun s hs ↦ completedDualLFunction_eq_of_one_lt hΦ hs
    · apply (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      simp only [Set.mem_preimage, re_ofNat, Set.mem_Ioi, Nat.one_lt_ofNat]
  · refine DifferentiableOn.analyticOn (fun s hs ↦ ?_) hUo
    exact (differentiableAt_completedDualLFunction _ _ hs.1 hs.2).differentiableWithinAt
  · refine DifferentiableOn.analyticOn (fun s hs ↦ ?_) hUo
    refine (differentiableAt_completedLFunction ?_ s ?_ ?_).differentiableWithinAt
    · rwa [← dft_even, ← dft_odd]
    · simp only [dft_def, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
      exact hs.1
    · refine hs.2.imp (by tauto) (fun hΦ ↦ ?_)
      have := congr_fun (dft_dft Φ) 0
      rw [neg_zero, hΦ, smul_zero, dft_def] at this
      simpa only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
  · change IsPreconnected ({s | (s ≠ 0 ∨ ∑ i : ZMod N, Φ i = 0)} ∩ {s  | s ≠ 1 ∨ Φ 0 = 0})
    suffices IsPreconnected ({s : ℂ | s = 0 ∧ ∑ i : ZMod N, Φ i ≠ 0} ∪
        {s : ℂ | s = 1 ∧ Φ 0 ≠ 0})ᶜ by
      rw [Set.compl_union, Set.compl_def, Set.compl_def] at this
      convert this using 1
      refine Set.ext fun x ↦ ?_
      simp only [Set.mem_setOf, not_and_or, ne_eq, not_not]
    apply IsConnected.isPreconnected
    apply Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
    apply Set.Countable.union
    · apply Set.Countable.mono (s₂ := {0}) <;> simp
    · apply Set.Countable.mono (s₂ := {1}) <;> simp

/--
The dual L-function of a primitive character is the L-function of its inverse.
-/
lemma dualLFunction_eq {Φ : ZMod N → ℂ} (hΦ : Φ.Even ∨ Φ.Odd) (s : ℂ)
    (hΦs : s ≠ 0 ∨ ∑ i, Φ i = 0) (hΦs' : s ≠ 1 ∨ Φ 0 = 0) :
    dualLFunction Φ s = LFunction (𝓕 Φ) s := by
  rw [dualLFunction_eq_completed_div_gammaFactor hΦ _ hΦs,
    LFunction_eq_completed_div_gammaFactor (by simpa [← dft_odd, ← dft_even] using hΦ),
    completedDualLFunction_eq hΦ _ hΦs hΦs', gammaFactor_dft]
  simp only [dft_def, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
  exact hΦs

lemma completedLFunction_one_sub_eq {Φ : ZMod N → ℂ} (hΦ : Φ.Even ∨ Φ.Odd)
    (s : ℂ) (hΦs : s ≠ 0 ∨ ∑ i, Φ i = 0) (hΦs' : s ≠ 1 ∨ Φ 0 = 0) :
    completedLFunction Φ (1 - s) =
      ↑N ^ (s - 1) * I ^ (if Function.Even Φ then 0 else 1) * completedLFunction (𝓕 Φ) s := by
  rw [completedLFunction_one_sub_eq_dual, completedDualLFunction_eq hΦ _ hΦs hΦs', mul_assoc]

end ZMod
