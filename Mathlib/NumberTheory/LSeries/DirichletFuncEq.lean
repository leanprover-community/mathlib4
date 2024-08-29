/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.LSeries.DirichletContinuation2
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Functional equations of Dirichlet L-functions

We show that the completed `L`-functions of Dirichlet characters satisfy functional equations
relating `s` and `1 - s`.

## Brief outline of construction

We define a function `dualLFunction χ s`, and a variant `completedDualLFunction χ s` given
by multiplying by a Gamma factor in the usual way. We show that
- `completedLFunction χ (1 - s) = □ * completedDualLFunction χ s` for an explicit factor `□`,
- `dualLFunction χ s` is the analytic continuation of the Dirichlet series with coefficients
  `gaussSum χ (stdAddChar.mulShift n)`.

These results are valid for all `χ`. However, if `χ` is primitive, then we have
`gaussSum χ (stdAddChar.mulShift n) = gaussSum χ stdAddChar * χ⁻¹ n` and we recover the usual
formulation of the functional equation.

## Main definitions and results

All definitions and theorems are in the `DirichletCharacter` namespace.

* `DirichletCharacter.rootNumber`: the global root number of the L-series of `χ`.
* `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`: if `χ` is primitive modulo `N`, then
  `completedLFunction χ s = N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s`.
-/

open HurwitzZeta Complex ZMod Finset Classical DirichletCharacter

open scoped Real

namespace DirichletContinuationOld

open DirichletContinuationOld.DirichletCharacter

variable {N : ℕ} [NeZero N]

local notation "G" χ:max => gaussSum χ stdAddChar

/-- Global root number of `χ` (for `χ` primitive; junk otherwise). Defined as
`gaussSum χ stdAddChar / I ^ a / N ^ (1 / 2)`, where `a = 0` if even, `a = 1` if odd. -/
noncomputable def rootNumber (χ : DirichletCharacter ℂ N) : ℂ :=
  G χ / I ^ (if χ.Even then 0 else 1) / N ^ (1 / 2 : ℂ)

lemma gaussSum_mod_one {R : Type*} [CommRing R] (χ : DirichletCharacter R 1)
    (e : AddChar (ZMod 1) R) :
    gaussSum χ e = 1 := by
  rw [gaussSum, univ_unique, sum_singleton]
  change χ 1 * e 0 = 1
  rw [map_one, AddChar.map_zero_eq_one, one_mul]

lemma gammaFactor_inv {N : ℕ} (χ : DirichletCharacter ℂ N) :
    gammaFactor χ⁻¹ = gammaFactor χ := by
  unfold gammaFactor
  rw [show χ⁻¹.Even ↔ χ.Even by
    simp only [DirichletCharacter.Even, χ.inv_apply_eq_inv', inv_eq_one]]

/-- "Dual" L-function of a Dirichlet character.

This is a meromorphic function which we show is equal to `L χ (1 - s)` up to the usual Gamma
factors, and is also equal to the sum of the Dirichlet series with `n`-th term
`gaussSum χ (stdAddChar.mulShift n)`.

When `χ` is primitive we shall show that this is equal to `L χ⁻¹ s` (but the
definition is valid more generally). -/
noncomputable def dualLFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑ j : ZMod N, χ j * expZeta (toAddCircle j) s

lemma dualLFunction_mod_one (χ : DirichletCharacter ℂ (1 : ℕ+)) :
    dualLFunction χ = riemannZeta := by
  ext s : 1
  simp only [dualLFunction, PNat.val_ofNat, univ_unique, sum_singleton]
  change χ 1 * expZeta (toAddCircle 0) s = _
  rw [map_one, map_zero, expZeta_zero, one_mul]

/-- Alternate version of the definition of `dualLFunction χ s` using sine / cosine zeta functions.
Useful for comparison with `completedDualLFunction χ s`. -/
lemma dualLFunction_def_signed (χ : DirichletCharacter ℂ N) (s : ℂ) :
    dualLFunction χ s =
      if χ.Even then ∑ j : ZMod N, χ j * cosZeta (toAddCircle j) s
        else ∑ j : ZMod N, χ j * I * sinZeta (toAddCircle j) s := by
  simp only [dualLFunction, ← mul_ite, expZeta, mul_add, sum_add_distrib]
  rcases χ.even_or_odd with h | h
  · simp only [h, ↓reduceIte, add_right_eq_self, ← neg_eq_self ℂ, ← sum_neg_distrib]
    refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
    simp only [Equiv.neg_apply, map_neg, sinZeta_neg, mul_neg]
    rw [← neg_one_mul i, map_mul, h, one_mul]
  · simp only [h.not_even, ↓reduceIte, add_left_eq_self, ← neg_eq_self ℂ,
      ← sum_neg_distrib, ← mul_assoc]
    refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
    simp only [Equiv.neg_apply, map_neg, cosZeta_neg, mul_neg]
    rw [← neg_one_mul i, map_mul, h, neg_mul, neg_mul, one_mul]

/-- Completed version of `dualLFunction χ s`. -/
noncomputable def completedDualLFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  if χ.Even then ∑ j : ZMod N, χ j * completedCosZeta (toAddCircle j) s
    else ∑ j : ZMod N, χ j * I * completedSinZeta (toAddCircle j) s

lemma completedDualLFunction_mod_one (χ : DirichletCharacter ℂ (1 : ℕ+)) :
    completedDualLFunction χ = completedRiemannZeta := by
  ext s : 1
  simp only [completedDualLFunction, PNat.val_ofNat, univ_unique, sum_singleton,
    (show χ.Even from map_one _), ↓reduceIte]
  change χ 1 * completedCosZeta (toAddCircle 0) s = _
  rw [map_one, map_zero, completedCosZeta_zero, one_mul]

lemma dualLFunction_eq_completed_div_gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ)
    (h : s ≠ 0 ∨ χ ≠ 1) :
    dualLFunction χ s = completedDualLFunction χ s / gammaFactor χ s := by
  rw [dualLFunction_def_signed, completedDualLFunction, gammaFactor]
  split_ifs with hχ <;> simp only [sum_div, mul_div_assoc, cosZeta, sinZeta]
  rcases eq_or_ne s 0 with rfl | hs
  · simp only [Function.update_same, Gammaℝ, zero_div, Gamma_zero, mul_zero, div_zero,
      sum_const_zero, ← sum_mul]
    rw [χ.sum_eq_zero_of_ne_one (by tauto), zero_mul]
  · simp only [Function.update_noteq (by tauto)]

/-- General form of functional equation (allowing non-primitive characters): equality between
`completedLFunction` at `1 - s` and `completedDualLFunction` at `s`.

See `IsPrimitive.completedLFunction_one_sub` for the more familiar form when `χ` is primitive. -/
lemma completedLFunction_one_sub_eq_dual (χ : DirichletCharacter ℂ N) (s : ℂ) :
    completedLFunction χ (1 - s) =
      N ^ (s - 1) / I ^ (if χ.Even then 0 else 1) * completedDualLFunction χ s := by
  rw [completedLFunction, completedDualLFunction, neg_sub]
  split_ifs
  · simp only [completedHurwitzZetaEven_one_sub, pow_zero, div_one]
  · rw [pow_one, div_mul_eq_mul_div, mul_div_assoc, sum_div]
    congr 2 with i
    rw [mul_right_comm, mul_div_cancel_right₀ _ I_ne_zero, completedHurwitzZetaOdd_one_sub]

/-- If `χ ≠ 1` then the dual completed L-function is differentiable everywhere. -/
lemma differentiable_completedDualLFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (completedDualLFunction χ) := by
  unfold completedDualLFunction
  split_ifs
  · simp only [completedCosZeta_eq, mul_sub, sum_sub_distrib]
    refine (Differentiable.sub ?_ ?_).sub ?_
    · exact Differentiable.sum fun i _ ↦ (differentiable_completedCosZeta₀ _).const_mul _
    · simp only [← sum_mul, χ.sum_eq_zero_of_ne_one hχ, zero_mul, differentiable_const]
    · simp only [div_eq_mul_inv, ite_mul, mul_ite]
      have (a : ZMod N) : toAddCircle a = 0 ↔ a = 0 := by
        simpa only [← (toAddCircle (N := N)).map_zero] using (toAddCircle_injective _).eq_iff
      have h : N ≠ 1 := (show χ ≠ 1 by tauto) ∘ level_one' χ
      simp only [this, ← div_eq_mul_inv, zero_div, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte,
        map_zero' _ h, zero_mul, differentiable_const]
  · exact Differentiable.sum fun i _ ↦ (differentiable_completedSinZeta _).const_mul _

/-- If the modulus is `≠ 1`, then `dualLFunction χ` is differentiable. -/
lemma differentiable_dualLFunction (χ : DirichletCharacter ℂ N) (hN : N ≠ 1) :
    Differentiable ℂ (dualLFunction χ) := by
  unfold dualLFunction
  refine Differentiable.sum fun j _ ↦ ?_
  rcases eq_or_ne j 0 with rfl | hj
  · simp only [χ.map_zero' hN, zero_mul, differentiable_const]
  · apply Differentiable.const_mul
    refine differentiable_expZeta_of_ne_zero fun h ↦ hj ?_
    rwa [← (toAddCircle (N := N)).map_zero, (toAddCircle_injective _).eq_iff] at h

/--
On the half-space `1 < re s`, the dual L-function is given by the Dirichlet series with
coefficients `gaussSum χ (stdAddChar.mulShift n)`.
-/
lemma dualLFunction_eq_LSeries_gaussSum (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < re s) :
    dualLFunction χ s = LSeries (fun n ↦ gaussSum χ (stdAddChar.mulShift n)) s := by
  rw [dualLFunction]
  have (a : ℝ) := (LSeriesHasSum_exp a hs).LSeries_eq
  simp only [toAddCircle_apply, ← this, LSeries, ← tsum_mul_left]
  rw [← tsum_sum (fun i _ ↦ Summable.mul_left _ (LSeriesHasSum_exp _ hs).LSeriesSummable)]
  congr 1 with n
  simp only [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), ← mul_div_assoc, ← sum_div]
  congr 2 with i
  rw [AddChar.mulShift_apply, mul_comm _ (n : ℂ), Complex.exp_nat_mul, ← nsmul_eq_mul,
    AddChar.map_nsmul_eq_pow]
  simp only [stdAddChar_apply, toCircle_apply, push_cast, mul_div_assoc]

namespace IsPrimitive

/--
First step towards functional equation: prove equality of dual L-series with L-series of `χ⁻¹`
in convergence range. Private because it is superseded by `dualLFunction_eq` below.
-/
private lemma dualLFunction_eq_of_one_lt {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ)
    {s : ℂ} (hs : 1 < re s) :
    dualLFunction χ s = G χ * LFunction χ⁻¹ s := by
  simp only [dualLFunction_eq_LSeries_gaussSum _ hs, LSeries, LSeries.term_of_ne_zero'
    (ne_zero_of_one_lt_re hs), LFunction_eq_LSeries _ hs, ← tsum_mul_left]
  congr 1 with n
  simp only [← mul_div_assoc, gaussSum_mulShift_of_isPrimitive _ hχ, mul_comm]

/--
Second step towards functional equation: prove equality of completed dual L-series with completed
L-series of `χ⁻¹` in convergence range. Private because it is superseded by
`completedDualLFunction_eq` below.
-/
private lemma completedDualLFunction_eq_of_one_lt {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ)
    {s : ℂ} (hs : 1 < re s) :
    completedDualLFunction χ s = G χ * completedLFunction χ⁻¹ s := by
  have h := dualLFunction_eq_of_one_lt hχ hs
  suffices dualLFunction χ s = completedDualLFunction χ s / gammaFactor χ s by
    rwa [this, LFunction_eq_completed_div_gammaFactor _ _ (Or.inl
      (Complex.ne_zero_of_one_lt_re hs)), ← mul_div_assoc, gammaFactor_inv, div_left_inj'] at h
    rw [gammaFactor] -- remains to show gammaFactor ≠ 0
    split_ifs <;>
    apply Gammaℝ_ne_zero_of_re_pos <;>
    [skip; rw [add_re, one_re]] <;>
    positivity
  exact dualLFunction_eq_completed_div_gammaFactor _ _ (Or.inl (Complex.ne_zero_of_one_lt_re hs))

/--
The completed dual L-function of a primitive character is the completed L-function of its inverse.
-/
lemma completedDualLFunction_eq {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (s : ℂ) :
    completedDualLFunction χ s = G χ * completedLFunction χ⁻¹ s := by
  rcases eq_or_ne χ 1 with rfl | hχ'
  · obtain rfl : N = 1 := by
      rwa [IsPrimitive, conductor_one (NeZero.ne _), Eq.comm] at hχ
    rw [inv_one, completedLFunction_mod_one, completedDualLFunction_mod_one, gaussSum_mod_one,
      one_mul]
  apply congr_fun
  apply AnalyticOn.eq_of_eventuallyEq (𝕜 := ℂ)
  · exact (differentiable_completedDualLFunction hχ').differentiableOn.analyticOn isOpen_univ
  · refine (Differentiable.differentiableOn ?_).analyticOn isOpen_univ
    exact (differentiable_completedLFunction (inv_ne_one.mpr hχ')).const_mul _
  · refine Filter.eventually_of_mem ?_ (fun t ht ↦ completedDualLFunction_eq_of_one_lt hχ ht)
    refine (continuous_re.isOpen_preimage _ (isOpen_lt' _)).mem_nhds (?_ : 1 < re (2 : ℂ))
    simp only [re_ofNat, Nat.one_lt_ofNat]

/--
The dual L-function of a primitive character is the L-function of its inverse.
-/
lemma dualLFunction_eq {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (s : ℂ) :
    dualLFunction χ s = G χ * LFunction χ⁻¹ s := by
  rcases eq_or_ne χ 1 with rfl | hχ'
  · obtain ⟨rfl⟩ : N = 1 := by
      rwa [isPrimitive_def, conductor_one (NeZero.ne _), Eq.comm] at hχ
    rw [inv_one, LFunction_mod_one, dualLFunction_mod_one, gaussSum_mod_one, one_mul]
  have : N ≠ 1 := hχ' ∘ level_one' χ
  rw [dualLFunction_eq_completed_div_gammaFactor _ _ (Or.inr hχ'),
    LFunction_eq_completed_div_gammaFactor _ _  (Or.inr this),
    completedDualLFunction_eq hχ, gammaFactor_inv, mul_div_assoc]

/-- Functional equation for primitive Dirichlet L-functions. -/
theorem completedLFunction_one_sub {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (s : ℂ) :
    completedLFunction χ (1 - s) = N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s := by
  simp only [completedLFunction_one_sub_eq_dual, rootNumber, completedDualLFunction_eq hχ s]
  suffices N ^ (s - 1) = (N : ℂ) ^ (s - 1 / 2 : ℂ) / N ^ (1 / 2 : ℂ) by rw [this]; ring
  rw [← cpow_sub _ _ (NeZero.ne _), sub_sub, ← add_div, one_add_one_eq_two, div_self two_ne_zero]

end IsPrimitive

end DirichletContinuationOld
