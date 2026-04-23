/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike

/-!
# Mellin inversion formula

We derive the Mellin inversion formula as a consequence of the Fourier inversion formula.

## Main results
- `mellin_inversion`: The inverse Mellin transform of the Mellin transform applied to `x > 0` is x.
-/

public section

open Real Complex Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

open scoped FourierTransform

private theorem rexp_neg_deriv_aux :
    ∀ x ∈ univ, HasDerivWithinAt (rexp ∘ Neg.neg) (-rexp (-x)) univ x :=
  fun x _ ↦ mul_neg_one (rexp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem rexp_neg_image_aux : rexp ∘ Neg.neg '' univ = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

private theorem rexp_neg_injOn_aux : univ.InjOn (rexp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

private theorem rexp_cexp_aux (x : ℝ) (s : ℂ) (f : E) :
    rexp (-x) • cexp (-↑x) ^ (s - 1) • f = cexp (-s * ↑x) • f := by
  change (rexp (-x) : ℂ) • _ = _ • f
  rw [← smul_assoc, smul_eq_mul]
  push_cast
  conv in cexp _ * _ => lhs; rw [← cpow_one (cexp _)]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _), cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [pi_pos]) (by simpa using pi_nonneg)]
  ring_nf

set_option backward.isDefEq.respectTransparency false in
theorem mellin_eq_fourier (f : ℝ → E) {s : ℂ} :
    mellin f s = 𝓕 (fun (u : ℝ) ↦ (Real.exp (-s.re * u) • f (Real.exp (-u)))) (s.im / (2 * π)) :=
  calc
    mellin f s
      = ∫ (u : ℝ), Complex.exp (-s * u) • f (Real.exp (-u)) := by
      rw [mellin, ← rexp_neg_image_aux, integral_image_eq_integral_abs_deriv_smul
        MeasurableSet.univ rexp_neg_deriv_aux rexp_neg_injOn_aux]
      simp [rexp_cexp_aux]
    _ = ∫ (u : ℝ), Complex.exp (↑(-2 * π * (u * (s.im / (2 * π)))) * I) •
        (Real.exp (-s.re * u) • f (Real.exp (-u))) := by
      congr
      ext u
      trans Complex.exp (-s.im * u * I) • (Real.exp (-s.re * u) • f (Real.exp (-u)))
      · conv => lhs; rw [← re_add_im s]
        rw [neg_add, add_mul, Complex.exp_add, mul_comm, ← smul_eq_mul, smul_assoc]
        norm_cast
        push_cast
        ring_nf
      congr
      simp [field]
    _ = 𝓕 (fun (u : ℝ) ↦ (Real.exp (-s.re * u) • f (Real.exp (-u)))) (s.im / (2 * π)) := by
      simp [fourier_eq', mul_comm (_ / _)]

@[deprecated (since := "2025-11-16")]
alias mellin_eq_fourierIntegral := mellin_eq_fourier

set_option backward.isDefEq.respectTransparency false in
theorem mellinInv_eq_fourierInv (σ : ℝ) (f : ℂ → E) {x : ℝ} (hx : 0 < x) :
    mellinInv σ f x =
    (x : ℂ) ^ (-σ : ℂ) • 𝓕⁻ (fun (y : ℝ) ↦ f (σ + 2 * π * y * I)) (-Real.log x) := calc
  mellinInv σ f x
    = (x : ℂ) ^ (-σ : ℂ) •
      (∫ (y : ℝ), Complex.exp (2 * π * (y * (-Real.log x)) * I) • f (σ + 2 * π * y * I)) := by
    rw [mellinInv, one_div, ← abs_of_pos (show 0 < (2 * π)⁻¹ by simp [pi_pos])]
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
    simp_rw [neg_add, cpow_add _ _ hx0, mul_smul, integral_smul]
    rw [smul_comm, ← Measure.integral_comp_mul_left]
    congr! 3
    rw [cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
    push_cast
    ring_nf
  _ = (x : ℂ) ^ (-σ : ℂ) • 𝓕⁻ (fun (y : ℝ) ↦ f (σ + 2 * π * y * I)) (-Real.log x) := by
    simp [fourierInv_eq', mul_comm (Real.log _)]

@[deprecated (since := "2025-11-16")]
alias mellinInv_eq_fourierIntegralInv := mellinInv_eq_fourierInv

variable [CompleteSpace E]

/-- The inverse Mellin transform of the Mellin transform applied to `x > 0` is x. -/
theorem mellinInv_mellin_eq (σ : ℝ) (f : ℝ → E) {x : ℝ} (hx : 0 < x) (hf : MellinConvergent f σ)
    (hFf : VerticalIntegrable (mellin f) σ) (hfx : ContinuousAt f x) :
    mellinInv σ (mellin f) x = f x := by
  let g := fun (u : ℝ) => Real.exp (-σ * u) • f (Real.exp (-u))
  replace hf : Integrable g := by
    rw [MellinConvergent, ← rexp_neg_image_aux, integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ rexp_neg_deriv_aux rexp_neg_injOn_aux] at hf
    replace hf : Integrable fun (x : ℝ) ↦ cexp (-↑σ * ↑x) • f (rexp (-x)) := by
      simpa [rexp_cexp_aux] using hf
    norm_cast at hf
  replace hFf : Integrable (𝓕 g) := by
    have h2π : 2 * π ≠ 0 := by simp
    have : Integrable (𝓕 (fun u ↦ rexp (-(σ * u)) • f (rexp (-u)))) := by
      simpa [mellin_eq_fourier, mul_div_cancel_right₀ _ h2π] using hFf.comp_mul_right' h2π
    simp_rw [neg_mul_eq_neg_mul] at this
    exact this
  replace hfx : ContinuousAt g (-Real.log x) := by
    refine ContinuousAt.smul (by fun_prop) (ContinuousAt.comp ?_ (by fun_prop))
    simpa [Real.exp_log hx] using hfx
  calc
    mellinInv σ (mellin f) x
      = mellinInv σ (fun s ↦ 𝓕 g (s.im / (2 * π))) x := by
      simp [g, mellinInv, mellin_eq_fourier]
    _ = (x : ℂ) ^ (-σ : ℂ) • g (-Real.log x) := by
      rw [mellinInv_eq_fourierInv _ _ hx, ← hf.fourierInv_fourier_eq hFf hfx]
      simp [mul_div_cancel_left₀ _ (show 2 * π ≠ 0 by simp)]
    _ = (x : ℂ) ^ (-σ : ℂ) • rexp (σ * Real.log x) • f (rexp (Real.log x)) := by simp [g]
    _ = f x := by
      norm_cast
      rw [mul_comm σ, ← rpow_def_of_pos hx, Real.exp_log hx, ← Complex.ofReal_cpow hx.le]
      norm_cast
      rw [← smul_assoc, smul_eq_mul, Real.rpow_neg hx.le,
        inv_mul_cancel₀ (ne_of_gt (rpow_pos_of_pos hx σ)), one_smul]

@[deprecated (since := "2025-11-16")]
alias mellin_inversion := mellinInv_mellin_eq
