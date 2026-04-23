/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
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
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Fourier Coefficients of Polynomials

We define an algebra map from `ℂ[X]` to the `MeasureTheory.Lp` (with `p := 2`) space on the additive
circle and show that it sends monomials to the Fourier basis. From this, we derive that polynomial
coefficients match Fourier coefficients and prove Parseval's identity for polynomials.

## Main definitions

- `Polynomial.toAddCircle`: Algebra map from `ℂ[X]` to `C(AddCircle (2 * π), ℂ)` that evaluates
  polynomials on the unit circle.

## Main results

- `Polynomial.fourierCoeff_toAddCircle`: The `n`-th Fourier coefficient of a polynomial
  equals its `n`-th coefficient when `n` is nonnegative, else 0.
- `Polynomial.fourierCoeff_toAddCircle_natCast`: A variant of `Polynomial.fourierCoeff_toAddCircle`
  for `ℕ` arguments.
- `Polynomial.sum_sq_norm_coeff_eq_circleAverage`: Parseval's identity that the sum of the squares
  of the norms of the coefficients of a polynomial equals the average over the circle of the norm
  square of the polynomial.
-/

open Complex MeasureTheory Set AddCircle
open scoped Real

namespace Polynomial

@[expose] public section complex

variable (p : ℂ[X])

local instance instTwoPiPos : Fact (0 < 2 * π) := Fact.mk Real.two_pi_pos

/-- Algebra map from `ℂ[X]` to `C(AddCircle (2 * π), ℂ)` that evaluates polynomials on the unit
circle. For a polynomial `p`, this maps it to the function `fun θ ↦ p (exp (I * θ))`. -/
noncomputable def toAddCircle : ℂ[X] →ₐ[ℂ] C(AddCircle (2 * π), ℂ) :=
  Polynomial.aeval { toFun c := c.toCircle }

lemma toAddCircle.integrable :
    Integrable p.toAddCircle (haarAddCircle (T := 2 * π)) := by
  simpa using p.toAddCircle.continuous.continuousOn.integrableOn_compact isCompact_univ

theorem toAddCircle_C_eq_smul_fourier_zero {c : ℂ} : (C c).toAddCircle = c • fourier 0 := by
  ext θ; simp [toAddCircle]

theorem toAddCircle_X_eq_fourier_one : (X : ℂ[X]).toAddCircle = fourier 1 := by
  ext θ; simp [toAddCircle]

theorem toAddCircle_X_pow_eq_fourier {n : ℕ} : (X ^ n : ℂ[X]).toAddCircle = fourier n := by
  ext θ; simp [toAddCircle, AddCircle.toCircle_nsmul]

theorem toAddCircle_monomial_eq_smul_fourier {n : ℕ} {c : ℂ} :
    (monomial n c).toAddCircle = c • fourier n := by
  ext θ; simp [toAddCircle, AddCircle.toCircle_nsmul]

/-- The `n`th Fourier coefficient of a polynomial is the coefficient of `X ^ n`, or
zero if `n < 0`. -/
theorem fourierCoeff_toAddCircle (n : ℤ) :
    fourierCoeff (T := 2 * π) p.toAddCircle n = if 0 ≤ n then p.coeff n.natAbs else 0 := by
  have : n < 0 ∨ ∃ k : ℕ, n = k := lt_or_ge n 0 |>.imp_right Int.eq_ofNat_of_zero_le
  induction p using Polynomial.induction_on' with obtain (hn | ⟨k, rfl⟩) := this
  | add p q hp hq =>
    simp_all [not_le_of_gt, fourierCoeff.add (toAddCircle.integrable p) (toAddCircle.integrable q)]
  | monomial m a =>
    simp_all [not_le_of_gt, coeff_monomial, toAddCircle_monomial_eq_smul_fourier,
      fourierCoeff.const_smul, fourierCoeff_fourier, Pi.single_apply]
    grind

/-- The `n`th Fourier coefficient of a polynomial is the coefficient of `X ^ n` -/
theorem fourierCoeff_toAddCircle_natCast (n : ℕ) :
    fourierCoeff (T := 2 * π) p.toAddCircle n = p.coeff n := by
  simp [fourierCoeff_toAddCircle]

theorem fourierCoeff_toAddCircle_eq_zero_of_lt_zero (n : ℤ) (hn : n < 0) :
    fourierCoeff (T := 2 * π) p.toAddCircle n = 0 := by
  simp [fourierCoeff_toAddCircle, hn]

/-- **Parseval's Identity** for polynomials -/
theorem sum_sq_norm_coeff_eq_circleAverage : ∑ i ∈ p.support, ‖p.coeff i‖ ^ 2 =
    Real.circleAverage (fun θ ↦ ‖p.eval θ‖ ^ 2) 0 1 := by
  -- Rewrite coefficients as Fourier coefficients
  have := tsum_sq_fourierCoeff (T := 2 * π) (p.toAddCircle.toLp 2 haarAddCircle ℂ)
  simp_rw [fourierCoeff_toLp, fourierCoeff_toAddCircle] at this
  rw [tsum_eq_sum (s := p.support.map ⟨_, Nat.cast_injective⟩) (fun b hb => ?eq_zero)] at this
  case eq_zero =>
    obtain h | h := le_or_gt 0 b
    · lift b to ℕ using h
      simpa using hb
    · simp [h]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk, Nat.cast_nonneg,
    ↓reduceIte, Int.natAbs_natCast, ContinuousMap.coe_toLp] at this
  have h1 : ∫ (t : AddCircle (2 * π)), ‖toAddCircle p t‖ ^ 2 ∂haarAddCircle =
      ∫ (t : AddCircle (2 * π)),
        ‖(ContinuousMap.toAEEqFun haarAddCircle (toAddCircle p)) t‖ ^ 2 ∂haarAddCircle := by
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toAEEqFun haarAddCircle (toAddCircle p)] with t ht
    rw [← ht]
  rw [this, ← h1, AddCircle.integral_haarAddCircle, Real.circleAverage,
    ← AddCircle.intervalIntegral_preimage (2 * π) 0]
  simp [toAddCircle, toCircle, circleMap]

end complex
end Polynomial
