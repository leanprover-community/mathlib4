/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Fourier Coefficients of Polynomials

We define a linear map from ℂ[X] to the Lp space on the additive circle and show that it sends
monomials to the Fourier basis. From this, we derive that polynomial coefficients match Fourier
coefficients and prove Parseval's identity for polynomials.

## Main definitions

- `Polynomial.toAddCircle`: Linear map from ℂ[X] to C(AddCircle (2 * π), ℂ) that evaluates
  polynomials on the unit circle.

## Main results

- `Polynomial.toAddCircle_fourierCoeff_zcoeff`: The `n`-th Fourier coefficient of a polynomial
  equals its `n`-th coefficient when `n` is nonnegative, else 0.
- `Polynomial.toAddCircle_fourierCoeff_coeff`: A variant of
  `Polynomial.toAddCircle_fourierCoeff_zcoeff` for `ℕ` arguments.
- `Polynomial.sum_sq_norm_coeff_eq_circleAverage`: Parseval's identity that the sum of the squares
  of the norms of the coefficients equals the average over the circle of the norm square.

-/

open Complex MeasureTheory Set AddCircle

namespace Polynomial

@[expose] public section complex

variable (p : ℂ[X])

private instance instTwoPiPos : Fact (0 < 2 * Real.pi) := Fact.mk Real.two_pi_pos

/-- Linear map from ℂ[X] to C(AddCircle (2 * π), ℂ) that evaluates polynomials on the unit circle.
For a polynomial p, this maps it to the function θ ↦ p(exp(iθ)). -/
noncomputable def toAddCircle : ℂ[X] →ₗ[ℂ] C(AddCircle (2 * Real.pi), ℂ) where
  toFun p := {
    toFun := fun θ => p.eval (toCircle θ)
    continuous_toFun := p.continuous.comp
      (continuous_subtype_val.comp AddCircle.continuous_toCircle)
  }
  map_add' p q := by ext; simp [Polynomial.eval_add]
  map_smul' c p := by ext; simp [Polynomial.eval_smul, smul_eq_mul]

lemma toAddCircle.integrable :
    Integrable p.toAddCircle (@haarAddCircle _ (Fact.mk Real.two_pi_pos)) := by
  simpa using (p.toAddCircle.continuous.continuousOn (s := Set.univ)).integrableOn_compact
    isCompact_univ

theorem toAddCircle_C_fourier {c : ℂ} : (C c).toAddCircle = c • (fourier 0) := by
  ext θ; simp [toAddCircle]

theorem toAddCircle_X_fourier : (X : ℂ[X]).toAddCircle = fourier 1 := by
  ext θ; simp [toAddCircle]

theorem toAddCircle_X_pow_fourier {n : ℕ} : (X ^ n : ℂ[X]).toAddCircle = fourier n := by
  ext θ; simp [toAddCircle, AddCircle.toCircle_nsmul]

theorem toAddCircle_C_mul_X_pow_fourier {n : ℕ} {c : ℂ} : ((C c) * (X : ℂ[X]) ^ n).toAddCircle =
    c • fourier n := by
  ext θ; simp [toAddCircle, AddCircle.toCircle_nsmul]

theorem toAddCircle_fourierCoeff_zcoeff (n : ℤ) :
    fourierCoeff (hT := Fact.mk Real.two_pi_pos) p.toAddCircle n =
      if 0 ≤ n then p.coeff n.natAbs else 0 := by
  nth_rw 1 [p.as_sum_support_C_mul_X_pow, map_sum]
  simp only [ContinuousMap.coe_sum, Finset.sum_apply,
    fourierCoeff.sum (hT := Fact.mk Real.two_pi_pos) _ _ (fun i _ ↦ toAddCircle.integrable _)]
  simp_rw [toAddCircle_C_mul_X_pow_fourier, ContinuousMap.coe_smul, fourierCoeff.const_smul,
    fourierCoeff_fourier, Pi.single_apply, smul_ite, smul_zero, smul_eq_mul, mul_one]
  split_ifs with h
  · rw [show n = n.natAbs by omega]
    norm_cast
    simp only [Finset.sum_ite_eq, mem_support_iff, ne_eq, ite_not, ite_eq_right_iff]
    exact fun h ↦ h.symm
  · refine Finset.sum_eq_zero ?_
    simp only [ite_eq_right_iff]
    omega

theorem toAddCircle_fourierCoeff_coeff (n : ℕ) :
    fourierCoeff (hT := Fact.mk Real.two_pi_pos) p.toAddCircle n = p.coeff n := by
  simp [toAddCircle_fourierCoeff_zcoeff]

/-- **Parseval's Identity** for polynomials -/
theorem sum_sq_norm_coeff_eq_circleAverage : ∑ i ∈ p.support, ‖p.coeff i‖ ^ 2 =
    Real.circleAverage (fun θ ↦ ‖p.eval θ‖ ^ 2) 0 1 := by
  -- Rewrite coefficients as Fourier coefficients
  have := tsum_sq_fourierCoeff (T := 2 * Real.pi) (p.toAddCircle.toLp 2 haarAddCircle ℂ)
  simp_rw [fourierCoeff_toLp, toAddCircle_fourierCoeff_zcoeff] at this
  rw [tsum_eq_sum (s := p.support.map ⟨Int.ofNat, Int.ofNat_injective⟩) (fun b hb => by
    obtain h | h := le_or_gt 0 b
    · simp only [h, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      norm_eq_zero]
      by_contra! h'
      rw [Finset.mem_map] at hb
      push_neg at hb
      exact hb _ (mem_support_iff.mpr h') (Int.natAbs_of_nonneg h)
    · simp [h])] at this
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk, Int.ofNat_eq_natCast, Nat.cast_nonneg,
    ↓reduceIte, Int.natAbs_natCast, ContinuousMap.coe_toLp] at this
  have h1 : ∫ (t : AddCircle (2 * Real.pi)), ‖toAddCircle p t‖ ^ 2 ∂haarAddCircle =
      ∫ (t : AddCircle (2 * Real.pi)),
        ‖(ContinuousMap.toAEEqFun haarAddCircle (toAddCircle p)) t‖ ^ 2 ∂haarAddCircle := by
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toAEEqFun haarAddCircle (toAddCircle p)] with t ht
    rw [← ht]
  rw [this, ← h1, AddCircle.integral_haarAddCircle, Real.circleAverage,
    ← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0]
  simp [toAddCircle, toCircle, circleMap]

end complex

end Polynomial
