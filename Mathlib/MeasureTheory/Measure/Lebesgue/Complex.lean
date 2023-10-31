/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

#align_import measure_theory.measure.lebesgue.complex from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Lebesgue measure on `ℂ`

In this file, we consider the Lebesgue measure on `ℂ` defined as the push-forward of the volume
on `ℝ²` under the natural isomorphism and prove that it is equal to the measure `volume` of `ℂ`
coming from its `InnerProductSpace` structure over `ℝ`. For that, we consider the two frequently
used ways to represent `ℝ²` in `mathlib`: `ℝ × ℝ` and `Fin 2 → ℝ`, define measurable equivalences
(`MeasurableEquiv`) to both types and prove that both of them are volume preserving (in the sense
of `MeasureTheory.measurePreserving`).
-/

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

open MeasureTheory

noncomputable section

namespace Complex

/-- Measurable equivalence between `ℂ` and `ℝ² = Fin 2 → ℝ`. -/
def measurableEquivPi : ℂ ≃ᵐ (Fin 2 → ℝ) :=
  basisOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
#align complex.measurable_equiv_pi Complex.measurableEquivPi

@[simp]
theorem measurableEquivPi_apply (a : ℂ) :
    measurableEquivPi a = ![a.re, a.im] := rfl

@[simp]
theorem measurableEquivPi_symm_apply (p : (Fin 2) → ℝ) :
    measurableEquivPi.symm p = (p 0) + (p 1) * I := rfl

/-- Measurable equivalence between `ℂ` and `ℝ × ℝ`. -/
def measurableEquivRealProd : ℂ ≃ᵐ ℝ × ℝ :=
  equivRealProdClm.toHomeomorph.toMeasurableEquiv
#align complex.measurable_equiv_real_prod Complex.measurableEquivRealProd

@[simp]
theorem measurableEquivRealProd_apply (a : ℂ) : measurableEquivRealProd a = (a.re, a.im) := rfl

@[simp]
theorem measurableEquivRealProd_symm_apply (p : ℝ × ℝ) :
    measurableEquivRealProd.symm p = {re := p.1, im := p.2} := rfl

theorem volume_preserving_equiv_pi : MeasurePreserving measurableEquivPi := by
  convert (measurableEquivPi.symm.measurable.measurePreserving volume).symm
  rw [← addHaarMeasure_eq_volume_pi, ← Basis.parallelepiped_basisFun, ← Basis.addHaar,
    measurableEquivPi, Homeomorph.toMeasurableEquiv_symm_coe,
    ContinuousLinearEquiv.symm_toHomeomorph, ContinuousLinearEquiv.coe_toHomeomorph,
    Basis.map_addHaar, eq_comm]
  exact (Basis.addHaar_eq_iff _ _).mpr Complex.orthonormalBasisOneI.volume_parallelepiped
#align complex.volume_preserving_equiv_pi Complex.volume_preserving_equiv_pi

theorem volume_preserving_equiv_real_prod : MeasurePreserving measurableEquivRealProd :=
  (volume_preserving_finTwoArrow ℝ).comp volume_preserving_equiv_pi
#align complex.volume_preserving_equiv_real_prod Complex.volume_preserving_equiv_real_prod

@[simp]
theorem volume_ball (a : ℂ) (r : ℝ) :
    volume (Metric.ball a r) = NNReal.pi * ENNReal.ofReal r ^ 2 := by
  rw [Measure.addHaar_ball_center, ← EuclideanSpace.volume_ball 0,
    ← (volume_preserving_equiv_pi.symm).measure_preimage measurableSet_ball,
    ← ((EuclideanSpace.volume_preserving_measurableEquiv (Fin 2)).symm).measure_preimage
    measurableSet_ball]
  refine congrArg _ (Set.ext fun _ => ?_)
  simp_rw [← MeasurableEquiv.coe_toEquiv_symm, Set.mem_preimage, MeasurableEquiv.coe_toEquiv_symm,
    measurableEquivPi_symm_apply, mem_ball_zero_iff, norm_eq_abs, abs_def, normSq_add_mul_I,
    EuclideanSpace.coe_measurableEquiv_symm, EuclideanSpace.norm_eq, WithLp.equiv_symm_pi_apply,
    Fin.sum_univ_two, Real.norm_eq_abs, _root_.sq_abs]

@[simp]
theorem volume_closedBall (a : ℂ) (r : ℝ) :
    volume (Metric.closedBall a r) = NNReal.pi * ENNReal.ofReal r ^ 2 := by
  rw [MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball, Complex.volume_ball]

section polar

/-- The polar coordinates local homeomorphism in `ℂ`, mapping `r (cos θ + I * sin θ)` to `(r, θ)`.
It is a homeomorphism between `ℂ - ℝ≤0` and `(0, +∞) × (-π, π)`. -/
protected noncomputable def polarCoord : LocalHomeomorph ℂ (ℝ × ℝ) :=
  equivRealProdClm.toHomeomorph.toLocalHomeomorph.trans polarCoord

protected theorem polarCoord_apply (a : ℂ) :
    Complex.polarCoord a = (Complex.abs a, Complex.arg a) := by
  simp_rw [Complex.abs_def, Complex.normSq_apply, ← pow_two]
  rfl

protected theorem polarCoord_source :
    Complex.polarCoord.source = {a | 0 < a.re} ∪ {a | a.im ≠ 0} := by simp [Complex.polarCoord]

alias Complex.polarCoord_target := polarCoord_target

@[simp]
protected theorem polarCoord_symm_apply (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
  simp [Complex.polarCoord, equivRealProdClm_symm_apply, mul_add, mul_assoc]

theorem polardCoord_symm_abs (p : ℝ × ℝ) :
    Complex.abs (Complex.polarCoord.symm p) = |p.1| := by simp

protected theorem integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ p in polarCoord.target, p.1 • f (Complex.polarCoord.symm p)) = ∫ p, f p := by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    measurableEquivRealProd.symm.measurableEmbedding, ← integral_comp_polarCoord_symm]
  rfl

end polar

end Complex
