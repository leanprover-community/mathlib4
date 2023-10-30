/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

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

/-- The polar coordinates local homeomorphism in `ℂ`, mapping `r (cos θ + I * sin θ)` to `(r, θ)`.
It is a homeomorphism between `ℂ - ℝ≤0` and `(0, +∞) × (-π, π)`. -/
protected noncomputable def Complex.polarCoord : LocalHomeomorph ℂ (ℝ × ℝ) :=
  equivRealProdClm.toHomeomorph.toLocalHomeomorph.trans polarCoord

protected theorem Complex.polarCoord_apply (a : ℂ) :
    Complex.polarCoord a = (Complex.abs a, Complex.arg a) := by
  simp_rw [Complex.abs_def, Complex.normSq_apply, ← pow_two]
  rfl

@[simp]
theorem Complex.equivRealProdAddHom_symm_apply (p : ℝ × ℝ) :
    Complex.equivRealProdAddHom.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p

@[simp]
theorem Complex.equivRealProdLm_symm_apply (p : ℝ × ℝ) :
    Complex.equivRealProdLm.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p

@[simp]
theorem Complex.equivRealProdClm_symm_apply (p : ℝ × ℝ) :
    Complex.equivRealProdClm.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p

protected theorem Complex.polarCoord_source :
    Complex.polarCoord.source = {a | 0 < a.re} ∪ {a | a.im ≠ 0} := by simp [Complex.polarCoord]

@[simp]
protected theorem Complex.polarCoord_symm_apply (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
  simp [Complex.polarCoord, mul_add, mul_assoc]

theorem Complex.polardCoord_symm_abs (p : ℝ × ℝ) :
    Complex.abs (Complex.polarCoord.symm p) = |p.1| := by simp

alias Complex.polarCoord_target := polarCoord_target

protected theorem Complex.integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ p in polarCoord.target, p.1 • f (Complex.polarCoord.symm p)) = ∫ p, f p := by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    measurableEquivRealProd.symm.measurableEmbedding, ← integral_comp_polarCoord_symm]
  rfl

end Complex
