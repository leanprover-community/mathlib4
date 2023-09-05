/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
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


open MeasureTheory

noncomputable section

namespace Complex

/-- Measurable equivalence between `ℂ` and `ℝ² = Fin 2 → ℝ`. -/
def measurableEquivPi : ℂ ≃ᵐ (Fin 2 → ℝ) :=
  basisOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
#align complex.measurable_equiv_pi Complex.measurableEquivPi

/-- Measurable equivalence between `ℂ` and `ℝ × ℝ`. -/
def measurableEquivRealProd : ℂ ≃ᵐ ℝ × ℝ :=
  equivRealProdClm.toHomeomorph.toMeasurableEquiv
#align complex.measurable_equiv_real_prod Complex.measurableEquivRealProd

@[simp]
theorem measurableEquivRealProd_apply (a : ℂ) : measurableEquivRealProd a = (a.re, a.im) := rfl

theorem volume_preserving_equiv_pi : MeasurePreserving measurableEquivPi := by
  convert (measurableEquivPi.symm.measurable.measurePreserving volume).symm
  rw [← addHaarMeasure_eq_volume_pi, ← Basis.parallelepiped_basisFun, ← Basis.addHaar,
    measurableEquivPi, Homeomorph.toMeasurableEquiv_symm_coe,
    ContinuousLinearEquiv.symm_toHomeomorph, ContinuousLinearEquiv.coe_toHomeomorph,
    Basis.addHaar_map]
  exact Basis.addHaar_eq.mpr Complex.orthonormalBasisOneI.volume_parallelepiped
#align complex.volume_preserving_equiv_pi Complex.volume_preserving_equiv_pi

theorem volume_preserving_equiv_real_prod : MeasurePreserving measurableEquivRealProd :=
  (volume_preserving_finTwoArrow ℝ).comp volume_preserving_equiv_pi
#align complex.volume_preserving_equiv_real_prod Complex.volume_preserving_equiv_real_prod

-- See: https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

@[simp]
theorem volume_ball (a : ℂ) (r : ℝ) :
    volume (Metric.ball a r) = NNReal.pi * (ENNReal.ofReal r) ^ 2 := by
  obtain hr | hr := lt_or_le r 0
  · rw [Metric.ball_eq_empty.mpr (le_of_lt hr), measure_empty, ← ENNReal.zero_eq_ofReal.mpr
      (le_of_lt hr), zero_pow zero_lt_two, mul_zero]
  · suffices volume (Metric.ball (0: ℂ) 1) = NNReal.pi by
      rw [Measure.addHaar_ball _ _ hr, finrank_real_complex, ENNReal.ofReal_pow hr, this, mul_comm]
    let D := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
    have mes_D : MeasurableSet D :=
      measurableSet_lt (Measurable.add (by measurability) (by measurability)) (by measurability)
    have D_eq : D = regionBetween (fun x => - Real.sqrt (1 - x ^ 2))
        (fun x => Real.sqrt (1 - x ^ 2)) (Set.Ioc (-1) 1) := by
      ext p
      simp_rw [regionBetween, Set.mem_Ioc, Set.mem_Ioo, ← Real.sq_lt, lt_tsub_iff_left,
        Set.mem_setOf_eq, Nat.cast_one]
      refine iff_and_self.mpr (fun h => And.imp_right le_of_lt ?_)
      rw [← abs_lt, ← sq_lt_one_iff_abs_lt_one]
      exact lt_of_add_lt_of_nonneg_left h (sq_nonneg _)
    calc
      _ = (volume (measurableEquivRealProd ⁻¹' D)) := by
            simp_rw [Metric.ball, dist_zero_right, norm_eq_abs, Set.preimage_setOf_eq,
              measurableEquivRealProd_apply, ← normSq_add_mul_I, re_add_im, normSq_eq_abs,
              pow_lt_one_iff_of_nonneg (map_nonneg _ _) two_ne_zero]
      _ = (volume D) := volume_preserving_equiv_real_prod.measure_preimage mes_D
      _ = ENNReal.ofReal ((2 : ℝ) * ∫ (a : ℝ) in Set.Ioc (-1) 1, Real.sqrt (1 - a ^ 2)) := by
            rw [D_eq, Measure.volume_eq_prod, volume_regionBetween_eq_integral
              (Continuous.integrableOn_Ioc (by continuity)) (Continuous.integrableOn_Ioc
              (by continuity)) measurableSet_Ioc (fun _ _ => neg_le_self (Real.sqrt_nonneg _))]
            simp_rw [Pi.sub_apply, sub_neg_eq_add, ← two_mul, integral_mul_left]
      _ = NNReal.pi := by
            rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), Nat.cast_one,
              integral_sqrt_one_sub_sq, two_mul, add_halves, ← NNReal.coe_real_pi,
              ENNReal.ofReal_coe_nnreal]

@[simp]
theorem volume_closedBall (a : ℂ) (r : ℝ) :
     volume (Metric.closedBall a r) = NNReal.pi * (ENNReal.ofReal r) ^ 2 := by
  rw [MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball, Complex.volume_ball]
end Complex
