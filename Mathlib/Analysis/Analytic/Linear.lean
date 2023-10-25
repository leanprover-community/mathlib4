/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Analytic.Composition

#align_import analysis.analytic.linear from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Linear functions are analytic

In this file we prove that a `ContinuousLinearMap` defines an analytic function with
the formal power series `f x = f a + f (x - a)`. We also prove similar results for multilinear maps.
-/


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open scoped Topology Classical BigOperators NNReal ENNReal

open Set Filter Asymptotics

noncomputable section

namespace ContinuousLinearMap

@[simp]
theorem fpowerSeries_radius (f : E →L[𝕜] F) (x : E) : (f.fpowerSeries x).radius = ∞ :=
  (f.fpowerSeries x).radius_eq_top_of_forall_image_add_eq_zero 2 fun _ => rfl
#align continuous_linear_map.fpower_series_radius ContinuousLinearMap.fpowerSeries_radius

protected theorem hasFPowerSeriesOnBall (f : E →L[𝕜] F) (x : E) :
    HasFPowerSeriesOnBall f (f.fpowerSeries x) x ∞ :=
  { r_le := by simp
    r_pos := ENNReal.coe_lt_top
    hasSum := fun _ => (hasSum_nat_add_iff' 2).1 <| by
      simp [Finset.sum_range_succ, ← sub_sub, hasSum_zero, fpowerSeries] }
#align continuous_linear_map.has_fpower_series_on_ball ContinuousLinearMap.hasFPowerSeriesOnBall

protected theorem hasFPowerSeriesAt (f : E →L[𝕜] F) (x : E) :
    HasFPowerSeriesAt f (f.fpowerSeries x) x :=
  ⟨∞, f.hasFPowerSeriesOnBall x⟩
#align continuous_linear_map.has_fpower_series_at ContinuousLinearMap.hasFPowerSeriesAt

protected theorem analyticAt (f : E →L[𝕜] F) (x : E) : AnalyticAt 𝕜 f x :=
  (f.hasFPowerSeriesAt x).analyticAt
#align continuous_linear_map.analytic_at ContinuousLinearMap.analyticAt

/-- Reinterpret a bilinear map `f : E →L[𝕜] F →L[𝕜] G` as a multilinear map
`(E × F) [×2]→L[𝕜] G`. This multilinear map is the second term in the formal
multilinear series expansion of `uncurry f`. It is given by
`f.uncurryBilinear ![(x, y), (x', y')] = f x y'`. -/
def uncurryBilinear (f : E →L[𝕜] F →L[𝕜] G) : E × F[×2]→L[𝕜] G :=
  @ContinuousLinearMap.uncurryLeft 𝕜 1 (fun _ => E × F) G _ _ _ _ _ <|
    (↑(continuousMultilinearCurryFin1 𝕜 (E × F) G).symm : (E × F →L[𝕜] G) →L[𝕜] _).comp <|
      f.bilinearComp (fst _ _ _) (snd _ _ _)
#align continuous_linear_map.uncurry_bilinear ContinuousLinearMap.uncurryBilinear

@[simp]
theorem uncurryBilinear_apply (f : E →L[𝕜] F →L[𝕜] G) (m : Fin 2 → E × F) :
    f.uncurryBilinear m = f (m 0).1 (m 1).2 :=
  rfl
#align continuous_linear_map.uncurry_bilinear_apply ContinuousLinearMap.uncurryBilinear_apply

/-- Formal multilinear series expansion of a bilinear function `f : E →L[𝕜] F →L[𝕜] G`. -/
def fpowerSeriesBilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) : FormalMultilinearSeries 𝕜 (E × F) G
  | 0 => ContinuousMultilinearMap.curry0 𝕜 _ (f x.1 x.2)
  | 1 => (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.deriv₂ x)
  | 2 => f.uncurryBilinear
  | _ => 0
#align continuous_linear_map.fpower_series_bilinear ContinuousLinearMap.fpowerSeriesBilinear

theorem fpowerSeriesBilinear_apply_zero (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    fpowerSeriesBilinear f x 0 = ContinuousMultilinearMap.curry0 𝕜 _ (f x.1 x.2) :=
  rfl

theorem fpowerSeriesBilinear_apply_one (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    fpowerSeriesBilinear f x 1 = (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.deriv₂ x) :=
  rfl

theorem fpowerSeriesBilinear_apply_two (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    fpowerSeriesBilinear f x 2 = f.uncurryBilinear :=
  rfl

theorem fpowerSeriesBilinear_apply_add_three (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) (n) :
    fpowerSeriesBilinear f x (n + 3) = 0 :=
  rfl

attribute
  [eqns
    fpowerSeriesBilinear_apply_zero
    fpowerSeriesBilinear_apply_one
    fpowerSeriesBilinear_apply_two
    fpowerSeriesBilinear_apply_add_three] fpowerSeriesBilinear
attribute [simp] fpowerSeriesBilinear

@[simp]
theorem fpowerSeriesBilinear_radius (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    (f.fpowerSeriesBilinear x).radius = ∞ :=
  (f.fpowerSeriesBilinear x).radius_eq_top_of_forall_image_add_eq_zero 3 fun _ => rfl
#align continuous_linear_map.fpower_series_bilinear_radius ContinuousLinearMap.fpowerSeriesBilinear_radius

protected theorem hasFPowerSeriesOnBall_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    HasFPowerSeriesOnBall (fun x : E × F => f x.1 x.2) (f.fpowerSeriesBilinear x) x ∞ :=
  { r_le := by simp
    r_pos := ENNReal.coe_lt_top
    hasSum := fun _ =>
      (hasSum_nat_add_iff' 3).1 <| by
        simp only [Finset.sum_range_succ, Finset.sum_range_one, Prod.fst_add, Prod.snd_add,
          f.map_add_add]
        simp [fpowerSeriesBilinear, hasSum_zero] }
#align continuous_linear_map.has_fpower_series_on_ball_bilinear ContinuousLinearMap.hasFPowerSeriesOnBall_bilinear

protected theorem hasFPowerSeriesAt_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    HasFPowerSeriesAt (fun x : E × F => f x.1 x.2) (f.fpowerSeriesBilinear x) x :=
  ⟨∞, f.hasFPowerSeriesOnBall_bilinear x⟩
#align continuous_linear_map.has_fpower_series_at_bilinear ContinuousLinearMap.hasFPowerSeriesAt_bilinear

protected theorem analyticAt_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    AnalyticAt 𝕜 (fun x : E × F => f x.1 x.2) x :=
  (f.hasFPowerSeriesAt_bilinear x).analyticAt
#align continuous_linear_map.analytic_at_bilinear ContinuousLinearMap.analyticAt_bilinear

end ContinuousLinearMap

variable (𝕜)

lemma analyticAt_id (z : E) : AnalyticAt 𝕜 (id : E → E) z :=
  (ContinuousLinearMap.id 𝕜 E).analyticAt z

/-- Scalar multiplication is analytic (jointly in both variables). The statement is a little
pedantic to allow towers of field extensions.

TODO: can we replace `𝕜'` with a "normed module" in such a way that `analyticAt_mul` is a special
case of this? -/
lemma analyticAt_smul
    {𝕝 : Type*} [NormedField 𝕝] [NormedAlgebra 𝕜 𝕝] [NormedSpace 𝕝 E] [IsScalarTower 𝕜 𝕝 E]
    (z : 𝕝 × E) : AnalyticAt 𝕜 (fun x : 𝕝 × E ↦ x.1 • x.2) z :=
  (ContinuousLinearMap.lsmul 𝕜 𝕝).analyticAt_bilinear z

/-- Multiplication in a normed algebra over `𝕜` is -/
lemma analyticAt_mul {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] (z : A × A) :
    AnalyticAt 𝕜 (fun x : A × A ↦ x.1 * x.2) z :=
  (ContinuousLinearMap.mul 𝕜 A).analyticAt_bilinear z

namespace AnalyticAt
variable {𝕜}

/-- Scalar multiplication of one analytic function by another. -/
lemma smul {𝕝 : Type*} [NontriviallyNormedField 𝕝] [NormedSpace 𝕝 F] [NormedAlgebra 𝕜 𝕝]
    [IsScalarTower 𝕜 𝕝 F] {f : E → 𝕝} {g : E → F} {z : E}
    (hf : AnalyticAt 𝕜 f z) (hg : AnalyticAt 𝕜 g z) :
    AnalyticAt 𝕜 (f • g) z :=
  @AnalyticAt.comp 𝕜 E (𝕝 × F) F _ _ _ _ _ _ _
    (fun x ↦ x.1 • x.2) (fun e ↦ (f e, g e)) z (analyticAt_smul _ _) (hf.prod hg)

/-- Multiplication of analytic functions (valued in a normd `𝕜`-algebra) is analytic. -/
lemma mul {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    {f g : E → A} {z : E}
    (hf : AnalyticAt 𝕜 f z) (hg : AnalyticAt 𝕜 g z) : AnalyticAt 𝕜 (f * g) z :=
  @AnalyticAt.comp 𝕜 E (A × A) A _ _ _ _ _ _ _
    (fun x ↦ x.1 * x.2) (fun e ↦ (f e, g e)) z (analyticAt_mul _ (f z, g z)) (hf.prod hg)

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
lemma pow {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    {f : E → A} {z : E} (hf : AnalyticAt 𝕜 f z) (n : ℕ) :
    AnalyticAt 𝕜 (f ^ n) z := by
  induction' n with m hm
  · rw [pow_zero]
    exact (analyticAt_const : AnalyticAt 𝕜 (fun _ ↦ (1 : A)) z)
  · exact pow_succ f m ▸ hf.mul hm

end AnalyticAt

/-- If `𝕝` is a normed field extension of `𝕜`, then the inverse map `𝕝 → 𝕝` is `𝕜`-analytic
away from 0. -/
lemma analyticAt_inv {𝕝 : Type*} [NontriviallyNormedField 𝕝] [NormedAlgebra 𝕜 𝕝]
    {z : 𝕝} (hz : z ≠ 0) : AnalyticAt 𝕜 Inv.inv z := by
  let f1 : 𝕝 → 𝕝 := fun a ↦ 1 / z * a
  let f2 : 𝕝 → 𝕝 := fun b ↦ (1 - b)⁻¹
  let f3 : 𝕝 → 𝕝 := fun c ↦ 1 - c / z
  have feq : f1 ∘ f2 ∘ f3 = Inv.inv
  · ext1 x
    dsimp only [Function.comp_apply]
    field_simp
  have f3val : f3 z = 0 := by simp only [div_self hz, sub_self]
  have f3an : AnalyticAt 𝕜 f3 z
  · apply analyticAt_const.sub
    simpa only [div_eq_inv_mul] using analyticAt_const.mul (analyticAt_id 𝕜 z)
  exact feq ▸ (analyticAt_const.mul (analyticAt_id _ _)).comp
    ((f3val.symm ▸ analyticAt_inv_one_sub 𝕝).comp f3an)
