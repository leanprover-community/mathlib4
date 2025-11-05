/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.CPolynomialDef

/-!
# Linear functions are analytic

In this file we prove that a `ContinuousLinearMap` defines an analytic function with
the formal power series `f x = f a + f (x - a)`. We also prove similar results for bilinear maps.

We deduce this fact from the stronger result that continuous linear maps are continuously
polynomial, i.e., they admit a finite power series.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open scoped Topology NNReal ENNReal
open Set Filter Asymptotics

noncomputable section

namespace ContinuousLinearMap

@[simp]
theorem fpowerSeries_radius (f : E →L[𝕜] F) (x : E) : (f.fpowerSeries x).radius = ∞ :=
  (f.fpowerSeries x).radius_eq_top_of_forall_image_add_eq_zero 2 fun _ => rfl

protected theorem hasFiniteFPowerSeriesOnBall (f : E →L[𝕜] F) (x : E) :
    HasFiniteFPowerSeriesOnBall f (f.fpowerSeries x) x 2 ∞ where
  r_le := by simp
  r_pos := ENNReal.coe_lt_top
  hasSum := fun _ => (hasSum_nat_add_iff' 2).1 <| by
    simp [Finset.sum_range_succ, hasSum_zero, fpowerSeries]
  finite := by
    intro m hm
    match m with
    | 0 | 1 => linarith
    | n + 2 => simp [fpowerSeries]

protected theorem hasFPowerSeriesOnBall (f : E →L[𝕜] F) (x : E) :
    HasFPowerSeriesOnBall f (f.fpowerSeries x) x ∞ :=
  (f.hasFiniteFPowerSeriesOnBall x).toHasFPowerSeriesOnBall

protected theorem hasFPowerSeriesAt (f : E →L[𝕜] F) (x : E) :
    HasFPowerSeriesAt f (f.fpowerSeries x) x :=
  ⟨∞, f.hasFPowerSeriesOnBall x⟩

protected theorem cpolynomialAt (f : E →L[𝕜] F) (x : E) : CPolynomialAt 𝕜 f x :=
  (f.hasFiniteFPowerSeriesOnBall x).cpolynomialAt

protected theorem analyticAt (f : E →L[𝕜] F) (x : E) : AnalyticAt 𝕜 f x :=
  (f.hasFPowerSeriesAt x).analyticAt

protected theorem cpolynomialOn (f : E →L[𝕜] F) (s : Set E) : CPolynomialOn 𝕜 f s :=
  fun x _ ↦ f.cpolynomialAt x

protected theorem analyticOnNhd (f : E →L[𝕜] F) (s : Set E) : AnalyticOnNhd 𝕜 f s :=
  fun x _ ↦ f.analyticAt x

protected theorem analyticWithinAt (f : E →L[𝕜] F) (s : Set E) (x : E) : AnalyticWithinAt 𝕜 f s x :=
  (f.analyticAt x).analyticWithinAt

protected theorem analyticOn (f : E →L[𝕜] F) (s : Set E) : AnalyticOn 𝕜 f s :=
  fun x _ ↦ f.analyticWithinAt _ x

/-- Reinterpret a bilinear map `f : E →L[𝕜] F →L[𝕜] G` as a multilinear map
`(E × F) [×2]→L[𝕜] G`. This multilinear map is the second term in the formal
multilinear series expansion of `uncurry f`. It is given by
`f.uncurryBilinear ![(x, y), (x', y')] = f x y'`. -/
def uncurryBilinear (f : E →L[𝕜] F →L[𝕜] G) : E × F[×2]→L[𝕜] G :=
  @ContinuousLinearMap.uncurryLeft 𝕜 1 (fun _ => E × F) G _ _ _ _ _ <|
    (↑(continuousMultilinearCurryFin1 𝕜 (E × F) G).symm : (E × F →L[𝕜] G) →L[𝕜] _).comp <|
      f.bilinearComp (fst _ _ _) (snd _ _ _)

@[simp]
theorem uncurryBilinear_apply (f : E →L[𝕜] F →L[𝕜] G) (m : Fin 2 → E × F) :
    f.uncurryBilinear m = f (m 0).1 (m 1).2 :=
  rfl

/-- Formal multilinear series expansion of a bilinear function `f : E →L[𝕜] F →L[𝕜] G`. -/
def fpowerSeriesBilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) : FormalMultilinearSeries 𝕜 (E × F) G
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ (f x.1 x.2)
  | 1 => (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.deriv₂ x)
  | 2 => f.uncurryBilinear
  | _ => 0

@[simp]
theorem fpowerSeriesBilinear_apply_zero (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    fpowerSeriesBilinear f x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ (f x.1 x.2) :=
  rfl

@[simp]
theorem fpowerSeriesBilinear_apply_one (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    fpowerSeriesBilinear f x 1 = (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.deriv₂ x) :=
  rfl

@[simp]
theorem fpowerSeriesBilinear_apply_two (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    fpowerSeriesBilinear f x 2 = f.uncurryBilinear :=
  rfl

@[simp]
theorem fpowerSeriesBilinear_apply_add_three (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) (n) :
    fpowerSeriesBilinear f x (n + 3) = 0 :=
  rfl

@[simp]
theorem fpowerSeriesBilinear_radius (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    (f.fpowerSeriesBilinear x).radius = ∞ :=
  (f.fpowerSeriesBilinear x).radius_eq_top_of_forall_image_add_eq_zero 3 fun _ => rfl

protected theorem hasFPowerSeriesOnBall_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    HasFPowerSeriesOnBall (fun x : E × F => f x.1 x.2) (f.fpowerSeriesBilinear x) x ∞ :=
  { r_le := by simp
    r_pos := ENNReal.coe_lt_top
    hasSum := fun _ =>
      (hasSum_nat_add_iff' 3).1 <| by
        simp only [Finset.sum_range_succ, Prod.fst_add, Prod.snd_add, f.map_add_add]
        simp [fpowerSeriesBilinear, hasSum_zero] }

protected theorem hasFPowerSeriesAt_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    HasFPowerSeriesAt (fun x : E × F => f x.1 x.2) (f.fpowerSeriesBilinear x) x :=
  ⟨∞, f.hasFPowerSeriesOnBall_bilinear x⟩

protected theorem analyticAt_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    AnalyticAt 𝕜 (fun x : E × F => f x.1 x.2) x :=
  (f.hasFPowerSeriesAt_bilinear x).analyticAt

protected theorem analyticWithinAt_bilinear (f : E →L[𝕜] F →L[𝕜] G) (s : Set (E × F)) (x : E × F) :
    AnalyticWithinAt 𝕜 (fun x : E × F => f x.1 x.2) s x :=
  (f.analyticAt_bilinear x).analyticWithinAt

protected theorem analyticOnNhd_bilinear (f : E →L[𝕜] F →L[𝕜] G) (s : Set (E × F)) :
    AnalyticOnNhd 𝕜 (fun x : E × F => f x.1 x.2) s :=
  fun x _ ↦ f.analyticAt_bilinear x

protected theorem analyticOn_bilinear (f : E →L[𝕜] F →L[𝕜] G) (s : Set (E × F)) :
    AnalyticOn 𝕜 (fun x : E × F => f x.1 x.2) s :=
  (f.analyticOnNhd_bilinear s).analyticOn

end ContinuousLinearMap

variable {s : Set E} {z : E} {t : Set (E × F)} {p : E × F}

@[fun_prop]
lemma analyticAt_id : AnalyticAt 𝕜 (id : E → E) z :=
  (ContinuousLinearMap.id 𝕜 E).analyticAt z

lemma analyticWithinAt_id : AnalyticWithinAt 𝕜 (id : E → E) s z :=
  analyticAt_id.analyticWithinAt

/-- `id` is entire -/
theorem analyticOnNhd_id : AnalyticOnNhd 𝕜 (fun x : E ↦ x) s :=
  fun _ _ ↦ analyticAt_id

theorem analyticOn_id : AnalyticOn 𝕜 (fun x : E ↦ x) s :=
  fun _ _ ↦ analyticWithinAt_id

/-- `fst` is analytic -/
theorem analyticAt_fst : AnalyticAt 𝕜 (fun p : E × F ↦ p.fst) p :=
  (ContinuousLinearMap.fst 𝕜 E F).analyticAt p

theorem analyticWithinAt_fst : AnalyticWithinAt 𝕜 (fun p : E × F ↦ p.fst) t p :=
  analyticAt_fst.analyticWithinAt

/-- `snd` is analytic -/
theorem analyticAt_snd : AnalyticAt 𝕜 (fun p : E × F ↦ p.snd) p :=
  (ContinuousLinearMap.snd 𝕜 E F).analyticAt p

theorem analyticWithinAt_snd : AnalyticWithinAt 𝕜 (fun p : E × F ↦ p.snd) t p :=
  analyticAt_snd.analyticWithinAt

/-- `fst` is entire -/
theorem analyticOnNhd_fst : AnalyticOnNhd 𝕜 (fun p : E × F ↦ p.fst) t :=
  fun _ _ ↦ analyticAt_fst

theorem analyticOn_fst : AnalyticOn 𝕜 (fun p : E × F ↦ p.fst) t :=
  fun _ _ ↦ analyticWithinAt_fst

/-- `snd` is entire -/
theorem analyticOnNhd_snd : AnalyticOnNhd 𝕜 (fun p : E × F ↦ p.snd) t :=
  fun _ _ ↦ analyticAt_snd

theorem analyticOn_snd : AnalyticOn 𝕜 (fun p : E × F ↦ p.snd) t :=
  fun _ _ ↦ analyticWithinAt_snd

namespace ContinuousLinearEquiv

variable (f : E ≃L[𝕜] F) (s : Set E) (x : E)

protected theorem analyticAt : AnalyticAt 𝕜 f x :=
  ((f : E →L[𝕜] F).hasFPowerSeriesAt x).analyticAt

protected theorem analyticOnNhd : AnalyticOnNhd 𝕜 f s :=
  fun x _ ↦ f.analyticAt x

protected theorem analyticWithinAt : AnalyticWithinAt 𝕜 f s x :=
  (f.analyticAt x).analyticWithinAt

protected theorem analyticOn : AnalyticOn 𝕜 f s :=
  fun x _ ↦ f.analyticWithinAt _ x

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

variable (f : E ≃ₗᵢ[𝕜] F) (s : Set E) (x : E)

protected theorem analyticAt : AnalyticAt 𝕜 f x :=
  ((f : E →L[𝕜] F).hasFPowerSeriesAt x).analyticAt

protected theorem analyticOnNhd : AnalyticOnNhd 𝕜 f s :=
  fun x _ ↦ f.analyticAt x

protected theorem analyticWithinAt : AnalyticWithinAt 𝕜 f s x :=
  (f.analyticAt x).analyticWithinAt

protected theorem analyticOn : AnalyticOn 𝕜 f s :=
  fun x _ ↦ f.analyticWithinAt _ x

end LinearIsometryEquiv
