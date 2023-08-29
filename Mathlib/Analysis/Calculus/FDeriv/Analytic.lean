/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiffDef

#align_import analysis.calculus.fderiv_analytic from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Frechet derivatives of analytic functions.

A function expressible as a power series at a point has a Frechet derivative there.
Also the special case in terms of `deriv` when the domain is 1-dimensional.
-/


open Filter Asymptotics

open scoped ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section fderiv

variable {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞}

variable {f : E → F} {x : E} {s : Set E}

theorem HasFPowerSeriesAt.hasStrictFDerivAt (h : HasFPowerSeriesAt f p x) :
    HasStrictFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x := by
  refine' h.isBigO_image_sub_norm_mul_norm_sub.trans_isLittleO (IsLittleO.of_norm_right _)
  -- ⊢ (fun y => ‖y - (x, x)‖ * ‖y.fst - y.snd‖) =o[nhds (x, x)] fun x => ‖x.fst -  …
  refine' isLittleO_iff_exists_eq_mul.2 ⟨fun y => ‖y - (x, x)‖, _, EventuallyEq.rfl⟩
  -- ⊢ Tendsto (fun y => ‖y - (x, x)‖) (nhds (x, x)) (nhds 0)
  refine' (continuous_id.sub continuous_const).norm.tendsto' _ _ _
  -- ⊢ ‖id (x, x) - (x, x)‖ = 0
  rw [_root_.id, sub_self, norm_zero]
  -- 🎉 no goals
#align has_fpower_series_at.has_strict_fderiv_at HasFPowerSeriesAt.hasStrictFDerivAt

theorem HasFPowerSeriesAt.hasFDerivAt (h : HasFPowerSeriesAt f p x) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x :=
  h.hasStrictFDerivAt.hasFDerivAt
#align has_fpower_series_at.has_fderiv_at HasFPowerSeriesAt.hasFDerivAt

theorem HasFPowerSeriesAt.differentiableAt (h : HasFPowerSeriesAt f p x) : DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt
#align has_fpower_series_at.differentiable_at HasFPowerSeriesAt.differentiableAt

theorem AnalyticAt.differentiableAt : AnalyticAt 𝕜 f x → DifferentiableAt 𝕜 f x
  | ⟨_, hp⟩ => hp.differentiableAt
#align analytic_at.differentiable_at AnalyticAt.differentiableAt

theorem AnalyticAt.differentiableWithinAt (h : AnalyticAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x :=
  h.differentiableAt.differentiableWithinAt
#align analytic_at.differentiable_within_at AnalyticAt.differentiableWithinAt

theorem HasFPowerSeriesAt.fderiv_eq (h : HasFPowerSeriesAt f p x) :
    fderiv 𝕜 f x = continuousMultilinearCurryFin1 𝕜 E F (p 1) :=
  h.hasFDerivAt.fderiv
#align has_fpower_series_at.fderiv_eq HasFPowerSeriesAt.fderiv_eq

theorem HasFPowerSeriesOnBall.differentiableOn [CompleteSpace F]
    (h : HasFPowerSeriesOnBall f p x r) : DifferentiableOn 𝕜 f (EMetric.ball x r) := fun _ hy =>
  (h.analyticAt_of_mem hy).differentiableWithinAt
#align has_fpower_series_on_ball.differentiable_on HasFPowerSeriesOnBall.differentiableOn

theorem AnalyticOn.differentiableOn (h : AnalyticOn 𝕜 f s) : DifferentiableOn 𝕜 f s := fun y hy =>
  (h y hy).differentiableWithinAt
#align analytic_on.differentiable_on AnalyticOn.differentiableOn

theorem HasFPowerSeriesOnBall.hasFDerivAt [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y) :=
  (h.changeOrigin hy).hasFPowerSeriesAt.hasFDerivAt
#align has_fpower_series_on_ball.has_fderiv_at HasFPowerSeriesOnBall.hasFDerivAt

theorem HasFPowerSeriesOnBall.fderiv_eq [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    fderiv 𝕜 f (x + y) = continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1) :=
  (h.hasFDerivAt hy).fderiv
#align has_fpower_series_on_ball.fderiv_eq HasFPowerSeriesOnBall.fderiv_eq

/-- If a function has a power series on a ball, then so does its derivative. -/
theorem HasFPowerSeriesOnBall.fderiv [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (fderiv 𝕜 f)
      ((continuousMultilinearCurryFin1 𝕜 E F :
            (E[×1]→L[𝕜] F) →L[𝕜] E →L[𝕜] F).compFormalMultilinearSeries
        (p.changeOriginSeries 1))
      x r := by
  suffices A :
    HasFPowerSeriesOnBall
      (fun z => continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin (z - x) 1))
      ((continuousMultilinearCurryFin1 𝕜 E F :
            (E[×1]→L[𝕜] F) →L[𝕜] E →L[𝕜] F).compFormalMultilinearSeries
        (p.changeOriginSeries 1))
      x r
  · apply A.congr
    -- ⊢ Set.EqOn (fun z => ↑(continuousMultilinearCurryFin1 𝕜 E F) (FormalMultilinea …
    intro z hz
    -- ⊢ (fun z => ↑(continuousMultilinearCurryFin1 𝕜 E F) (FormalMultilinearSeries.c …
    dsimp
    -- ⊢ ↑(continuousMultilinearCurryFin1 𝕜 E F) (FormalMultilinearSeries.changeOrigi …
    rw [← h.fderiv_eq, add_sub_cancel'_right]
    -- ⊢ ↑‖z - x‖₊ < r
    simpa only [edist_eq_coe_nnnorm_sub, EMetric.mem_ball] using hz
    -- 🎉 no goals
  suffices B :
    HasFPowerSeriesOnBall (fun z => p.changeOrigin (z - x) 1) (p.changeOriginSeries 1) x r
  exact
    (continuousMultilinearCurryFin1 𝕜 E
              F).toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesOnBall
      B
  simpa using
    ((p.hasFPowerSeriesOnBall_changeOrigin 1 (h.r_pos.trans_le h.r_le)).mono h.r_pos
          h.r_le).comp_sub
      x
#align has_fpower_series_on_ball.fderiv HasFPowerSeriesOnBall.fderiv

/-- If a function is analytic on a set `s`, so is its Fréchet derivative. -/
theorem AnalyticOn.fderiv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (fderiv 𝕜 f) s := by
  intro y hy
  -- ⊢ AnalyticAt 𝕜 (_root_.fderiv 𝕜 f) y
  rcases h y hy with ⟨p, r, hp⟩
  -- ⊢ AnalyticAt 𝕜 (_root_.fderiv 𝕜 f) y
  exact hp.fderiv.analyticAt
  -- 🎉 no goals
#align analytic_on.fderiv AnalyticOn.fderiv

/-- If a function is analytic on a set `s`, so are its successive Fréchet derivative. -/
theorem AnalyticOn.iteratedFDeriv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) (n : ℕ) :
    AnalyticOn 𝕜 (iteratedFDeriv 𝕜 n f) s := by
  induction' n with n IH
  -- ⊢ AnalyticOn 𝕜 (_root_.iteratedFDeriv 𝕜 Nat.zero f) s
  · rw [iteratedFDeriv_zero_eq_comp]
    -- ⊢ AnalyticOn 𝕜 (↑(LinearIsometryEquiv.symm (continuousMultilinearCurryFin0 𝕜 E …
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm : F →L[𝕜] E[×0]→L[𝕜] F).comp_analyticOn h
    -- 🎉 no goals
  · rw [iteratedFDeriv_succ_eq_comp_left]
    -- ⊢ AnalyticOn 𝕜 (↑(continuousMultilinearCurryLeftEquiv 𝕜 (fun x => E) F) ∘ _roo …
    -- Porting note: for reasons that I do not understand at all, `?g` cannot be inlined.
    convert @ContinuousLinearMap.comp_analyticOn 𝕜 E
      ?_ (ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ E) F)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      s ?g IH.fderiv
    case g =>
      exact ↑(continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F)
    rfl
    -- 🎉 no goals
#align analytic_on.iterated_fderiv AnalyticOn.iteratedFDeriv

/-- An analytic function is infinitely differentiable. -/
theorem AnalyticOn.contDiffOn [CompleteSpace F] (h : AnalyticOn 𝕜 f s) {n : ℕ∞} :
    ContDiffOn 𝕜 n f s := by
  let t := { x | AnalyticAt 𝕜 f x }
  -- ⊢ ContDiffOn 𝕜 n f s
  suffices : ContDiffOn 𝕜 n f t; exact this.mono h
  -- ⊢ ContDiffOn 𝕜 n f s
                                 -- ⊢ ContDiffOn 𝕜 n f t
  have H : AnalyticOn 𝕜 f t := fun x hx => hx
  -- ⊢ ContDiffOn 𝕜 n f t
  have t_open : IsOpen t := isOpen_analyticAt 𝕜 f
  -- ⊢ ContDiffOn 𝕜 n f t
  apply contDiffOn_of_continuousOn_differentiableOn
  -- ⊢ ∀ (m : ℕ), ↑m ≤ n → ContinuousOn (fun x => iteratedFDerivWithin 𝕜 m f t x) t
  · rintro m -
    -- ⊢ ContinuousOn (fun x => iteratedFDerivWithin 𝕜 m f t x) t
    apply (H.iteratedFDeriv m).continuousOn.congr
    -- ⊢ Set.EqOn (fun x => iteratedFDerivWithin 𝕜 m f t x) (_root_.iteratedFDeriv 𝕜  …
    intro x hx
    -- ⊢ (fun x => iteratedFDerivWithin 𝕜 m f t x) x = _root_.iteratedFDeriv 𝕜 m f x
    exact iteratedFDerivWithin_of_isOpen _ t_open hx
    -- 🎉 no goals
  · rintro m -
    -- ⊢ DifferentiableOn 𝕜 (fun x => iteratedFDerivWithin 𝕜 m f t x) t
    apply (H.iteratedFDeriv m).differentiableOn.congr
    -- ⊢ ∀ (x : E), x ∈ t → iteratedFDerivWithin 𝕜 m f t x = _root_.iteratedFDeriv 𝕜  …
    intro x hx
    -- ⊢ iteratedFDerivWithin 𝕜 m f t x = _root_.iteratedFDeriv 𝕜 m f x
    exact iteratedFDerivWithin_of_isOpen _ t_open hx
    -- 🎉 no goals
#align analytic_on.cont_diff_on AnalyticOn.contDiffOn

theorem AnalyticAt.contDiffAt [CompleteSpace F] (h : AnalyticAt 𝕜 f x) {n : ℕ∞} :
    ContDiffAt 𝕜 n f x := by
  obtain ⟨s, hs, hf⟩ := h.exists_mem_nhds_analyticOn
  -- ⊢ ContDiffAt 𝕜 n f x
  exact hf.contDiffOn.contDiffAt hs
  -- 🎉 no goals

end fderiv

section deriv

variable {p : FormalMultilinearSeries 𝕜 𝕜 F} {r : ℝ≥0∞}

variable {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}

protected theorem HasFPowerSeriesAt.hasStrictDerivAt (h : HasFPowerSeriesAt f p x) :
    HasStrictDerivAt f (p 1 fun _ => 1) x :=
  h.hasStrictFDerivAt.hasStrictDerivAt
#align has_fpower_series_at.has_strict_deriv_at HasFPowerSeriesAt.hasStrictDerivAt

protected theorem HasFPowerSeriesAt.hasDerivAt (h : HasFPowerSeriesAt f p x) :
    HasDerivAt f (p 1 fun _ => 1) x :=
  h.hasStrictDerivAt.hasDerivAt
#align has_fpower_series_at.has_deriv_at HasFPowerSeriesAt.hasDerivAt

protected theorem HasFPowerSeriesAt.deriv (h : HasFPowerSeriesAt f p x) :
    deriv f x = p 1 fun _ => 1 :=
  h.hasDerivAt.deriv
#align has_fpower_series_at.deriv HasFPowerSeriesAt.deriv

/-- If a function is analytic on a set `s`, so is its derivative. -/
theorem AnalyticOn.deriv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (deriv f) s :=
  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_analyticOn h.fderiv
#align analytic_on.deriv AnalyticOn.deriv

/-- If a function is analytic on a set `s`, so are its successive derivatives. -/
theorem AnalyticOn.iterated_deriv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) (n : ℕ) :
    AnalyticOn 𝕜 (_root_.deriv^[n] f) s := by
  induction' n with n IH
  -- ⊢ AnalyticOn 𝕜 (_root_.deriv^[Nat.zero] f) s
  · exact h
    -- 🎉 no goals
  · simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv
    -- 🎉 no goals
#align analytic_on.iterated_deriv AnalyticOn.iterated_deriv

end deriv
