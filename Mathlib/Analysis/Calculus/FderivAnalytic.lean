/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.calculus.fderiv_analytic
! leanprover-community/mathlib commit 3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Analytic.Basic
import Mathbin.Analysis.Calculus.Deriv.Basic
import Mathbin.Analysis.Calculus.ContDiffDef

/-!
# Frechet derivatives of analytic functions.

A function expressible as a power series at a point has a Frechet derivative there.
Also the special case in terms of `deriv` when the domain is 1-dimensional.
-/


open Filter Asymptotics

open scoped ENNReal

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section fderiv

variable {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞}

variable {f : E → F} {x : E} {s : Set E}

theorem HasFPowerSeriesAt.hasStrictFDerivAt (h : HasFPowerSeriesAt f p x) :
    HasStrictFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x :=
  by
  refine' h.is_O_image_sub_norm_mul_norm_sub.trans_is_o (is_o.of_norm_right _)
  refine' is_o_iff_exists_eq_mul.2 ⟨fun y => ‖y - (x, x)‖, _, eventually_eq.rfl⟩
  refine' (continuous_id.sub continuous_const).norm.tendsto' _ _ _
  rw [_root_.id, sub_self, norm_zero]
#align has_fpower_series_at.has_strict_fderiv_at HasFPowerSeriesAt.hasStrictFDerivAt

theorem HasFPowerSeriesAt.hasFDerivAt (h : HasFPowerSeriesAt f p x) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x :=
  h.HasStrictFDerivAt.HasFDerivAt
#align has_fpower_series_at.has_fderiv_at HasFPowerSeriesAt.hasFDerivAt

theorem HasFPowerSeriesAt.differentiableAt (h : HasFPowerSeriesAt f p x) : DifferentiableAt 𝕜 f x :=
  h.HasFDerivAt.DifferentiableAt
#align has_fpower_series_at.differentiable_at HasFPowerSeriesAt.differentiableAt

theorem AnalyticAt.differentiableAt : AnalyticAt 𝕜 f x → DifferentiableAt 𝕜 f x
  | ⟨p, hp⟩ => hp.DifferentiableAt
#align analytic_at.differentiable_at AnalyticAt.differentiableAt

theorem AnalyticAt.differentiableWithinAt (h : AnalyticAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x :=
  h.DifferentiableAt.DifferentiableWithinAt
#align analytic_at.differentiable_within_at AnalyticAt.differentiableWithinAt

theorem HasFPowerSeriesAt.fderiv_eq (h : HasFPowerSeriesAt f p x) :
    fderiv 𝕜 f x = continuousMultilinearCurryFin1 𝕜 E F (p 1) :=
  h.HasFDerivAt.fderiv
#align has_fpower_series_at.fderiv_eq HasFPowerSeriesAt.fderiv_eq

theorem HasFPowerSeriesOnBall.differentiableOn [CompleteSpace F]
    (h : HasFPowerSeriesOnBall f p x r) : DifferentiableOn 𝕜 f (EMetric.ball x r) := fun y hy =>
  (h.analyticAt_of_mem hy).DifferentiableWithinAt
#align has_fpower_series_on_ball.differentiable_on HasFPowerSeriesOnBall.differentiableOn

theorem AnalyticOn.differentiableOn (h : AnalyticOn 𝕜 f s) : DifferentiableOn 𝕜 f s := fun y hy =>
  (h y hy).DifferentiableWithinAt
#align analytic_on.differentiable_on AnalyticOn.differentiableOn

theorem HasFPowerSeriesOnBall.hasFDerivAt [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y) :=
  (h.changeOrigin hy).HasFPowerSeriesAt.HasFDerivAt
#align has_fpower_series_on_ball.has_fderiv_at HasFPowerSeriesOnBall.hasFDerivAt

theorem HasFPowerSeriesOnBall.fderiv_eq [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    fderiv 𝕜 f (x + y) = continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1) :=
  (h.HasFDerivAt hy).fderiv
#align has_fpower_series_on_ball.fderiv_eq HasFPowerSeriesOnBall.fderiv_eq

/-- If a function has a power series on a ball, then so does its derivative. -/
theorem HasFPowerSeriesOnBall.fderiv [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (fderiv 𝕜 f)
      ((continuousMultilinearCurryFin1 𝕜 E F :
            (E[×1]→L[𝕜] F) →L[𝕜] E →L[𝕜] F).compFormalMultilinearSeries
        (p.changeOriginSeries 1))
      x r :=
  by
  suffices A :
    HasFPowerSeriesOnBall
      (fun z => continuousMultilinearCurryFin1 𝕜 E F (p.change_origin (z - x) 1))
      ((continuousMultilinearCurryFin1 𝕜 E F :
            (E[×1]→L[𝕜] F) →L[𝕜] E →L[𝕜] F).compFormalMultilinearSeries
        (p.change_origin_series 1))
      x r
  · apply A.congr
    intro z hz
    dsimp
    rw [← h.fderiv_eq, add_sub_cancel'_right]
    simpa only [edist_eq_coe_nnnorm_sub, EMetric.mem_ball] using hz
  suffices B :
    HasFPowerSeriesOnBall (fun z => p.change_origin (z - x) 1) (p.change_origin_series 1) x r
  exact
    (continuousMultilinearCurryFin1 𝕜 E
              F).toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesOnBall
      B
  simpa using
    ((p.has_fpower_series_on_ball_change_origin 1 (h.r_pos.trans_le h.r_le)).mono h.r_pos
          h.r_le).comp_sub
      x
#align has_fpower_series_on_ball.fderiv HasFPowerSeriesOnBall.fderiv

/-- If a function is analytic on a set `s`, so is its Fréchet derivative. -/
theorem AnalyticOn.fderiv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (fderiv 𝕜 f) s :=
  by
  intro y hy
  rcases h y hy with ⟨p, r, hp⟩
  exact hp.fderiv.analytic_at
#align analytic_on.fderiv AnalyticOn.fderiv

/-- If a function is analytic on a set `s`, so are its successive Fréchet derivative. -/
theorem AnalyticOn.iteratedFDeriv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) (n : ℕ) :
    AnalyticOn 𝕜 (iteratedFDeriv 𝕜 n f) s :=
  by
  induction' n with n IH
  · rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm : F →L[𝕜] E[×0]→L[𝕜] F).comp_analyticOn h
  · rw [iteratedFDeriv_succ_eq_comp_left]
    apply
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun i : Fin (n + 1) => E)
              F).toContinuousLinearEquiv.toContinuousLinearMap.comp_analyticOn
    exact IH.fderiv
#align analytic_on.iterated_fderiv AnalyticOn.iteratedFDeriv

/-- An analytic function is infinitely differentiable. -/
theorem AnalyticOn.contDiffOn [CompleteSpace F] (h : AnalyticOn 𝕜 f s) {n : ℕ∞} :
    ContDiffOn 𝕜 n f s := by
  let t := { x | AnalyticAt 𝕜 f x }
  suffices : ContDiffOn 𝕜 n f t; exact this.mono h
  have H : AnalyticOn 𝕜 f t := fun x hx => hx
  have t_open : IsOpen t := isOpen_analyticAt 𝕜 f
  apply contDiffOn_of_continuousOn_differentiableOn
  · intro m hm
    apply (H.iterated_fderiv m).ContinuousOn.congr
    intro x hx
    exact iteratedFDerivWithin_of_isOpen _ t_open hx
  · intro m hm
    apply (H.iterated_fderiv m).DifferentiableOn.congr
    intro x hx
    exact iteratedFDerivWithin_of_isOpen _ t_open hx
#align analytic_on.cont_diff_on AnalyticOn.contDiffOn

end fderiv

section deriv

variable {p : FormalMultilinearSeries 𝕜 𝕜 F} {r : ℝ≥0∞}

variable {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}

protected theorem HasFPowerSeriesAt.hasStrictDerivAt (h : HasFPowerSeriesAt f p x) :
    HasStrictDerivAt f (p 1 fun _ => 1) x :=
  h.HasStrictFDerivAt.HasStrictDerivAt
#align has_fpower_series_at.has_strict_deriv_at HasFPowerSeriesAt.hasStrictDerivAt

protected theorem HasFPowerSeriesAt.hasDerivAt (h : HasFPowerSeriesAt f p x) :
    HasDerivAt f (p 1 fun _ => 1) x :=
  h.HasStrictDerivAt.HasDerivAt
#align has_fpower_series_at.has_deriv_at HasFPowerSeriesAt.hasDerivAt

protected theorem HasFPowerSeriesAt.deriv (h : HasFPowerSeriesAt f p x) :
    deriv f x = p 1 fun _ => 1 :=
  h.HasDerivAt.deriv
#align has_fpower_series_at.deriv HasFPowerSeriesAt.deriv

/-- If a function is analytic on a set `s`, so is its derivative. -/
theorem AnalyticOn.deriv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (deriv f) s :=
  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_analyticOn h.fderiv
#align analytic_on.deriv AnalyticOn.deriv

/-- If a function is analytic on a set `s`, so are its successive derivatives. -/
theorem AnalyticOn.iterated_deriv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) (n : ℕ) :
    AnalyticOn 𝕜 ((deriv^[n]) f) s := by
  induction' n with n IH
  · exact h
  · simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv
#align analytic_on.iterated_deriv AnalyticOn.iterated_deriv

end deriv

