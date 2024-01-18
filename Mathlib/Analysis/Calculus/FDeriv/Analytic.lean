/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

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
  refine' isLittleO_iff_exists_eq_mul.2 ⟨fun y => ‖y - (x, x)‖, _, EventuallyEq.rfl⟩
  refine' (continuous_id.sub continuous_const).norm.tendsto' _ _ _
  rw [_root_.id, sub_self, norm_zero]
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
      ((continuousMultilinearCurryFin1 𝕜 E F : (E[×1]→L[𝕜] F) →L[𝕜] E →L[𝕜] F)
        |>.compFormalMultilinearSeries (p.changeOriginSeries 1)) x r := by
  refine .congr (f := fun z ↦ continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin (z - x) 1)) ?_
    fun z hz ↦ ?_
  · refine continuousMultilinearCurryFin1 𝕜 E F
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesOnBall ?_
    simpa using ((p.hasFPowerSeriesOnBall_changeOrigin 1
      (h.r_pos.trans_le h.r_le)).mono h.r_pos h.r_le).comp_sub x
  dsimp only
  rw [← h.fderiv_eq, add_sub_cancel'_right]
  simpa only [edist_eq_coe_nnnorm_sub, EMetric.mem_ball] using hz
#align has_fpower_series_on_ball.fderiv HasFPowerSeriesOnBall.fderiv

/-- If a function is analytic on a set `s`, so is its Fréchet derivative. -/
theorem AnalyticOn.fderiv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (fderiv 𝕜 f) s := by
  intro y hy
  rcases h y hy with ⟨p, r, hp⟩
  exact hp.fderiv.analyticAt
#align analytic_on.fderiv AnalyticOn.fderiv

/-- If a function is analytic on a set `s`, so are its successive Fréchet derivative. -/
theorem AnalyticOn.iteratedFDeriv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) (n : ℕ) :
    AnalyticOn 𝕜 (iteratedFDeriv 𝕜 n f) s := by
  induction' n with n IH
  · rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm : F →L[𝕜] E[×0]→L[𝕜] F).comp_analyticOn h
  · rw [iteratedFDeriv_succ_eq_comp_left]
    -- Porting note: for reasons that I do not understand at all, `?g` cannot be inlined.
    convert ContinuousLinearMap.comp_analyticOn ?g IH.fderiv
    case g => exact ↑(continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E) F)
    simp
#align analytic_on.iterated_fderiv AnalyticOn.iteratedFDeriv

/-- An analytic function is infinitely differentiable. -/
theorem AnalyticOn.contDiffOn [CompleteSpace F] (h : AnalyticOn 𝕜 f s) {n : ℕ∞} :
    ContDiffOn 𝕜 n f s :=
  let t := { x | AnalyticAt 𝕜 f x }
  suffices ContDiffOn 𝕜 n f t from this.mono h
  have H : AnalyticOn 𝕜 f t := fun _x hx ↦ hx
  have t_open : IsOpen t := isOpen_analyticAt 𝕜 f
  contDiffOn_of_continuousOn_differentiableOn
    (fun m _ ↦ (H.iteratedFDeriv m).continuousOn.congr
      fun  _ hx ↦ iteratedFDerivWithin_of_isOpen _ t_open hx)
    (fun m _ ↦ (H.iteratedFDeriv m).differentiableOn.congr
      fun _ hx ↦ iteratedFDerivWithin_of_isOpen _ t_open hx)
#align analytic_on.cont_diff_on AnalyticOn.contDiffOn

theorem AnalyticAt.contDiffAt [CompleteSpace F] (h : AnalyticAt 𝕜 f x) {n : ℕ∞} :
    ContDiffAt 𝕜 n f x := by
  obtain ⟨s, hs, hf⟩ := h.exists_mem_nhds_analyticOn
  exact hf.contDiffOn.contDiffAt hs

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
  · exact h
  · simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv
#align analytic_on.iterated_deriv AnalyticOn.iterated_deriv

end deriv
section fderiv

variable {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞} {n : ℕ}

variable {f : E → F} {x : E} {s : Set E}

/-! The case of continuously polynomial functions. We get the same differentiability
results as for analytic functions, but without the assumptions that `F` is complete.-/

theorem HasFiniteFPowerSeriesOnBall.differentiableOn
    (h : HasFiniteFPowerSeriesOnBall f p x n r) : DifferentiableOn 𝕜 f (EMetric.ball x r) :=
  fun _ hy ↦ (h.cPolynomialAt_of_mem hy).analyticAt.differentiableWithinAt

theorem HasFiniteFPowerSeriesOnBall.hasFDerivAt (h : HasFiniteFPowerSeriesOnBall f p x n r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y) :=
  (h.changeOrigin hy).toHasFPowerSeriesOnBall.hasFPowerSeriesAt.hasFDerivAt

theorem HasFiniteFPowerSeriesOnBall.fderiv_eq (h : HasFiniteFPowerSeriesOnBall f p x n r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    fderiv 𝕜 f (x + y) = continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1) :=
  (h.hasFDerivAt hy).fderiv

/-- If a function has a finite power series on a ball, then so does its derivative. -/
protected theorem HasFiniteFPowerSeriesOnBall.fderiv
    (h : HasFiniteFPowerSeriesOnBall f p x (n + 1) r) :
    HasFiniteFPowerSeriesOnBall (fderiv 𝕜 f)
      ((continuousMultilinearCurryFin1 𝕜 E F : (E[×1]→L[𝕜] F) →L[𝕜] E →L[𝕜] F)
        |>.compFormalMultilinearSeries (p.changeOriginSeries 1)) x n r := by
  refine .congr (f := fun z ↦ continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin (z - x) 1)) ?_
    fun z hz ↦ ?_
  · refine continuousMultilinearCurryFin1 𝕜 E F
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall ?_
    simpa using
      ((p.hasFiniteFPowerSeriesOnBall_changeOrigin 1 h.finite).mono h.r_pos le_top).comp_sub x
  dsimp only
  rw [← h.fderiv_eq, add_sub_cancel'_right]
  simpa only [edist_eq_coe_nnnorm_sub, EMetric.mem_ball] using hz

/-- If a function has a finite power series on a ball, then so does its derivative.
This is a variant of `HasFiniteFPowerSeriesOnBall.fderiv` where the degree of `f` is `< n`
and not `< n + 1`. -/
theorem HasFiniteFPowerSeriesOnBall.fderiv' (h : HasFiniteFPowerSeriesOnBall f p x n r) :
    HasFiniteFPowerSeriesOnBall (fderiv 𝕜 f)
      ((continuousMultilinearCurryFin1 𝕜 E F : (E[×1]→L[𝕜] F) →L[𝕜] E →L[𝕜] F)
        |>.compFormalMultilinearSeries (p.changeOriginSeries 1)) x (n - 1) r := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [zero_tsub]
    refine HasFiniteFPowerSeriesOnBall.bound_zero_of_eq_zero (fun y hy ↦ ?_) h.r_pos fun n ↦ ?_
    · rw [Filter.EventuallyEq.fderiv_eq (f := fun _ ↦ 0)]
      · rw [fderiv_const, Pi.zero_apply]
      · exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨EMetric.ball x r,
          EMetric.isOpen_ball.mem_nhds hy, fun z hz ↦ by rw [h.eq_zero_of_bound_zero z hz]⟩
    · apply ContinuousMultilinearMap.ext; intro a
      change (continuousMultilinearCurryFin1 𝕜 E F) (p.changeOriginSeries 1 n a) = 0
      rw [p.changeOriginSeries_finite_of_finite h.finite 1 (Nat.zero_le _)]
      exact map_zero _
  · rw [← Nat.succ_pred hn] at h
    exact h.fderiv

/-- If a function is polynomial on a set `s`, so is its Fréchet derivative. -/
theorem CPolynomialOn.fderiv (h : CPolynomialOn 𝕜 f s) :
    CPolynomialOn 𝕜 (fderiv 𝕜 f) s := by
  intro y hy
  rcases h y hy with ⟨p, r, n, hp⟩
  exact hp.fderiv'.cPolynomialAt

/-- If a function is polynomial on a set `s`, so are its successive Fréchet derivative. -/
theorem CPolynomialOn.iteratedFDeriv (h : CPolynomialOn 𝕜 f s) (n : ℕ) :
    CPolynomialOn 𝕜 (iteratedFDeriv 𝕜 n f) s := by
  induction' n with n IH
  · rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm : F →L[𝕜] E[×0]→L[𝕜] F).comp_cPolynomialOn h
  · rw [iteratedFDeriv_succ_eq_comp_left]
    convert ContinuousLinearMap.comp_cPolynomialOn ?g IH.fderiv
    case g => exact ↑(continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E) F)
    simp

/-- A polynomial function is infinitely differentiable. -/
theorem CPolynomialOn.contDiffOn (h : CPolynomialOn 𝕜 f s) {n : ℕ∞} :
    ContDiffOn 𝕜 n f s :=
  let t := { x | CPolynomialAt 𝕜 f x }
  suffices ContDiffOn 𝕜 n f t from this.mono h
  have H : CPolynomialOn 𝕜 f t := fun _x hx ↦ hx
  have t_open : IsOpen t := isOpen_cPolynomialAt 𝕜 f
  contDiffOn_of_continuousOn_differentiableOn
    (fun m _ ↦ (H.iteratedFDeriv m).continuousOn.congr
      fun  _ hx ↦ iteratedFDerivWithin_of_isOpen _ t_open hx)
    (fun m _ ↦ (H.iteratedFDeriv m).analyticOn.differentiableOn.congr
      fun _ hx ↦ iteratedFDerivWithin_of_isOpen _ t_open hx)

theorem CPolynomialAt.contDiffAt (h : CPolynomialAt 𝕜 f x) {n : ℕ∞} :
    ContDiffAt 𝕜 n f x :=
  let ⟨_, hs, hf⟩ := h.exists_mem_nhds_cPolynomialOn
  hf.contDiffOn.contDiffAt hs

end fderiv

section deriv

variable {p : FormalMultilinearSeries 𝕜 𝕜 F} {r : ℝ≥0∞}

variable {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}

/-- If a function is polynomial on a set `s`, so is its derivative. -/
protected theorem CPolynomialOn.deriv (h : CPolynomialOn 𝕜 f s) : CPolynomialOn 𝕜 (deriv f) s :=
  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_cPolynomialOn h.fderiv

/-- If a function is polynomial on a set `s`, so are its successive derivatives. -/
theorem CPolynomialOn.iterated_deriv (h : CPolynomialOn 𝕜 f s) (n : ℕ) :
    CPolynomialOn 𝕜 (deriv^[n] f) s := by
  induction' n with n IH
  · exact h
  · simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv

end deriv

namespace ContinuousMultilinearMap

--TODO: move to appropriate place

variable {R : Type*} {ι : Type*} {M₁ : ι → Type*} {M₂ : Type*} [Ring R]
  [(i : ι) → AddCommGroup (M₁ i)] [AddCommGroup M₂] [(i : ι) → Module R (M₁ i)] [Module R M₂]
  [(i : ι) → TopologicalSpace (M₁ i)] [(i : ι) → TopologicalAddGroup (M₁ i)]
  [(i : ι) → ContinuousConstSMul R (M₁ i)] [TopologicalSpace M₂] [TopologicalAddGroup M₂]
  [ContinuousConstSMul R M₂] [Fintype ι] (f : ContinuousMultilinearMap R M₁ M₂)

/-- Realize a ContinuousMultilinearMap on `∀ i : ι, M₁ i` as the evaluation of a
FormalMultilinearSeries by choosing an arbitrary identification `ι ≃ Fin (Fintype.card ι)`. -/
noncomputable def toFormalMultilinearSeries : FormalMultilinearSeries R (∀ i, M₁ i) M₂ :=
  fun n ↦ if h : Fintype.card ι = n then
    (f.compContinuousLinearMap ContinuousLinearMap.proj).domDomCongr (Fintype.equivFinOfCardEq h)
  else 0

open scoped BigOperators

/-- The derivative of a continuous multilinear map, as a continuous linear map
from `∀ i, M₁ i` to `M₂`; see `ContinuousMultilinearMap.hasFDerivAt`. -/
def linearDeriv [DecidableEq ι] (x : (i : ι) → M₁ i) : ((i : ι) → M₁ i) →L[R] M₂ :=
  ∑ i : ι, (f.toContinuousLinearMap x i).comp (.proj i)

@[simp]
lemma linearDeriv_apply [DecidableEq ι] (f : ContinuousMultilinearMap R M₁ M₂)
    (x y : (i : ι) → M₁ i) :
    f.linearDeriv x y = ∑ i, f (Function.update x i (y i)) := by
  unfold linearDeriv toContinuousLinearMap
  simp only [ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, LinearMap.coe_toAddHom, Finset.sum_apply,
    Function.comp_apply, ContinuousLinearMap.proj_apply, MultilinearMap.toLinearMap_apply, coe_coe]

variable {R : Type*} {ι : Type*} {M₁ : ι → Type*} {M₂ : Type*} [NontriviallyNormedField R]
  [(i : ι) → NormedAddCommGroup (M₁ i)] [NormedAddCommGroup M₂] [(i : ι) → NormedSpace R (M₁ i)]
  [NormedSpace R M₂] [Fintype ι] (f : ContinuousMultilinearMap R M₁ M₂)

open FormalMultilinearSeries

protected theorem hasFiniteFPowerSeriesOnBall :
    HasFiniteFPowerSeriesOnBall f f.toFormalMultilinearSeries 0 (Fintype.card ι + 1) ⊤ :=
  .mk' (fun m hm ↦ dif_neg (Nat.succ_le_iff.mp hm).ne) ENNReal.zero_lt_top fun y _ ↦ by
    rw [Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _), zero_add]
    · rw [toFormalMultilinearSeries, dif_pos rfl]; rfl
    · intro m _ ne; rw [toFormalMultilinearSeries, dif_neg ne.symm]; rfl

theorem changeOriginSeries_support (f : ContinuousMultilinearMap R M₁ M₂) {k l : ℕ}
    (h : k + l ≠ Fintype.card ι) :
    f.toFormalMultilinearSeries.changeOriginSeries k l = 0 := by
  unfold FormalMultilinearSeries.changeOriginSeries
  exact Finset.sum_eq_zero (fun _ _ ↦ by
    rw [FormalMultilinearSeries.changeOriginSeriesTerm, AddEquivClass.map_eq_zero_iff]
    simp only [toFormalMultilinearSeries, Ne.symm h, dite_false])

open Finset in
theorem changeOrigin_toFormalMultilinearSeries [DecidableEq ι] (x : ∀ i, M₁ i) :
    continuousMultilinearCurryFin1 R (∀ i, M₁ i) M₂ (f.toFormalMultilinearSeries.changeOrigin x 1) =
    f.linearDeriv x := by
  ext y
  simp only [continuousMultilinearCurryFin1_apply, linearDeriv_apply]
  rw [FormalMultilinearSeries.changeOrigin, FormalMultilinearSeries.sum,
    tsum_eq_single (Fintype.card ι - 1)]
  · by_cases he : IsEmpty ι
    · simp only [univ_eq_empty, sum_empty]
      letI := he
      rw [Fintype.card_eq_zero, Nat.zero_sub, changeOriginSeries_support, zero_apply, zero_apply]
      rw [Fintype.card_eq_zero, add_zero]
      exact Nat.one_ne_zero
    · have heq : Fin.snoc 0 y = (fun _ : Fin (0 + 1) ↦ y) := by
        ext _ _
        unfold Fin.snoc
        simp only [Fin.coe_fin_one, lt_self_iff_false, Fin.castSucc_castLT, Pi.zero_apply,
          cast_eq, dite_eq_ite, ite_false]
      rw [FormalMultilinearSeries.changeOriginSeries, ContinuousMultilinearMap.sum_apply,
        ContinuousMultilinearMap.sum_apply, heq]
      have hcard : Fintype.card ι = 1 + (Fintype.card ι - 1) := by
        letI := not_isEmpty_iff.mp he
        rw [← Nat.succ_eq_one_add, ← Nat.pred_eq_sub_one, Nat.succ_pred Fintype.card_ne_zero]
      set I : (i : ι) → i ∈ Finset.univ → {s : Finset (Fin (1 + (Fintype.card ι - 1))) //
          s.card = Fintype.card ι - 1} := by
        intro i _
        refine ⟨Finset.univ.erase (Fintype.equivFinOfCardEq hcard i), ?_⟩
        simp only [mem_univ, card_erase_of_mem, card_fin, add_tsub_cancel_left]
      rw [sum_bij I (fun _ _ ↦ mem_univ _) (fun _ _ _ _ ↦ by
          simp only [mem_univ, not_true_eq_false, Subtype.mk.injEq,
          erase_inj _ (mem_univ _), Equiv.apply_eq_iff_eq, imp_self])]
      · intro ⟨s, hs⟩ _
        have h : sᶜ.card = 1 := by
          rw [Finset.card_compl, hs]
          simp only [ge_iff_le, Fintype.card_fin, add_le_iff_nonpos_left, nonpos_iff_eq_zero,
            add_tsub_cancel_right]
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
        existsi ((Fintype.equivFinOfCardEq hcard).symm a), Finset.mem_univ _
        simp only [mem_univ, not_true_eq_false, Equiv.apply_symm_apply, Subtype.mk.injEq]
        rw [Finset.erase_eq, ← ha]
        simp only [sdiff_compl, ge_iff_le, le_eq_subset, subset_univ, inf_of_le_right]
      · intro i _
        rw [FormalMultilinearSeries.changeOriginSeriesTerm_apply, toFormalMultilinearSeries]
        simp_rw [eq_true hcard]
        rw [dite_true]
        simp only [piecewise_erase_univ, domDomCongr_apply, compContinuousLinearMap_apply,
          ContinuousLinearMap.proj_apply]
        congr
        ext j
        by_cases hj : j = i
        · rw [hj, Function.update_same, Function.update_same]
        · rw [Function.update_noteq hj, Function.update_noteq]
          rw [ne_eq, Equiv.apply_eq_iff_eq]
          exact hj
  · intro m hm
    have h' : Fintype.card ι ≠ 1 + m := fun h ↦ by
      apply_fun Nat.pred at h
      rw [← Nat.succ_eq_one_add, Nat.pred_succ, Nat.pred_eq_sub_one] at h
      exact hm (Eq.symm h)
    rw [FormalMultilinearSeries.changeOriginSeries, sum_apply]
    apply Finset.sum_eq_zero
    intro ⟨s, hs⟩ _
    rw [FormalMultilinearSeries.changeOriginSeriesTerm, toFormalMultilinearSeries]
    simp only [h', dite_false]
    erw [LinearMap.map_zero]
    rw [ContinuousMultilinearMap.zero_apply]

protected theorem hasFDerivAt [DecidableEq ι] (x : ∀ i, M₁ i) :
    HasFDerivAt f (f.linearDeriv x) x := by
  rw [← changeOrigin_toFormalMultilinearSeries]
  convert f.hasFiniteFPowerSeriesOnBall.hasFDerivAt (y := x) ENNReal.coe_lt_top
  rw [zero_add]

end ContinuousMultilinearMap
