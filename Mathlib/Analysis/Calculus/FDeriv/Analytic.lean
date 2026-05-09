/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.CPolynomial
public import Mathlib.Analysis.Analytic.Inverse
public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# Fréchet derivatives of analytic functions.

A function expressible as a power series at a point has a Fréchet derivative there.
Also the special case in terms of `deriv` when the domain is 1-dimensional.

As an application, we show that continuous multilinear maps are smooth. We also compute their
iterated derivatives, in `ContinuousMultilinearMap.iteratedFDeriv_eq`.

## Main definitions and results

* `AnalyticAt.differentiableAt` : an analytic function at a point is differentiable there.
* `AnalyticOnNhd.fderiv` : in a complete space, if a function is analytic on a
  neighborhood of a set `s`, so is its derivative.
* `AnalyticOnNhd.fderiv_of_isOpen` : if a function is analytic on a neighborhood of an
  open set `s`, so is its derivative.
* `AnalyticOn.fderivWithin` : if a function is analytic on a set of unique differentiability,
  so is its derivative within this set.
* `OpenPartialHomeomorph.analyticAt_symm` : if an open partial homeomorphism `f` is analytic at a
  point `f.symm a`, with invertible derivative, then its inverse is analytic at `a`.

## Comments on completeness

Some theorems need a complete space, some don't, for the following reason.

(1) If a function is analytic at a point `x`, then it is differentiable there (with derivative given
by the first term in the power series). There is no issue of convergence here.

(2) If a function has a power series on a ball `B (x, r)`, there is no guarantee that the power
series for the derivative will converge at `y ≠ x`, if the space is not complete. So, to deduce
that `f` is differentiable at `y`, one needs completeness in general.

(3) However, if a function `f` has a power series on a ball `B (x, r)`, and is a priori known to be
differentiable at some point `y ≠ x`, then the power series for the derivative of `f` will
automatically converge at `y`, towards the given derivative: this follows from the facts that this
is true in the completion (thanks to the previous point) and that the map to the completion is
an embedding.

(4) Therefore, if one assumes `AnalyticOn 𝕜 f s` where `s` is an open set, then `f` is analytic
therefore differentiable at every point of `s`, by (1), so by (3) the power series for its
derivative converges on whole balls. Therefore, the derivative of `f` is also analytic on `s`. The
same holds if `s` is merely a set with unique differentials.

(5) However, this does not work for `AnalyticOnNhd 𝕜 f s`, as we don't get for free
differentiability at points in a neighborhood of `s`. Therefore, the theorem that deduces
`AnalyticOnNhd 𝕜 (fderiv 𝕜 f) s` from `AnalyticOnNhd 𝕜 f s` requires completeness of the space.

-/

public section

open Filter Asymptotics Set

open scoped ENNReal Topology

universe u v

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section fderiv

variable {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞}
variable {f : E → F} {x : E} {s : Set E}

/-- A function which is analytic within a set is strictly differentiable there. Since we
don't have a predicate `HasStrictFDerivWithinAt`, we spell out what it would mean. -/
theorem HasFPowerSeriesWithinAt.hasStrictFDerivWithinAt (h : HasFPowerSeriesWithinAt f p s x) :
    (fun y ↦ f y.1 - f y.2 - (continuousMultilinearCurryFin1 𝕜 E F (p 1)) (y.1 - y.2))
      =o[𝓝[insert x s ×ˢ insert x s] (x, x)] fun y ↦ y.1 - y.2 := by
  refine h.isBigO_image_sub_norm_mul_norm_sub.trans_isLittleO (IsLittleO.of_norm_right ?_)
  refine isLittleO_iff_exists_eq_mul.2 ⟨fun y => ‖y - (x, x)‖, ?_, EventuallyEq.rfl⟩
  apply Tendsto.mono_left _ nhdsWithin_le_nhds
  refine (continuous_id.sub continuous_const).norm.tendsto' _ _ ?_
  rw [_root_.id, sub_self, norm_zero]

theorem HasFPowerSeriesAt.hasStrictFDerivAt (h : HasFPowerSeriesAt f p x) :
    HasStrictFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x := by
  simpa only [hasStrictFDerivAt_iff_isLittleO, Set.insert_eq_of_mem, Set.mem_univ,
      Set.univ_prod_univ, nhdsWithin_univ]
    using (h.hasFPowerSeriesWithinAt (s := Set.univ)).hasStrictFDerivWithinAt

theorem HasFPowerSeriesWithinAt.hasFDerivWithinAt (h : HasFPowerSeriesWithinAt f p s x) :
    HasFDerivWithinAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) (insert x s) x := by
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have : Tendsto (fun y ↦ (y, x)) (𝓝[insert x s] x) (𝓝[insert x s ×ˢ insert x s] (x, x)) := by
    rw [nhdsWithin_prod_eq]
    exact Tendsto.prodMk tendsto_id (tendsto_const_nhdsWithin (by simp))
  exact this (isLittleO_iff.1 h.hasStrictFDerivWithinAt hc)

theorem HasFPowerSeriesAt.hasFDerivAt (h : HasFPowerSeriesAt f p x) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x :=
  h.hasStrictFDerivAt.hasFDerivAt

theorem HasFPowerSeriesWithinAt.differentiableWithinAt (h : HasFPowerSeriesWithinAt f p s x) :
    DifferentiableWithinAt 𝕜 f (insert x s) x :=
  h.hasFDerivWithinAt.differentiableWithinAt

theorem HasFPowerSeriesAt.differentiableAt (h : HasFPowerSeriesAt f p x) : DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt

theorem AnalyticWithinAt.differentiableWithinAt (h : AnalyticWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 f (insert x s) x := by
  obtain ⟨p, hp⟩ := h
  exact hp.differentiableWithinAt

@[fun_prop]
theorem AnalyticAt.differentiableAt : AnalyticAt 𝕜 f x → DifferentiableAt 𝕜 f x
  | ⟨_, hp⟩ => hp.differentiableAt

theorem AnalyticAt.differentiableWithinAt (h : AnalyticAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x :=
  h.differentiableAt.differentiableWithinAt

theorem HasFPowerSeriesWithinAt.fderivWithin_eq
    (h : HasFPowerSeriesWithinAt f p s x) (hu : UniqueDiffWithinAt 𝕜 (insert x s) x) :
    fderivWithin 𝕜 f (insert x s) x = continuousMultilinearCurryFin1 𝕜 E F (p 1) :=
  h.hasFDerivWithinAt.fderivWithin hu

theorem HasFPowerSeriesAt.fderiv_eq (h : HasFPowerSeriesAt f p x) :
    fderiv 𝕜 f x = continuousMultilinearCurryFin1 𝕜 E F (p 1) :=
  h.hasFDerivAt.fderiv

theorem AnalyticAt.hasStrictFDerivAt (h : AnalyticAt 𝕜 f x) :
    HasStrictFDerivAt f (fderiv 𝕜 f x) x := by
  rcases h with ⟨p, hp⟩
  rw [hp.fderiv_eq]
  exact hp.hasStrictFDerivAt

lemma AnalyticAt.hasStrictDerivAt {f : 𝕜 → F} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
    HasStrictDerivAt f (deriv f x) x := by
  simpa [hasStrictDerivAt_iff_hasStrictFDerivAt, toSpanSingleton_deriv] using hf.hasStrictFDerivAt

theorem HasFPowerSeriesWithinOnBall.differentiableOn [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r) :
    DifferentiableOn 𝕜 f (insert x s ∩ Metric.eball x r) := by
  intro y hy
  have Z := (h.analyticWithinAt_of_mem hy).differentiableWithinAt
  rcases eq_or_ne y x with rfl | hy
  · exact Z.mono inter_subset_left
  · apply (Z.mono (subset_insert _ _)).mono_of_mem_nhdsWithin
    suffices s ∈ 𝓝[insert x s] y from nhdsWithin_mono _ inter_subset_left this
    rw [nhdsWithin_insert_of_ne hy]
    exact self_mem_nhdsWithin

theorem HasFPowerSeriesOnBall.differentiableOn [CompleteSpace F]
    (h : HasFPowerSeriesOnBall f p x r) : DifferentiableOn 𝕜 f (Metric.eball x r) := fun _ hy =>
  (h.analyticAt_of_mem hy).differentiableWithinAt

theorem HasFPowerSeriesAt.eventually_differentiableAt
    [CompleteSpace F] (hp : HasFPowerSeriesAt f p x) :
    ∀ᶠ z in 𝓝 x, DifferentiableAt 𝕜 f z := by
  obtain ⟨r, hp⟩ := hp
  exact hp.differentiableOn.eventually_differentiableAt (Metric.eball_mem_nhds _ hp.r_pos)

theorem AnalyticOn.differentiableOn (h : AnalyticOn 𝕜 f s) : DifferentiableOn 𝕜 f s :=
  fun y hy ↦ (h y hy).differentiableWithinAt.mono (by simp)

theorem AnalyticOnNhd.differentiableOn (h : AnalyticOnNhd 𝕜 f s) : DifferentiableOn 𝕜 f s :=
  fun y hy ↦ (h y hy).differentiableWithinAt

theorem HasFPowerSeriesWithinOnBall.hasFDerivWithinAt [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) (h'y : x + y ∈ insert x s) :
    HasFDerivWithinAt f (continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1))
      (insert x s) (x + y) := by
  rcases eq_or_ne y 0 with rfl | h''y
  · convert (h.changeOrigin hy h'y).hasFPowerSeriesWithinAt.hasFDerivWithinAt
    simp
  · have Z := (h.changeOrigin hy h'y).hasFPowerSeriesWithinAt.hasFDerivWithinAt
    apply (Z.mono (subset_insert _ _)).mono_of_mem_nhdsWithin
    rw [nhdsWithin_insert_of_ne]
    · exact self_mem_nhdsWithin
    · simpa using h''y

theorem HasFPowerSeriesOnBall.hasFDerivAt [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y) :=
  (h.changeOrigin hy).hasFPowerSeriesAt.hasFDerivAt

theorem HasFPowerSeriesWithinOnBall.fderivWithin_eq [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) (h'y : x + y ∈ insert x s) (hu : UniqueDiffOn 𝕜 (insert x s)) :
    fderivWithin 𝕜 f (insert x s) (x + y) =
      continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1) :=
  (h.hasFDerivWithinAt hy h'y).fderivWithin (hu _ h'y)

theorem HasFPowerSeriesOnBall.fderiv_eq [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    fderiv 𝕜 f (x + y) = continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1) :=
  (h.hasFDerivAt hy).fderiv

/-- If a function has a power series on a ball, then so does its derivative. -/
protected theorem HasFPowerSeriesOnBall.fderiv [CompleteSpace F]
    (h : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (fderiv 𝕜 f) p.derivSeries x r := by
  refine .congr (f := fun z ↦ continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin (z - x) 1)) ?_
    fun z hz ↦ ?_
  · refine continuousMultilinearCurryFin1 𝕜 E F
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesOnBall ?_
    simpa using ((p.hasFPowerSeriesOnBall_changeOrigin 1
      (h.r_pos.trans_le h.r_le)).mono h.r_pos h.r_le).comp_sub x
  dsimp only
  rw [← h.fderiv_eq, add_sub_cancel]
  simpa only [edist_eq_enorm_sub, Metric.mem_eball] using hz

/-- If a function has a power series within a set on a ball, then so does its derivative. -/
protected theorem HasFPowerSeriesWithinOnBall.fderivWithin [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r) (hu : UniqueDiffOn 𝕜 (insert x s)) :
    HasFPowerSeriesWithinOnBall (fderivWithin 𝕜 f (insert x s)) p.derivSeries s x r := by
  refine .congr' (f := fun z ↦ continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin (z - x) 1)) ?_
    (fun z hz ↦ ?_)
  · refine continuousMultilinearCurryFin1 𝕜 E F
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall ?_
    apply HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall
    simpa using ((p.hasFPowerSeriesOnBall_changeOrigin 1
      (h.r_pos.trans_le h.r_le)).mono h.r_pos h.r_le).comp_sub x
  · dsimp only
    rw [← h.fderivWithin_eq _ _ hu, add_sub_cancel]
    · simpa only [edist_eq_enorm_sub, Metric.mem_eball] using hz.2
    · simpa using hz.1

/-- If a function has a power series within a set on a ball, then so does its derivative. For a
version without completeness, but assuming that the function is analytic on the set `s`, see
`HasFPowerSeriesWithinOnBall.fderivWithin_of_mem_of_analyticOn`. -/
protected theorem HasFPowerSeriesWithinOnBall.fderivWithin_of_mem [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r) (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    HasFPowerSeriesWithinOnBall (fderivWithin 𝕜 f s) p.derivSeries s x r := by
  have : insert x s = s := insert_eq_of_mem hx
  rw [← this] at hu
  convert h.fderivWithin hu
  exact this.symm

/-- If a function is analytic on a set `s`, so is its Fréchet derivative. -/
@[fun_prop]
protected theorem AnalyticAt.fderiv [CompleteSpace F] (h : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (fderiv 𝕜 f) x := by
  rcases h with ⟨p, r, hp⟩
  exact hp.fderiv.analyticAt

/-- If a function is analytic on a set `s`, so is its Fréchet derivative. See also
`AnalyticOnNhd.fderiv_of_isOpen`, removing the completeness assumption but requiring the set
to be open. -/
protected theorem AnalyticOnNhd.fderiv [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (fderiv 𝕜 f) s :=
  fun y hy ↦ AnalyticAt.fderiv (h y hy)

/-- If a function is analytic on a set `s`, so are its successive Fréchet derivative. See also
`AnalyticOnNhd.iteratedFDeriv_of_isOpen`, removing the completeness assumption but requiring the set
to be open. -/
protected theorem AnalyticOnNhd.iteratedFDeriv [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f s) (n : ℕ) :
    AnalyticOnNhd 𝕜 (iteratedFDeriv 𝕜 n f) s := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm : F →L[𝕜] E [×0]→L[𝕜] F).comp_analyticOnNhd h
  | succ n IH =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    -- Porting note: for reasons that I do not understand at all, `?g` cannot be inlined.
    convert ContinuousLinearMap.comp_analyticOnNhd ?g IH.fderiv
    case g => exact ↑(continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E) F).symm
    simp

/-- If a function is analytic on a neighborhood of a set `s`, then it has a Taylor series given
by the sequence of its derivatives. Note that, if the function were just analytic on `s`, then
one would have to use instead the sequence of derivatives inside the set, as in
`AnalyticOn.hasFTaylorSeriesUpToOn`. -/
lemma AnalyticOnNhd.hasFTaylorSeriesUpToOn [CompleteSpace F]
    (n : WithTop ℕ∞) (h : AnalyticOnNhd 𝕜 f s) :
    HasFTaylorSeriesUpToOn n f (ftaylorSeries 𝕜 f) s := by
  refine ⟨fun x _hx ↦ rfl, fun m _hm x hx ↦ ?_, fun m _hm x hx ↦ ?_⟩
  · apply HasFDerivAt.hasFDerivWithinAt
    exact ((h.iteratedFDeriv m x hx).differentiableAt).hasFDerivAt
  · apply (DifferentiableAt.continuousAt (𝕜 := 𝕜) ?_).continuousWithinAt
    exact (h.iteratedFDeriv m x hx).differentiableAt

lemma AnalyticWithinAt.exists_hasFTaylorSeriesUpToOn [CompleteSpace F]
    (n : WithTop ℕ∞) (h : AnalyticWithinAt 𝕜 f s x) :
    ∃ u ∈ 𝓝[insert x s] x, ∃ (p : E → FormalMultilinearSeries 𝕜 E F),
    HasFTaylorSeriesUpToOn n f p u ∧ ∀ i, AnalyticOn 𝕜 (fun x ↦ p x i) u := by
  rcases h.exists_analyticAt with ⟨g, -, fg, hg⟩
  rcases hg.exists_mem_nhds_analyticOnNhd with ⟨v, vx, hv⟩
  refine ⟨insert x s ∩ v, inter_mem_nhdsWithin _ vx, ftaylorSeries 𝕜 g, ?_, fun i ↦ ?_⟩
  · suffices HasFTaylorSeriesUpToOn n g (ftaylorSeries 𝕜 g) (insert x s ∩ v) from
      this.congr (fun y hy ↦ fg hy.1)
    exact AnalyticOnNhd.hasFTaylorSeriesUpToOn _ (hv.mono Set.inter_subset_right)
  · exact (hv.iteratedFDeriv i).analyticOn.mono Set.inter_subset_right

/-- If a function has a power series `p` within a set of unique differentiability, inside a ball,
and is differentiable at a point, then the derivative series of `p` is summable at a point, with
sum the given differential. Note that this theorem does not require completeness of the space. -/
theorem HasFPowerSeriesWithinOnBall.hasSum_derivSeries_of_hasFDerivWithinAt
    (h : HasFPowerSeriesWithinOnBall f p s x r)
    {f' : E →L[𝕜] F}
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) (h'y : x + y ∈ insert x s)
    (hf' : HasFDerivWithinAt f f' (insert x s) (x + y))
    (hu : UniqueDiffOn 𝕜 (insert x s)) :
    HasSum (fun n ↦ p.derivSeries n (fun _ ↦ y)) f' := by
  /- In the completion of the space, the derivative series is summable, and its sum is a derivative
  of the function. Therefore, by uniqueness of derivatives, its sum is the image of `f'` under
  the canonical embedding. As this is an embedding, it means that there was also convergence in
  the original space, to `f'`. -/
  let F' := UniformSpace.Completion F
  let a : F →L[𝕜] F' := UniformSpace.Completion.toComplL
  let b : (E →L[𝕜] F) →ₗᵢ[𝕜] (E →L[𝕜] F') := UniformSpace.Completion.toComplₗᵢ.postcomp
  rw [← b.isEmbedding.hasSum_iff]
  have : HasFPowerSeriesWithinOnBall (a ∘ f) (a.compFormalMultilinearSeries p) s x r :=
    a.comp_hasFPowerSeriesWithinOnBall h
  have Z := (this.fderivWithin hu).hasSum h'y (by simpa [edist_zero_right] using hy)
  have : fderivWithin 𝕜 (a ∘ f) (insert x s) (x + y) = a ∘L f' := by
    apply HasFDerivWithinAt.fderivWithin _ (hu _ h'y)
    exact a.hasFDerivAt.comp_hasFDerivWithinAt (x + y) hf'
  rw [this] at Z
  convert Z with n
  ext v
  simp only [FormalMultilinearSeries.derivSeries, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.compFormalMultilinearSeries_apply,
    FormalMultilinearSeries.changeOriginSeries,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_coe, Function.comp_apply, ContinuousMultilinearMap.sum_apply, map_sum]
  rfl

/-- If a function has a power series within a set on a ball, then so does its derivative. Version
assuming that the function is analytic on `s`. For a version without this assumption but requiring
that `F` is complete, see `HasFPowerSeriesWithinOnBall.fderivWithin_of_mem`. -/
protected theorem HasFPowerSeriesWithinOnBall.fderivWithin_of_mem_of_analyticOn
    (hr : HasFPowerSeriesWithinOnBall f p s x r)
    (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    HasFPowerSeriesWithinOnBall (fderivWithin 𝕜 f s) p.derivSeries s x r := by
  refine ⟨hr.r_le.trans p.radius_le_radius_derivSeries, hr.r_pos, fun {y} hy h'y ↦ ?_⟩
  apply hr.hasSum_derivSeries_of_hasFDerivWithinAt (by simpa [edist_zero_right] using h'y) hy
  · rw [insert_eq_of_mem hx] at hy ⊢
    apply DifferentiableWithinAt.hasFDerivWithinAt
    exact h.differentiableOn _ hy
  · rwa [insert_eq_of_mem hx]

/-- If a function is analytic within a set with unique differentials, then so is its derivative.
Note that this theorem does not require completeness of the space. -/
protected theorem AnalyticOn.fderivWithin (h : AnalyticOn 𝕜 f s) (hu : UniqueDiffOn 𝕜 s) :
    AnalyticOn 𝕜 (fderivWithin 𝕜 f s) s := by
  intro x hx
  rcases h x hx with ⟨p, r, hr⟩
  refine ⟨p.derivSeries, r, hr.fderivWithin_of_mem_of_analyticOn h hu hx⟩

/-- If a function is analytic on a set `s`, so are its successive Fréchet derivative within this
set. Note that this theorem does not require completeness of the space. -/
protected theorem AnalyticOn.iteratedFDerivWithin (h : AnalyticOn 𝕜 f s)
    (hu : UniqueDiffOn 𝕜 s) (n : ℕ) :
    AnalyticOn 𝕜 (iteratedFDerivWithin 𝕜 n f s) s := by
  induction n with
  | zero =>
    rw [iteratedFDerivWithin_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm : F →L[𝕜] E [×0]→L[𝕜] F)
      |>.comp_analyticOn h
  | succ n IH =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]
    apply AnalyticOnNhd.comp_analyticOn _ (IH.fderivWithin hu) (mapsTo_univ _ _)
    apply LinearIsometryEquiv.analyticOnNhd

protected lemma AnalyticOn.hasFTaylorSeriesUpToOn {n : WithTop ℕ∞}
    (h : AnalyticOn 𝕜 f s) (hu : UniqueDiffOn 𝕜 s) :
    HasFTaylorSeriesUpToOn n f (ftaylorSeriesWithin 𝕜 f s) s := by
  refine ⟨fun x _hx ↦ rfl, fun m _hm x hx ↦ ?_, fun m _hm x hx ↦ ?_⟩
  · have := (h.iteratedFDerivWithin hu m x hx).differentiableWithinAt.hasFDerivWithinAt
    rwa [insert_eq_of_mem hx] at this
  · exact (h.iteratedFDerivWithin hu m x hx).continuousWithinAt

lemma AnalyticOn.exists_hasFTaylorSeriesUpToOn
    (h : AnalyticOn 𝕜 f s) (hu : UniqueDiffOn 𝕜 s) :
    ∃ p : E → FormalMultilinearSeries 𝕜 E F,
      HasFTaylorSeriesUpToOn ⊤ f p s ∧ ∀ i, AnalyticOn 𝕜 (fun x ↦ p x i) s :=
  ⟨ftaylorSeriesWithin 𝕜 f s, h.hasFTaylorSeriesUpToOn hu, h.iteratedFDerivWithin hu⟩

theorem AnalyticOnNhd.fderiv_of_isOpen (h : AnalyticOnNhd 𝕜 f s) (hs : IsOpen s) :
    AnalyticOnNhd 𝕜 (fderiv 𝕜 f) s := by
  rw [← hs.analyticOn_iff_analyticOnNhd] at h ⊢
  exact (h.fderivWithin hs.uniqueDiffOn).congr (fun x hx ↦ (fderivWithin_of_isOpen hs hx).symm)

theorem AnalyticOnNhd.iteratedFDeriv_of_isOpen (h : AnalyticOnNhd 𝕜 f s) (hs : IsOpen s) (n : ℕ) :
    AnalyticOnNhd 𝕜 (iteratedFDeriv 𝕜 n f) s := by
  rw [← hs.analyticOn_iff_analyticOnNhd] at h ⊢
  exact (h.iteratedFDerivWithin hs.uniqueDiffOn n).congr
    (fun x hx ↦ (iteratedFDerivWithin_of_isOpen n hs hx).symm)

/-- If an open partial homeomorphism `f` is analytic at a point `a`, with invertible derivative,
then its inverse is analytic at `f a`. -/
theorem OpenPartialHomeomorph.analyticAt_symm' (f : OpenPartialHomeomorph E F) {a : E}
    {i : E ≃L[𝕜] F} (h0 : a ∈ f.source) (h : AnalyticAt 𝕜 f a) (h' : fderiv 𝕜 f a = i) :
    AnalyticAt 𝕜 f.symm (f a) := by
  rcases h with ⟨p, hp⟩
  have : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i := by simp [← h', hp.fderiv_eq]
  exact (f.hasFPowerSeriesAt_symm h0 hp this).analyticAt

/-- If an open partial homeomorphism `f` is analytic at a point `f.symm a`, with invertible
derivative, then its inverse is analytic at `a`. -/
theorem OpenPartialHomeomorph.analyticAt_symm (f : OpenPartialHomeomorph E F) {a : F}
    {i : E ≃L[𝕜] F} (h0 : a ∈ f.target) (h : AnalyticAt 𝕜 f (f.symm a))
    (h' : fderiv 𝕜 f (f.symm a) = i) :
    AnalyticAt 𝕜 f.symm a := by
  have : a = f (f.symm a) := by simp [h0]
  rw [this]
  exact f.analyticAt_symm' (by simp [h0]) h h'

end fderiv

section deriv

variable {p : FormalMultilinearSeries 𝕜 𝕜 F} {r : ℝ≥0∞}
variable {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}

protected theorem HasFPowerSeriesAt.hasStrictDerivAt (h : HasFPowerSeriesAt f p x) :
    HasStrictDerivAt f (p 1 fun _ => 1) x :=
  h.hasStrictFDerivAt.hasStrictDerivAt

protected theorem HasFPowerSeriesAt.hasDerivAt (h : HasFPowerSeriesAt f p x) :
    HasDerivAt f (p 1 fun _ => 1) x :=
  h.hasStrictDerivAt.hasDerivAt

protected theorem HasFPowerSeriesAt.deriv (h : HasFPowerSeriesAt f p x) :
    deriv f x = p 1 fun _ => 1 :=
  h.hasDerivAt.deriv

/-- If a function is analytic on a set `s` in a complete space, so is its derivative. -/
protected theorem AnalyticOnNhd.deriv [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (deriv f) s :=
  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_analyticOnNhd h.fderiv

/-- If a function is analytic on an open set `s`, so is its derivative. -/
theorem AnalyticOnNhd.deriv_of_isOpen (h : AnalyticOnNhd 𝕜 f s) (hs : IsOpen s) :
    AnalyticOnNhd 𝕜 (deriv f) s :=
  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_analyticOnNhd (h.fderiv_of_isOpen hs)

/-- If a function is analytic on a set `s`, so are its successive derivatives. -/
theorem AnalyticOnNhd.iterated_deriv [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f s) (n : ℕ) :
    AnalyticOnNhd 𝕜 (deriv^[n] f) s := by
  induction n with
  | zero => exact h
  | succ n IH => simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv

@[fun_prop] protected theorem AnalyticAt.deriv [CompleteSpace F] (h : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (deriv f) x := by
  obtain ⟨r, hr, h⟩ := h.exists_ball_analyticOnNhd
  exact h.deriv x (by simp [hr])

@[fun_prop] theorem AnalyticAt.iterated_deriv [CompleteSpace F] (h : AnalyticAt 𝕜 f x) (n : ℕ) :
    AnalyticAt 𝕜 (deriv^[n] f) x := by
  induction n with
  | zero => exact h
  | succ n IH => simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv

end deriv
section fderiv

variable {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞} {n : ℕ}
variable {f : E → F} {x : E} {s : Set E}

/-! The case of continuously polynomial functions. We get the same differentiability
results as for analytic functions, but without the assumptions that `F` is complete. -/

theorem HasFiniteFPowerSeriesOnBall.differentiableOn
    (h : HasFiniteFPowerSeriesOnBall f p x n r) : DifferentiableOn 𝕜 f (Metric.eball x r) :=
  fun _ hy ↦ (h.cpolynomialAt_of_mem hy).analyticAt.differentiableWithinAt

theorem HasFiniteFPowerSeriesOnBall.hasStrictFDerivAt (h : HasFiniteFPowerSeriesOnBall f p x n r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    HasStrictFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y) :=
  (h.changeOrigin hy).toHasFPowerSeriesOnBall.hasFPowerSeriesAt.hasStrictFDerivAt

theorem HasFiniteFPowerSeriesOnBall.hasFDerivAt (h : HasFiniteFPowerSeriesOnBall f p x n r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y) :=
  (h.hasStrictFDerivAt hy).hasFDerivAt

theorem HasFiniteFPowerSeriesOnBall.fderiv_eq (h : HasFiniteFPowerSeriesOnBall f p x n r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    fderiv 𝕜 f (x + y) = continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1) :=
  (h.hasFDerivAt hy).fderiv

/-- If a function has a finite power series on a ball, then so does its derivative. -/
protected theorem HasFiniteFPowerSeriesOnBall.fderiv
    (h : HasFiniteFPowerSeriesOnBall f p x (n + 1) r) :
    HasFiniteFPowerSeriesOnBall (fderiv 𝕜 f) p.derivSeries x n r := by
  refine .congr (f := fun z ↦ continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin (z - x) 1)) ?_
    fun z hz ↦ ?_
  · refine continuousMultilinearCurryFin1 𝕜 E F
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall ?_
    simpa using
      ((p.hasFiniteFPowerSeriesOnBall_changeOrigin 1 h.finite).mono h.r_pos le_top).comp_sub x
  dsimp only
  rw [← h.fderiv_eq, add_sub_cancel]
  simpa only [edist_eq_enorm_sub, Metric.mem_eball] using hz

/-- If a function has a finite power series on a ball, then so does its derivative.
This is a variant of `HasFiniteFPowerSeriesOnBall.fderiv` where the degree of `f` is `< n`
and not `< n + 1`. -/
theorem HasFiniteFPowerSeriesOnBall.fderiv' (h : HasFiniteFPowerSeriesOnBall f p x n r) :
    HasFiniteFPowerSeriesOnBall (fderiv 𝕜 f) p.derivSeries x (n - 1) r := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [zero_tsub]
    refine HasFiniteFPowerSeriesOnBall.bound_zero_of_eq_zero (fun y hy ↦ ?_) h.r_pos fun n ↦ ?_
    · rw [Filter.EventuallyEq.fderiv_eq (f := fun _ ↦ 0)]
      · simp
      · exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨Metric.eball x r,
          Metric.isOpen_eball.mem_nhds hy, fun z hz ↦ by rw [h.eq_zero_of_bound_zero z hz]⟩
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
  exact hp.fderiv'.cpolynomialAt

/-- If a function is polynomial on a set `s`, so are its successive Fréchet derivative. -/
theorem CPolynomialOn.iteratedFDeriv (h : CPolynomialOn 𝕜 f s) (n : ℕ) :
    CPolynomialOn 𝕜 (iteratedFDeriv 𝕜 n f) s := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm : F →L[𝕜] E [×0]→L[𝕜] F).comp_cpolynomialOn h
  | succ n IH =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    convert ContinuousLinearMap.comp_cpolynomialOn ?g IH.fderiv
    case g => exact ↑(continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E) F).symm
    simp

end fderiv

section deriv

variable {p : FormalMultilinearSeries 𝕜 𝕜 F} {r : ℝ≥0∞}
variable {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}

/-- If a function is polynomial on a set `s`, so is its derivative. -/
protected theorem CPolynomialOn.deriv (h : CPolynomialOn 𝕜 f s) : CPolynomialOn 𝕜 (deriv f) s :=
  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_cpolynomialOn h.fderiv

/-- If a function is polynomial on a set `s`, so are its successive derivatives. -/
theorem CPolynomialOn.iterated_deriv (h : CPolynomialOn 𝕜 f s) (n : ℕ) :
    CPolynomialOn 𝕜 (deriv^[n] f) s := by
  induction n with
  | zero => exact h
  | succ n IH => simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv

end deriv

namespace ContinuousMultilinearMap

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [Fintype ι] (f : ContinuousMultilinearMap 𝕜 E F)

open FormalMultilinearSeries

theorem changeOriginSeries_support {k l : ℕ} (h : k + l ≠ Fintype.card ι) :
    f.toFormalMultilinearSeries.changeOriginSeries k l = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ by
    simp_rw [FormalMultilinearSeries.changeOriginSeriesTerm,
      toFormalMultilinearSeries, dif_neg h.symm, LinearIsometryEquiv.map_zero]

variable {n : WithTop ℕ∞} (x : ∀ i, E i)

open Finset in
theorem changeOrigin_toFormalMultilinearSeries [DecidableEq ι] :
    continuousMultilinearCurryFin1 𝕜 (∀ i, E i) F (f.toFormalMultilinearSeries.changeOrigin x 1) =
    f.linearDeriv x := by
  ext y
  rw [continuousMultilinearCurryFin1_apply, linearDeriv_apply,
      changeOrigin, FormalMultilinearSeries.sum]
  cases isEmpty_or_nonempty ι
  · have (l : _) : 1 + l ≠ Fintype.card ι := by
      rw [add_comm, Fintype.card_eq_zero]; exact Nat.succ_ne_zero _
    simp_rw [Fintype.sum_empty, changeOriginSeries_support _ (this _), zero_apply _, tsum_zero]; rfl
  rw [tsum_eq_single (Fintype.card ι - 1), changeOriginSeries]; swap
  · intro m hm
    rw [Ne, eq_tsub_iff_add_eq_of_le (by exact Fintype.card_pos), add_comm] at hm
    rw [f.changeOriginSeries_support hm, zero_apply]
  rw [sum_apply, ContinuousMultilinearMap.sum_apply, Fin.snoc_zero]
  simp_rw [changeOriginSeriesTerm_apply]
  refine (Fintype.sum_bijective (?_ ∘ Fintype.equivFinOfCardEq (Nat.add_sub_of_le
    Fintype.card_pos).symm) (.comp ?_ <| Equiv.bijective _) _ _ fun i ↦ ?_).symm
  · exact (⟨{·}ᶜ, by
      rw [card_compl, Fintype.card_fin, Finset.card_singleton, Nat.add_sub_cancel_left]⟩)
  · use fun _ _ ↦ (singleton_injective <| compl_injective <| Subtype.ext_iff.mp ·)
    intro ⟨s, hs⟩
    have h : #sᶜ = 1 := by rw [card_compl, hs, Fintype.card_fin, Nat.add_sub_cancel]
    obtain ⟨a, ha⟩ := card_eq_one.mp h
    exact ⟨a, Subtype.ext (compl_eq_comm.mp ha)⟩
  rw [Function.comp_apply, Subtype.coe_mk, compl_singleton, piecewise_erase_univ,
    toFormalMultilinearSeries, dif_pos (Nat.add_sub_of_le Fintype.card_pos).symm]
  simp_rw [domDomCongr_apply, compContinuousLinearMap_apply, ContinuousLinearMap.proj_apply,
    Function.update_apply, (Equiv.injective _).eq_iff, ite_apply]
  congr
  grind

protected theorem hasStrictFDerivAt [DecidableEq ι] : HasStrictFDerivAt f (f.linearDeriv x) x := by
  rw [← changeOrigin_toFormalMultilinearSeries]
  convert f.hasFiniteFPowerSeriesOnBall.hasStrictFDerivAt (y := x) ENNReal.coe_lt_top
  rw [zero_add]

protected theorem hasFDerivAt [DecidableEq ι] : HasFDerivAt f (f.linearDeriv x) x :=
  (f.hasStrictFDerivAt _).hasFDerivAt

protected theorem hasStrictFDerivAt_uncurry [DecidableEq ι]
    (fa : ContinuousMultilinearMap 𝕜 E F × ∀ i, E i) :
    HasStrictFDerivAt (fun fx : ContinuousMultilinearMap 𝕜 E F × ∀ i, E i ↦ fx.1 fx.2)
      (apply 𝕜 E F fa.2 ∘L .fst _ _ _ + fa.1.linearDeriv fa.2 ∘L .snd _ _ _) fa := by
  let f := ContinuousLinearMap.id 𝕜 (ContinuousMultilinearMap 𝕜 E F)
    |>.continuousMultilinearMapOption
  have Hf := (f.hasStrictFDerivAt (fun _ ↦ fa)).comp (f := fun fx _ ↦ fx) fa
    (hasStrictFDerivAt_pi.2 fun _ ↦ hasStrictFDerivAt_id _)
  convert Hf using 1
  ext g
  · suffices ∑ i, fa.1 (Function.update fa.2 i 0) =
        ∑ i, fa.1 fun j ↦ (Function.update (fun _ ↦ fa) (some i) (g, 0) (some j)).2 j by
      simpa [f, ContinuousLinearMap.continuousMultilinearMapOption]
    congr with i
    congr with j
    rcases eq_or_ne j i with rfl | hij <;> simp [*]
  · suffices ∑ i, fa.1 (Function.update fa.2 i (g i)) =
        ∑ x, fa.1 fun i ↦ (Function.update (fun x ↦ fa) (some x) (0, g) (some i)).2 i by
      simpa [f, ContinuousLinearMap.continuousMultilinearMapOption]
    congr with i
    congr with j
    rcases eq_or_ne j i with rfl | hij <;> simp [*]

theorem _root_.HasStrictFDerivAt.continuousMultilinearMap_apply {G : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [DecidableEq ι] {x : G}
    {f : G → ContinuousMultilinearMap 𝕜 E F} {g : ∀ i, G → E i}
    {f' : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F} {g' : ∀ i, G →L[𝕜] E i}
    (hf : HasStrictFDerivAt f f' x) (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) x) :
    HasStrictFDerivAt (fun x ↦ f x (g · x))
      (ContinuousMultilinearMap.apply 𝕜 E F (g · x) ∘L f' +
        ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i) x := by
  convert ContinuousMultilinearMap.hasStrictFDerivAt_uncurry (f x, (g · x))
    |>.comp x (hf.prodMk (hasStrictFDerivAt_pi.2 hg))
  ext
  simp

theorem _root_.HasFDerivWithinAt.continuousMultilinearMap_apply {G : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [DecidableEq ι] {s : Set G} {x : G}
    {f : G → ContinuousMultilinearMap 𝕜 E F} {g : ∀ i, G → E i}
    {f' : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F} {g' : ∀ i, G →L[𝕜] E i}
    (hf : HasFDerivWithinAt f f' s x) (hg : ∀ i, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt (fun x ↦ f x (g · x))
      (ContinuousMultilinearMap.apply 𝕜 E F (g · x) ∘L f' +
        ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i) s x := by
  convert ContinuousMultilinearMap.hasStrictFDerivAt_uncurry (f x, (g · x))
    |>.hasFDerivAt.comp_hasFDerivWithinAt x (hf.prodMk (hasFDerivWithinAt_pi.2 hg))
  ext
  simp

theorem _root_.HasFDerivAt.continuousMultilinearMap_apply {G : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [DecidableEq ι] {x : G}
    {f : G → ContinuousMultilinearMap 𝕜 E F} {g : ∀ i, G → E i}
    {f' : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F} {g' : ∀ i, G →L[𝕜] E i}
    (hf : HasFDerivAt f f' x) (hg : ∀ i, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt (fun x ↦ f x (g · x))
      (ContinuousMultilinearMap.apply 𝕜 E F (g · x) ∘L f' +
        ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i) x := by
  simp only [← hasFDerivWithinAt_univ] at *
  exact hf.continuousMultilinearMap_apply hg

/-- Given `f` a multilinear map, then the derivative of `x ↦ f (g₁ x, ..., gₙ x)` at `x` applied
to a vector `v` is given by `∑ i, f (g₁ x, ..., g'ᵢ v, ..., gₙ x)`. Version inside a set. -/
theorem _root_.HasFDerivWithinAt.multilinear_comp
    [DecidableEq ι] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {g : ∀ i, G → E i} {g' : ∀ i, G →L[𝕜] E i} {s : Set G} {x : G}
    (hg : ∀ i, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt (fun x ↦ f (fun i ↦ g i x))
      ((∑ i : ι, (f.toContinuousLinearMap (fun j ↦ g j x) i) ∘L (g' i))) s x := by
  simpa using (hasFDerivWithinAt_const f x s).continuousMultilinearMap_apply hg

/-- Given `f` a multilinear map, then the derivative of `x ↦ f (g₁ x, ..., gₙ x)` at `x` applied
to a vector `v` is given by `∑ i, f (g₁ x, ..., g'ᵢ v, ..., gₙ x)`. -/
theorem _root_.HasFDerivAt.multilinear_comp
    [DecidableEq ι] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {g : ∀ i, G → E i} {g' : ∀ i, G →L[𝕜] E i} {x : G}
    (hg : ∀ i, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt (fun x ↦ f (fun i ↦ g i x))
      ((∑ i : ι, (f.toContinuousLinearMap (fun j ↦ g j x) i) ∘L (g' i))) x := by
  simpa using (hasFDerivAt_const f x).continuousMultilinearMap_apply hg

/-- Technical lemma used in the proof of `hasFTaylorSeriesUpTo_iteratedFDeriv`, to compare sums
over embedding of `Fin k` and `Fin (k + 1)`. -/
private lemma _root_.Equiv.succ_embeddingFinSucc_fst_symm_apply {ι : Type*} [DecidableEq ι]
    {n : ℕ} (e : Fin (n + 1) ↪ ι) {k : ι}
    (h'k : k ∈ Set.range (Equiv.embeddingFinSucc n ι e).1) (hk : k ∈ Set.range e) :
    Fin.succ ((Equiv.embeddingFinSucc n ι e).1.toEquivRange.symm ⟨k, h'k⟩)
      = e.toEquivRange.symm ⟨k, hk⟩ := by
  rcases hk with ⟨j, rfl⟩
  have hj : j ≠ 0 := by
    rintro rfl
    simp at h'k
  simp only [Function.Embedding.toEquivRange_symm_apply_self]
  have : e j = (Equiv.embeddingFinSucc n ι e).1 (Fin.pred j hj) := by simp
  simp_rw [this]
  simp [-Equiv.embeddingFinSucc_fst]

/-- A continuous multilinear function `f` admits a Taylor series, whose successive terms are given
by `f.iteratedFDeriv n`. This is the point of the definition of `f.iteratedFDeriv`. -/
theorem hasFTaylorSeriesUpTo_iteratedFDeriv :
    HasFTaylorSeriesUpTo ⊤ f (fun v n ↦ f.iteratedFDeriv n v) := by
  classical
  constructor
  · simp [ContinuousMultilinearMap.iteratedFDeriv]
  · rintro n - x
    suffices H : curryLeft (f.iteratedFDeriv (Nat.succ n) x) = (∑ e : Fin n ↪ ι,
          ((iteratedFDerivComponent f e.toEquivRange).linearDeriv
            (Pi.compRightL 𝕜 _ Subtype.val x)) ∘L (Pi.compRightL 𝕜 _ Subtype.val)) by
      have A : HasFDerivAt (f.iteratedFDeriv n) (∑ e : Fin n ↪ ι,
          ((iteratedFDerivComponent f e.toEquivRange).linearDeriv (Pi.compRightL 𝕜 _ Subtype.val x))
            ∘L (Pi.compRightL 𝕜 _ Subtype.val)) x := by
        apply HasFDerivAt.fun_sum (fun s _hs ↦ ?_)
        exact (ContinuousMultilinearMap.hasFDerivAt _ _).comp x (ContinuousLinearMap.hasFDerivAt _)
      rwa [← H] at A
    ext v m
    simp only [ContinuousMultilinearMap.iteratedFDeriv, curryLeft_apply, sum_apply,
      iteratedFDerivComponent_apply, Finset.univ_sigma_univ,
      Pi.compRightL_apply, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_comp',
      Finset.sum_apply, Function.comp_apply, linearDeriv_apply, Finset.sum_sigma']
    rw [← (Equiv.embeddingFinSucc n ι).sum_comp]
    congr with e
    congr with k
    by_cases hke : k ∈ Set.range e
    · simp only [hke, ↓reduceDIte]
      split_ifs with hkf
      · simp only [← Equiv.succ_embeddingFinSucc_fst_symm_apply e hkf hke, Fin.cons_succ]
      · obtain rfl : k = e 0 := by
          rcases hke with ⟨j, rfl⟩
          simpa using hkf
        simp only [Function.Embedding.toEquivRange_symm_apply_self, Fin.cons_zero, Function.update,
          Pi.compRightL_apply]
        split_ifs with h
        · congr!
        · exfalso
          apply h
          simp_rw [← Equiv.embeddingFinSucc_snd e]
    · have hkf : k ∉ Set.range (Equiv.embeddingFinSucc n ι e).1 := by
        contrapose hke
        rw [Equiv.embeddingFinSucc_fst] at hke
        exact Set.range_comp_subset_range _ _ hke
      simp only [hke, hkf, ↓reduceDIte, Pi.compRightL,
        ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
      rw [Function.update_of_ne]
      contrapose hke
      rw [show k = _ from Subtype.ext_iff.1 hke, Equiv.embeddingFinSucc_snd e]
      exact Set.mem_range_self _
  · rintro n -
    apply continuous_finset_sum _ (fun e _ ↦ ?_)
    exact (ContinuousMultilinearMap.coe_continuous _).comp (ContinuousLinearMap.continuous _)

theorem iteratedFDeriv_eq (n : ℕ) :
    iteratedFDeriv 𝕜 n f = f.iteratedFDeriv n :=
  funext fun x ↦ (f.hasFTaylorSeriesUpTo_iteratedFDeriv.eq_iteratedFDeriv (m := n) le_top x).symm

theorem norm_iteratedFDeriv_le (n : ℕ) (x : (i : ι) → E i) :
    ‖iteratedFDeriv 𝕜 n f x‖
      ≤ Nat.descFactorial (Fintype.card ι) n * ‖f‖ * ‖x‖ ^ (Fintype.card ι - n) := by
  rw [f.iteratedFDeriv_eq]
  exact f.norm_iteratedFDeriv_le' n x

end ContinuousMultilinearMap

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F)

open Fintype ContinuousLinearMap in
theorem derivSeries_apply_diag (n : ℕ) (x : E) :
    derivSeries p n (fun _ ↦ x) x = (n + 1) • p (n + 1) fun _ ↦ x := by
  simp only [derivSeries, compFormalMultilinearSeries_apply, changeOriginSeries,
    compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe,
    Function.comp_apply, ContinuousMultilinearMap.sum_apply, map_sum, coe_sum', Finset.sum_apply,
    continuousMultilinearCurryFin1_apply, Matrix.zero_empty]
  convert Finset.sum_const _
  · rw [Fin.snoc_zero, changeOriginSeriesTerm_apply, Finset.piecewise_same, add_comm]
  · rw [← card, card_subtype, ← Finset.powerset_univ, ← Finset.powersetCard_eq_filter,
      Finset.card_powersetCard, ← card, card_fin, eq_comm, add_comm, Nat.choose_succ_self_right]

@[simp]
lemma derivSeries_coeff_one (p : FormalMultilinearSeries 𝕜 𝕜 F) (n : ℕ) :
    p.derivSeries.coeff n 1 = (n + 1) • p.coeff (n + 1) :=
  p.derivSeries_apply_diag _ _

end FormalMultilinearSeries

namespace HasFPowerSeriesOnBall

open FormalMultilinearSeries ENNReal Nat

variable {p : FormalMultilinearSeries 𝕜 E F} {f : E → F} {x : E} {r : ℝ≥0∞}
  (h : HasFPowerSeriesOnBall f p x r) (y : E)

include h in
theorem iteratedFDeriv_zero_apply_diag : iteratedFDeriv 𝕜 0 f x = p 0 := by
  ext
  simpa using (coeff_zero h _).symm

open ContinuousLinearMap

private theorem factorial_smul' {n : ℕ} : ∀ {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] {p : FormalMultilinearSeries 𝕜 E F}
    {f : E → F}, HasFPowerSeriesOnBall f p x r →
    n ! • p n (fun _ ↦ y) = iteratedFDeriv 𝕜 n f x (fun _ ↦ y) := by
  induction n with | zero => _ | succ n ih => _ <;> intro F _ _ _ p f h
  · rw [factorial_zero, one_smul, h.iteratedFDeriv_zero_apply_diag]
  · rw [factorial_succ, mul_comm, mul_smul, ← derivSeries_apply_diag,
      ← ContinuousLinearMap.smul_apply, ih h.fderiv, iteratedFDeriv_succ_apply_right]
    rfl

variable [CompleteSpace F]
include h

/-- The iterated derivative of an analytic function, on vectors `(y, ..., y)`, is given by `n!`
times the `n`-th term in the power series. For a more general result giving the full iterated
derivative as a sum over the permutations of `Fin n`, see
`HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum`. -/
theorem factorial_smul (n : ℕ) :
    n ! • p n (fun _ ↦ y) = iteratedFDeriv 𝕜 n f x (fun _ ↦ y) := by
  cases n
  · rw [factorial_zero, one_smul, h.iteratedFDeriv_zero_apply_diag]
  · rw [factorial_succ, mul_comm, mul_smul, ← derivSeries_apply_diag,
      ← ContinuousLinearMap.smul_apply, factorial_smul' _ h.fderiv, iteratedFDeriv_succ_apply_right]
    rfl

theorem hasSum_iteratedFDeriv [CharZero 𝕜] {y : E} (hy : y ∈ Metric.eball 0 r) :
    HasSum (fun n ↦ (n ! : 𝕜)⁻¹ • iteratedFDeriv 𝕜 n f x fun _ ↦ y) (f (x + y)) := by
  convert h.hasSum hy with n
  rw [← h.factorial_smul y n, smul_comm, ← smul_assoc, nsmul_eq_mul,
    mul_inv_cancel₀ <| cast_ne_zero.mpr n.factorial_ne_zero, one_smul]

end HasFPowerSeriesOnBall

/-!
### Derivative of a linear map into multilinear maps
-/

namespace ContinuousLinearMap

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
  [Fintype ι] {H : Type*} [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]

theorem hasFDerivAt_uncurry_of_multilinear [DecidableEq ι]
    (f : E →L[𝕜] ContinuousMultilinearMap 𝕜 G F) (v : E × Π i, G i) :
    HasFDerivAt (fun (p : E × Π i, G i) ↦ f p.1 p.2)
      ((f.flipMultilinear v.2) ∘L (.fst _ _ _) +
        ∑ i : ι, ((f v.1).toContinuousLinearMap v.2 i) ∘L (.proj _) ∘L (.snd _ _ _)) v :=
  (f ∘L .fst 𝕜 E (∀ i, G i)).hasFDerivAt.continuousMultilinearMap_apply
    (hasFDerivAt_pi'.mp (hasFDerivAt_snd (E := E) (F := ∀ i, G i)))

/-- Given `f` a linear map into multilinear maps, then the derivative
of `x ↦ f (a x) (b₁ x, ..., bₙ x)` at `x` applied to a vector `v` is given by
`f (a' v) (b₁ x, ...., bₙ x) + ∑ i, f a (b₁ x, ..., b'ᵢ v, ..., bₙ x)`. Version inside a set. -/
theorem _root_.HasFDerivWithinAt.linear_multilinear_comp
    [DecidableEq ι] {a : H → E} {a' : H →L[𝕜] E}
    {b : ∀ i, H → G i} {b' : ∀ i, H →L[𝕜] G i} {s : Set H} {x : H}
    (ha : HasFDerivWithinAt a a' s x) (hb : ∀ i, HasFDerivWithinAt (b i) (b' i) s x)
    (f : E →L[𝕜] ContinuousMultilinearMap 𝕜 G F) :
    HasFDerivWithinAt (fun y ↦ f (a y) (fun i ↦ b i y))
      ((f.flipMultilinear (fun i ↦ b i x)) ∘L a' +
        ∑ i, ((f (a x)).toContinuousLinearMap (fun j ↦ b j x) i) ∘L (b' i)) s x :=
  (f.hasFDerivAt.comp_hasFDerivWithinAt x ha).continuousMultilinearMap_apply hb

/-- Given `f` a linear map into multilinear maps, then the derivative
of `x ↦ f (a x) (b₁ x, ..., bₙ x)` at `x` applied to a vector `v` is given by
`f (a' v) (b₁ x, ...., bₙ x) + ∑ i, f a (b₁ x, ..., b'ᵢ v, ..., bₙ x)`. -/
theorem _root_.HasFDerivAt.linear_multilinear_comp [DecidableEq ι] {a : H → E} {a' : H →L[𝕜] E}
    {b : ∀ i, H → G i} {b' : ∀ i, H →L[𝕜] G i} {x : H}
    (ha : HasFDerivAt a a' x) (hb : ∀ i, HasFDerivAt (b i) (b' i) x)
    (f : E →L[𝕜] ContinuousMultilinearMap 𝕜 G F) :
    HasFDerivAt (fun y ↦ f (a y) (fun i ↦ b i y))
      ((f.flipMultilinear (fun i ↦ b i x)) ∘L a' +
        ∑ i, ((f (a x)).toContinuousLinearMap (fun j ↦ b j x) i) ∘L (b' i)) x :=
  (f.hasFDerivAt.comp x ha).continuousMultilinearMap_apply hb

end ContinuousLinearMap
