/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Higher differentiability over `ℝ` or `ℂ`
-/

noncomputable section

open Set Fin Filter Function

open scoped NNReal Topology

section Real

/-!
### Results over `ℝ` or `ℂ`
  The results in this section rely on the Mean Value Theorem, and therefore hold only over `ℝ` (and
  its extension fields such as `ℂ`).
-/

variable {n : ℕ∞} {𝕂 : Type*} [RCLike 𝕂]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E' F' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕂 E']
    [NormedAddCommGroup F'] [NormedSpace 𝕂 F']

/-- If a function has a Taylor series at order at least 1, then at points in the interior of the
    domain of definition, the term of order 1 of this series is a strict derivative of `f`. -/
theorem HasFTaylorSeriesUpToOn.hasStrictFDerivAt {s : Set E'} {f : E' → F'} {x : E'}
    {p : E' → FormalMultilinearSeries 𝕂 E' F'} (hf : HasFTaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
    (hs : s ∈ 𝓝 x) : HasStrictFDerivAt f ((continuousMultilinearCurryFin1 𝕂 E' F') (p x 1)) x :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hf.eventually_hasFDerivAt hn hs) <|
    (continuousMultilinearCurryFin1 𝕂 E' F').continuousAt.comp <| (hf.cont 1 hn).continuousAt hs

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
theorem ContDiffAt.hasStrictFDerivAt' {f : E' → F'} {f' : E' →L[𝕂] F'} {x : E'}
    (hf : ContDiffAt 𝕂 n f x) (hf' : HasFDerivAt f f' x) (hn : 1 ≤ n) :
    HasStrictFDerivAt f f' x := by
  rcases hf 1 hn with ⟨u, H, p, hp⟩
  simp only [nhdsWithin_univ, mem_univ, insert_eq_of_mem] at H
  have := hp.hasStrictFDerivAt le_rfl H
  rwa [hf'.unique this.hasFDerivAt]

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
theorem ContDiffAt.hasStrictDerivAt' {f : 𝕂 → F'} {f' : F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x)
    (hf' : HasDerivAt f f' x) (hn : 1 ≤ n) : HasStrictDerivAt f f' x :=
  hf.hasStrictFDerivAt' hf' hn

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
theorem ContDiffAt.hasStrictFDerivAt {f : E' → F'} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) :
    HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.hasStrictFDerivAt' (hf.differentiableAt hn).hasFDerivAt hn

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
theorem ContDiffAt.hasStrictDerivAt {f : 𝕂 → F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) :
    HasStrictDerivAt f (deriv f x) x :=
  (hf.hasStrictFDerivAt hn).hasStrictDerivAt

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
theorem ContDiff.hasStrictFDerivAt {f : E' → F'} {x : E'} (hf : ContDiff 𝕂 n f) (hn : 1 ≤ n) :
    HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.contDiffAt.hasStrictFDerivAt hn

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
theorem ContDiff.hasStrictDerivAt {f : 𝕂 → F'} {x : 𝕂} (hf : ContDiff 𝕂 n f) (hn : 1 ≤ n) :
    HasStrictDerivAt f (deriv f x) x :=
  hf.contDiffAt.hasStrictDerivAt hn

/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
and `‖p x 1‖₊ < K`, then `f` is `K`-Lipschitz in a neighborhood of `x` within `s`. -/
theorem HasFTaylorSeriesUpToOn.exists_lipschitzOnWith_of_nnnorm_lt
    {f : E → F} {p : E → FormalMultilinearSeries ℝ E F} {s : Set E} {x : E}
    (hf : HasFTaylorSeriesUpToOn 1 f p (insert x s)) (hs : Convex ℝ s) (K : ℝ≥0)
    (hK : ‖p x 1‖₊ < K) : ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  set f' := fun y => continuousMultilinearCurryFin1 ℝ E F (p y 1)
  have hder : ∀ y ∈ s, HasFDerivWithinAt f (f' y) s y := fun y hy =>
    (hf.hasFDerivWithinAt le_rfl (subset_insert x s hy)).mono (subset_insert x s)
  have hcont : ContinuousWithinAt f' s x :=
    (continuousMultilinearCurryFin1 ℝ E F).continuousAt.comp_continuousWithinAt
      ((hf.cont _ le_rfl _ (mem_insert _ _)).mono (subset_insert x s))
  replace hK : ‖f' x‖₊ < K := by simpa only [f', LinearIsometryEquiv.nnnorm_map]
  exact
    hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt
      (eventually_nhdsWithin_iff.2 <| Eventually.of_forall hder) hcont K hK

/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
then `f` is Lipschitz in a neighborhood of `x` within `s`. -/
theorem HasFTaylorSeriesUpToOn.exists_lipschitzOnWith
    {f : E → F} {p : E → FormalMultilinearSeries ℝ E F} {s : Set E} {x : E}
    (hf : HasFTaylorSeriesUpToOn 1 f p (insert x s)) (hs : Convex ℝ s) :
    ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t :=
  (exists_gt _).imp <| hf.exists_lipschitzOnWith_of_nnnorm_lt hs

/-- If `f` is `C^1` within a convex set `s` at `x`, then it is Lipschitz on a neighborhood of `x`
within `s`. -/
theorem ContDiffWithinAt.exists_lipschitzOnWith
    {f : E → F} {s : Set E} {x : E}
    (hf : ContDiffWithinAt ℝ 1 f s x) (hs : Convex ℝ s) :
    ∃ K : ℝ≥0, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  rcases hf 1 le_rfl with ⟨t, hst, p, hp⟩
  rcases Metric.mem_nhdsWithin_iff.mp hst with ⟨ε, ε0, hε⟩
  replace hp : HasFTaylorSeriesUpToOn 1 f p (Metric.ball x ε ∩ insert x s) := hp.mono hε
  clear hst hε t
  rw [← insert_eq_of_mem (Metric.mem_ball_self ε0), ← insert_inter_distrib] at hp
  rcases hp.exists_lipschitzOnWith ((convex_ball _ _).inter hs) with ⟨K, t, hst, hft⟩
  rw [inter_comm, ← nhdsWithin_restrict' _ (Metric.ball_mem_nhds _ ε0)] at hst
  exact ⟨K, t, hst, hft⟩

/-- If `f` is `C^1` at `x` and `‖fderiv 𝕂 f x‖ < K`, then `f` is `K`-Lipschitz in a neighborhood of
`x`. -/
theorem ContDiffAt.exists_lipschitzOnWith_of_nnnorm_lt {f : E' → F'} {x : E'}
    (hf : ContDiffAt 𝕂 1 f x) (K : ℝ≥0) (hK : ‖fderiv 𝕂 f x‖₊ < K) :
    ∃ t ∈ 𝓝 x, LipschitzOnWith K f t :=
  (hf.hasStrictFDerivAt le_rfl).exists_lipschitzOnWith_of_nnnorm_lt K hK

/-- If `f` is `C^1` at `x`, then `f` is Lipschitz in a neighborhood of `x`. -/
theorem ContDiffAt.exists_lipschitzOnWith {f : E' → F'} {x : E'} (hf : ContDiffAt 𝕂 1 f x) :
    ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t :=
  (hf.hasStrictFDerivAt le_rfl).exists_lipschitzOnWith

/-- If `f` is `C^1`, it is locally Lipschitz. -/
lemma ContDiff.locallyLipschitz {f : E' → F'} (hf : ContDiff 𝕂 1 f) : LocallyLipschitz f := by
  intro x
  rcases hf.contDiffAt.exists_lipschitzOnWith with ⟨K, t, ht, hf⟩
  use K, t

/-- If `f` is `C¹` on a convex compact set `s`, it is Lipschitz on `s`. -/
theorem ContDiffOn.exists_lipschitzOnWith {s : Set E} {f : E → F} {n} (hf : ContDiffOn ℝ n f s)
    (hn : 1 ≤ n) (hs : Convex ℝ s) (hs' : IsCompact s) (hs'' : UniqueDiffOn ℝ s) :
    ∃ K, LipschitzOnWith K f s := by
  obtain ⟨M, M_nonneg, hM⟩ := (bddAbove_iff_exists_ge 0).mp
    (hs'.image_of_continuousOn (hf.continuousOn_fderivWithin hs'' hn).norm).bddAbove
  simp_rw [forall_mem_image] at hM
  use ⟨M, M_nonneg⟩
  exact Convex.lipschitzOnWith_of_nnnorm_fderivWithin_le (hf.differentiableOn hn) hM hs

/-- A `C¹` function is Lipschitz on each convex compact set. -/
theorem ContDiff.exists_lipschitzOnWith {s : Set E} {f : E → F} {n}
    (hf : ContDiff ℝ n f) (hn : 1 ≤ n) (hs : Convex ℝ s) (hs' : IsCompact s) :
    ∃ K, LipschitzOnWith K f s := by
  have : UniqueDiffOn ℝ s := by
    refine uniqueDiffOn_convex hs ?hs
    sorry -- `s` has non-empty interior: is an extra condition!
  exact hf.contDiffOn.exists_lipschitzOnWith hn hs hs' this

/-- A `C^1` function with compact support is Lipschitz. -/
theorem ContDiff.lipschitzWith_of_hasCompactSupport {f : E' → F'} {n : ℕ∞}
    (hf : HasCompactSupport f) (h'f : ContDiff 𝕂 n f) (hn : 1 ≤ n) :
    ∃ C, LipschitzWith C f := by
  obtain ⟨C, hC⟩ := (hf.fderiv 𝕂).exists_bound_of_continuous (h'f.continuous_fderiv hn)
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (h'f.differentiable hn) (fun x ↦ ?_)
  simp [← NNReal.coe_le_coe, hC x]

end Real
