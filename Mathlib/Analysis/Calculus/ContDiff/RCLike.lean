/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue

#align_import analysis.calculus.cont_diff from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

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

variable {n : ℕ∞} {𝕂 : Type*} [RCLike 𝕂] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕂 E']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕂 F']

/-- If a function has a Taylor series at order at least 1, then at points in the interior of the
    domain of definition, the term of order 1 of this series is a strict derivative of `f`. -/
theorem HasFTaylorSeriesUpToOn.hasStrictFDerivAt {s : Set E'} {f : E' → F'} {x : E'}
    {p : E' → FormalMultilinearSeries 𝕂 E' F'} (hf : HasFTaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
    (hs : s ∈ 𝓝 x) : HasStrictFDerivAt f ((continuousMultilinearCurryFin1 𝕂 E' F') (p x 1)) x :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hf.eventually_hasFDerivAt hn hs) <|
    (continuousMultilinearCurryFin1 𝕂 E' F').continuousAt.comp <| (hf.cont 1 hn).continuousAt hs
#align has_ftaylor_series_up_to_on.has_strict_fderiv_at HasFTaylorSeriesUpToOn.hasStrictFDerivAt

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
theorem ContDiffAt.hasStrictFDerivAt' {f : E' → F'} {f' : E' →L[𝕂] F'} {x : E'}
    (hf : ContDiffAt 𝕂 n f x) (hf' : HasFDerivAt f f' x) (hn : 1 ≤ n) :
    HasStrictFDerivAt f f' x := by
  rcases hf 1 hn with ⟨u, H, p, hp⟩
  simp only [nhdsWithin_univ, mem_univ, insert_eq_of_mem] at H
  have := hp.hasStrictFDerivAt le_rfl H
  rwa [hf'.unique this.hasFDerivAt]
#align cont_diff_at.has_strict_fderiv_at' ContDiffAt.hasStrictFDerivAt'

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
theorem ContDiffAt.hasStrictDerivAt' {f : 𝕂 → F'} {f' : F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x)
    (hf' : HasDerivAt f f' x) (hn : 1 ≤ n) : HasStrictDerivAt f f' x :=
  hf.hasStrictFDerivAt' hf' hn
#align cont_diff_at.has_strict_deriv_at' ContDiffAt.hasStrictDerivAt'

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
theorem ContDiffAt.hasStrictFDerivAt {f : E' → F'} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) :
    HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.hasStrictFDerivAt' (hf.differentiableAt hn).hasFDerivAt hn
#align cont_diff_at.has_strict_fderiv_at ContDiffAt.hasStrictFDerivAt

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
theorem ContDiffAt.hasStrictDerivAt {f : 𝕂 → F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) :
    HasStrictDerivAt f (deriv f x) x :=
  (hf.hasStrictFDerivAt hn).hasStrictDerivAt
#align cont_diff_at.has_strict_deriv_at ContDiffAt.hasStrictDerivAt

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
theorem ContDiff.hasStrictFDerivAt {f : E' → F'} {x : E'} (hf : ContDiff 𝕂 n f) (hn : 1 ≤ n) :
    HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.contDiffAt.hasStrictFDerivAt hn
#align cont_diff.has_strict_fderiv_at ContDiff.hasStrictFDerivAt

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
theorem ContDiff.hasStrictDerivAt {f : 𝕂 → F'} {x : 𝕂} (hf : ContDiff 𝕂 n f) (hn : 1 ≤ n) :
    HasStrictDerivAt f (deriv f x) x :=
  hf.contDiffAt.hasStrictDerivAt hn
#align cont_diff.has_strict_deriv_at ContDiff.hasStrictDerivAt

/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
and `‖p x 1‖₊ < K`, then `f` is `K`-Lipschitz in a neighborhood of `x` within `s`. -/
theorem HasFTaylorSeriesUpToOn.exists_lipschitzOnWith_of_nnnorm_lt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {p : E → FormalMultilinearSeries ℝ E F} {s : Set E} {x : E}
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
      (eventually_nhdsWithin_iff.2 <| eventually_of_forall hder) hcont K hK
#align has_ftaylor_series_up_to_on.exists_lipschitz_on_with_of_nnnorm_lt HasFTaylorSeriesUpToOn.exists_lipschitzOnWith_of_nnnorm_lt

/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
then `f` is Lipschitz in a neighborhood of `x` within `s`. -/
theorem HasFTaylorSeriesUpToOn.exists_lipschitzOnWith {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {p : E → FormalMultilinearSeries ℝ E F} {s : Set E} {x : E}
    (hf : HasFTaylorSeriesUpToOn 1 f p (insert x s)) (hs : Convex ℝ s) :
    ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t :=
  (exists_gt _).imp <| hf.exists_lipschitzOnWith_of_nnnorm_lt hs
#align has_ftaylor_series_up_to_on.exists_lipschitz_on_with HasFTaylorSeriesUpToOn.exists_lipschitzOnWith

/-- If `f` is `C^1` within a convex set `s` at `x`, then it is Lipschitz on a neighborhood of `x`
within `s`. -/
theorem ContDiffWithinAt.exists_lipschitzOnWith {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {s : Set E} {x : E}
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
#align cont_diff_within_at.exists_lipschitz_on_with ContDiffWithinAt.exists_lipschitzOnWith

/-- If `f` is `C^1` at `x` and `K > ‖fderiv 𝕂 f x‖`, then `f` is `K`-Lipschitz in a neighborhood of
`x`. -/
theorem ContDiffAt.exists_lipschitzOnWith_of_nnnorm_lt {f : E' → F'} {x : E'}
    (hf : ContDiffAt 𝕂 1 f x) (K : ℝ≥0) (hK : ‖fderiv 𝕂 f x‖₊ < K) :
    ∃ t ∈ 𝓝 x, LipschitzOnWith K f t :=
  (hf.hasStrictFDerivAt le_rfl).exists_lipschitzOnWith_of_nnnorm_lt K hK
#align cont_diff_at.exists_lipschitz_on_with_of_nnnorm_lt ContDiffAt.exists_lipschitzOnWith_of_nnnorm_lt

/-- If `f` is `C^1` at `x`, then `f` is Lipschitz in a neighborhood of `x`. -/
theorem ContDiffAt.exists_lipschitzOnWith {f : E' → F'} {x : E'} (hf : ContDiffAt 𝕂 1 f x) :
    ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t :=
  (hf.hasStrictFDerivAt le_rfl).exists_lipschitzOnWith
#align cont_diff_at.exists_lipschitz_on_with ContDiffAt.exists_lipschitzOnWith

/-- If `f` is `C^1`, it is locally Lipschitz. -/
lemma ContDiff.locallyLipschitz {f : E' → F'} (hf : ContDiff 𝕂 1 f) : LocallyLipschitz f := by
  intro x
  rcases hf.contDiffAt.exists_lipschitzOnWith with ⟨K, t, ht, hf⟩
  use K, t

/-- A `C^1` function with compact support is Lipschitz. -/
theorem ContDiff.lipschitzWith_of_hasCompactSupport {f : E' → F'} {n : ℕ∞}
    (hf : HasCompactSupport f) (h'f : ContDiff 𝕂 n f) (hn : 1 ≤ n) :
    ∃ C, LipschitzWith C f := by
  obtain ⟨C, hC⟩ := (hf.fderiv 𝕂).exists_bound_of_continuous (h'f.continuous_fderiv hn)
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (h'f.differentiable hn) (fun x ↦ ?_)
  simp [← NNReal.coe_le_coe, hC x]

end Real
