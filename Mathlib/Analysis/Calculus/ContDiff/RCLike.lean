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

variable {n : WithTop ℕ∞} {𝕂 : Type*} [RCLike 𝕂] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕂 E'] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕂 F']

/-- If a function has a Taylor series at order at least 1, then at points in the interior of the
domain of definition, the term of order 1 of this series is a strict derivative of `f`. -/
theorem HasFTaylorSeriesUpToOn.hasStrictFDerivAt {n : WithTop ℕ∞}
    {s : Set E'} {f : E' → F'} {x : E'}
    {p : E' → FormalMultilinearSeries 𝕂 E' F'} (hf : HasFTaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
    (hs : s ∈ 𝓝 x) : HasStrictFDerivAt f ((continuousMultilinearCurryFin1 𝕂 E' F') (p x 1)) x :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hf.eventually_hasFDerivAt hn hs) <|
    (continuousMultilinearCurryFin1 𝕂 E' F').continuousAt.comp <| (hf.cont 1 hn).continuousAt hs

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
theorem ContDiffAt.hasStrictFDerivAt' {f : E' → F'} {f' : E' →L[𝕂] F'} {x : E'}
    (hf : ContDiffAt 𝕂 n f x) (hf' : HasFDerivAt f f' x) (hn : 1 ≤ n) :
    HasStrictFDerivAt f f' x := by
  rcases hf.of_le hn 1 le_rfl with ⟨u, H, p, hp⟩
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

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {p : E → FormalMultilinearSeries ℝ E F} {s : Set E} {x : E}

/-- If `f` has a formal Taylor series `p` up to order `1` on `{x} ∪ s`, where `s` is a convex set,
and `‖p x 1‖₊ < K`, then `f` is `K`-Lipschitz in a neighborhood of `x` within `s`. -/
theorem HasFTaylorSeriesUpToOn.exists_lipschitzOnWith_of_nnnorm_lt
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
    (hf : HasFTaylorSeriesUpToOn 1 f p (insert x s)) (hs : Convex ℝ s) :
    ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t :=
  (exists_gt _).imp <| hf.exists_lipschitzOnWith_of_nnnorm_lt hs

/-- If `f` is `C^1` within a convex set `s` at `x`, then it is Lipschitz on a neighborhood of `x`
within `s`. -/
theorem ContDiffWithinAt.exists_lipschitzOnWith
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

/-- If `f` is `C^1` at `x` and `K > ‖fderiv 𝕂 f x‖`, then `f` is `K`-Lipschitz in a neighborhood of
`x`. -/
theorem ContDiffAt.exists_lipschitzOnWith_of_nnnorm_lt {f : E' → F'} {x : E'}
    (hf : ContDiffAt 𝕂 1 f x) (K : ℝ≥0) (hK : ‖fderiv 𝕂 f x‖₊ < K) :
    ∃ t ∈ 𝓝 x, LipschitzOnWith K f t :=
  (hf.hasStrictFDerivAt le_rfl).exists_lipschitzOnWith_of_nnnorm_lt K hK

/-- If `f` is `C^1` at `x`, then `f` is Lipschitz in a neighborhood of `x`. -/
theorem ContDiffAt.exists_lipschitzOnWith {f : E' → F'} {x : E'} (hf : ContDiffAt 𝕂 1 f x) :
    ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t :=
  (hf.hasStrictFDerivAt le_rfl).exists_lipschitzOnWith

/-- If `f` is `C¹` on a convex set `s`, it is locally Lipschitz on `s`. -/
lemma ContDiffOn.locallyLipschitzOn {f : E → F} {s : Set E} (hs : Convex ℝ s)
    (hf : ContDiffOn ℝ 1 f s) : LocallyLipschitzOn s f := by
  intro x hx
  obtain ⟨K, t, ht, hf⟩ := ContDiffWithinAt.exists_lipschitzOnWith (hf x hx) hs
  use K, t

/-- If `f` is `C¹`, it is locally Lipschitz. -/
lemma ContDiff.locallyLipschitz {f : E' → F'} (hf : ContDiff 𝕂 1 f) : LocallyLipschitz f := by
  intro x
  rcases hf.contDiffAt.exists_lipschitzOnWith with ⟨K, t, ht, hf⟩
  use K, t

-- missing lemma, should be easy (but irrelevant for this PR)
lemma LipschitzOnWith.closure {K}
    (hcont : ContinuousOn f (closure s)) (hf : LipschitzOnWith K f s) :
    LipschitzOnWith K f (closure s) := by
  sorry

-- TODO: move to Lipschitz.lean
/-- If `f` is Lipschitz on a collection of sets `sᵢ` with constants `Kᵢ`,
it is also Lipschitz on `⋃ i, sᵢ` with constant `sup Kᵢ` (provided that supremum is finite). -/
lemma LipschitzOnWith.sup {f : E → F} {ι : Type*} {s : ι → Set E} {K : ι → ℝ≥0} {K' : ℝ≥0}
    (hf : ∀ i, LipschitzOnWith (K i) f (s i)) (hK' : ∀ i, K i ≤ K') :
    LipschitzOnWith K' f (⋃ i, s i) := by
  sorry

-- TODO: move to Lipschitz.lean
/-- If `f` is locally Lipschitz on a compact set `s`, it is Lipschitz on `s`. -/
lemma LocallyLipschitzOn.exists_lipschitzOnWith_of_compact {f : E → F} (hs : IsCompact s)
    (hf : LocallyLipschitzOn s f) : ∃ K, LipschitzOnWith K f s := by
  -- At each point `x`, you have a neighbourhood `tₓ`
  -- on which `f` is Lipschitz with some constant `Kₓ`.
  choose Kx tx htx hfx using hf
  -- Finitely many of these cover `s` (by compactness).
  obtain ⟨ti, hti⟩ := hs.elim_nhdsWithin_subcover' tx htx
  let Ki' : ti → ℝ≥0 := fun ⟨i, _hi⟩ ↦ Kx i.2
  -- Taking the maximum of the corresponding Kᵢ gives you a Lipschitz constant for `f` on `s`.
  use iSup Ki'
  have : s = ⋃ i ∈ ti, tx i.2 := sorry
  simp_rw [this]
  -- make this work
  -- apply LipschitzOnWith.sup (f := f) (K' := iSup Ki') (ι := ti)--(K := Ki')
  sorry

/-- If `f` is `C¹` on a convex compact set `s`, it is Lipschitz on `s`. -/
theorem ContDiffOn.exists_lipschitzOnWith {s : Set E} {f : E → F} {n} (hf : ContDiffOn ℝ n f s)
    (hn : 1 ≤ n) (hs : Convex ℝ s) (hs' : IsCompact s) :
    ∃ K, LipschitzOnWith K f s := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs'
  apply (hf.of_le hn).locallyLipschitzOn hs

/-- A `C^n` function with compact support is Lipschitz. -/
theorem ContDiff.lipschitzWith_of_hasCompactSupport {f : E' → F'}
    (hf : HasCompactSupport f) (h'f : ContDiff 𝕂 n f) (hn : 1 ≤ n) :
    ∃ C, LipschitzWith C f := by
  obtain ⟨C, hC⟩ := (hf.fderiv 𝕂).exists_bound_of_continuous (h'f.continuous_fderiv hn)
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (h'f.differentiable hn) (fun x ↦ ?_)
  simp [← NNReal.coe_le_coe, hC x]

end Real
