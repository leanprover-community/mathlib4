/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Analysis.Normed.Module.ContinuousRightInverse
public import Mathlib.Analysis.Normed.Module.Complemented
public import Mathlib.Analysis.Normed.Operator.Banach

/-! # Regular points of MDifferentiable maps

TODO: better doc-string

-/

open Function Set Topology

public section

universe u
-- A `NontriviallyNormedField` suffices; one lemma requires 𝕜 to be complete.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F F' G : Type*} {E' : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold I' n M']
variable {f : M → M'} {x : M} {n : WithTop ℕ∞}

/-- If `f : M → M'` has injective differential at `x`, it is `MDifferentiable` at `x`. -/
lemma mdifferentiableAt_of_mfderiv_surjective {f : M → M'} (hf : Surjective (mfderiv I I' f x)) :
    MDifferentiableAt I I' f x := by
  by_cases h: Subsingleton E
  · exact mdifferentiable_of_subsingleton.mdifferentiableAt
  · by_contra h'
    replace hf : (mfderiv I I' f x).toLinearMap.range = ⊤ := by rwa [LinearMap.range_eq_top]
    have hf' : (mfderiv I I' f x).range = ⊥ := by simp [mfderiv_zero_of_not_mdifferentiableAt h']
    have : Subsingleton (Submodule 𝕜 E) := subsingleton_of_bot_eq_top (by
      simp only [hf'] at hf; sorry) -- universe issues, why? exact hf
    simp_all only [Submodule.subsingleton_iff]

variable (I I' f x) in
/-- We say a map `f : M → M` has a regular point at `x` if the `fderiv` of
`writtenInExtChartAt I I f x` at `x' := extChartAt I x x` has a bounded right inverse. -/
@[expose] def IsRegularPoint (f : M → M') (x : M) : Prop :=
  fderiv 𝕜 (writtenInExtChartAt I I' x f) (extChartAt I x x) |>.HasBoundedRightInverse

lemma isRegularPointAt_iff {f : M → M'} {x : M} :
  IsRegularPoint I I' f x ↔
    (fderiv 𝕜 (writtenInExtChartAt I I' x f) (extChartAt I x x)).HasBoundedRightInverse := by rfl

/-- Whether `f` has a regular point at `x` can be tested in any extended charts for the manifold. -/
lemma isRegularPointAt_iff_extend {f : M → M'} {x : M}
    {φ : OpenPartialHomeomorph M H} {ψ : OpenPartialHomeomorph M' H'}
    (hφ : φ ∈ IsManifold.maximalAtlas I n M) (hψ : ψ ∈ IsManifold.maximalAtlas I' n M')
    (hxφ : x ∈ φ.source) (hxψ : f x ∈ ψ.source) :
    IsRegularPoint I I' f x ↔
      (fderiv 𝕜 (ψ.extend I' ∘ f ∘ (φ.extend I).symm) (φ.extend I x)).HasBoundedRightInverse := by
  sorry

namespace IsRegularPoint

variable {f g : M → M'} {x : M}

private lemma fderiv_surjective (hf : IsRegularPoint I I' f x) :
    Surjective (fderiv 𝕜 (writtenInExtChartAt I I' x f) (extChartAt I x x)) := hf.surjective

-- I *think* this lemma is useful for the proof of `comp`.
-- add `differentiableAt_of_fderiv_surjective`, then deduce this lemma!
lemma differentiableAt_writtenInExtChartAt (hf : IsRegularPoint I I' f x) :
    DifferentiableAt 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x) x) :=
  sorry -- differentiableAt_of_fderiv_surjective hf.fderiv_surjective

open IsManifold in
lemma mfderiv_surjective [IsManifold I 1 M] [IsManifold I' 1 M'] (hf : IsRegularPoint I I' f x) :
    Surjective (mfderiv I I' f x) := by
  -- TODO: add a version of foo for surjectivity
  --rw [← foo (n := 1) (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas (f x))
  --  (mem_chart_source H x) (mem_chart_source H' (f x))]
  --exact hf.fderiv_surjective
  sorry

lemma mdifferentiableAt [IsManifold I 1 M] [IsManifold I' 1 M'] (hf : IsRegularPoint I I' f x) :
    MDifferentiableAt I I' f x :=
  mdifferentiableAt_of_mfderiv_surjective hf.mfderiv_surjective

variable [IsManifold I 1 M] [IsManifold I' 1 M'] in
lemma continuousAt (hf : IsRegularPoint I I' f x) : ContinuousAt f x :=
  hf.mdifferentiableAt.continuousAt

lemma congr (hf : IsRegularPoint I I' f x) (hfg : g =ᶠ[𝓝 x] f) : IsRegularPoint I I' g x := by
  unfold IsRegularPoint at hf ⊢
  have aux : g ∘ (extChartAt I x).symm =ᶠ[𝓝 ((extChartAt I x) x)] f ∘ (extChartAt I x).symm := by
    apply hfg.comp_tendsto
    -- should this be a separate lemma?
    have := ContinuousAt.tendsto (f := (extChartAt I x).symm) (continuousAt_extChartAt_symm x)
    rwa [extChartAt_to_inv x] at this
  rw [writtenInExtChartAt, hfg.eq_of_nhds, (aux.fun_comp _).fderiv_eq]
  exact hf

variable [IsManifold I 1 M] [IsManifold J 1 N] [IsManifold I' 1 M'] [IsManifold J' 1 N'] in
lemma prodMap {y : N} (hf : IsRegularPoint I I' f x) {g : N → N'} (hg : IsRegularPoint J J' g y) :
    IsRegularPoint (I.prod J) (I'.prod J') (Prod.map f g) (x, y) := by
  have hf' := hf.mdifferentiableAt
  have hg' := hg.mdifferentiableAt
  unfold IsRegularPoint at hf hg ⊢
  rw [writtenInExtChart_prod] -- TODO misnamed lemma!
  -- missing lemma: fderiv of Prod.map (assuming both maps are differentiable, I presume?)
  -- then hopefully just
  -- apply ContinuousLinearMap.HasBoundedRightInverse.prodMap
  -- seeds from the immersion proof
  -- swap
  -- · have : (fun x ↦ (Prod.map f g x).1) = (fun x ↦ f x.1) := sorry
  --   rw [this]
  --   have (x : M × N) : MDifferentiableAt (I.prod J) I (fun x : M × N ↦ x.1) x := sorry
  --   sorry --apply MDifferentiableAt.comp x.1 this hf
  -- convert hf.prodMap hg
  -- simp only [Prod.map_apply, Prod.map_fst, Prod.map_snd]
  sorry

lemma of_isInvertible (hf : (mfderiv I I' f x).IsInvertible) : IsRegularPoint I I' f x := by
  sorry

lemma _root_.IsLocalDiffeomorphAt.isRegularPoint
    (hf : IsLocalDiffeomorphAt I I' n f x) (hn : n ≠ 0) : IsRegularPoint I I' f x :=
  of_isInvertible (hf.isInvertible_mfderiv hn)

/-- If `f` is split at `x` and `g` is split at `f x`, then `g ∘ f` is split at `x`. -/
-- TODO: I guess we don't need completeness at all!
lemma comp [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    {g : M' → N} (hg : IsRegularPoint I' J g (f x)) (hf : IsRegularPoint I I' f x) :
    IsRegularPoint I J (g ∘ f) x := by
  unfold IsRegularPoint at hf hg ⊢
  have aux := hg.comp hf
  sorry
  -- have hg' := hg.differentiableAt_writtenInExtChartAt
  -- have hx' :
  --     (writtenInExtChartAt I I' x f) ((extChartAt I x) x) = (extChartAt I' (f x)) (f x) := by simp
  -- rw [← hx'] at hg'
  -- -- better: do a calc proof of the mfderiv!

  -- have aux := fderiv_comp (f := writtenInExtChartAt I I' x f) (extChartAt I x x)
  --   hg' hf.differentiableAt_writtenInExtChartAt
  -- unfold MSplitsAt at hf hg ⊢
  -- have loc := hg.comp hf
  -- --rw [aux] at loc--rw [mSplitsAt_iff] at loc
  -- --unfold MSplitsAt
  -- --apply loc
  -- --rw [fderiv_comp]
  -- sorry -- needs redoing!
  -- /- rw [MSplitsAt] -- slight code smell?
  -- rw [mfderiv_comp x (mdifferentiableAt_of_mfderiv_injective hg.mfderiv_injective)
  --   (mdifferentiableAt_of_mfderiv_injective hf.mfderiv_injective)]
  -- have : CompleteSpace (TangentSpace I x) := by assumption
  -- have : CompleteSpace (TangentSpace I' (f x)) := by assumption
  -- have : CompleteSpace (TangentSpace J (g (f x))) := by assumption
  -- rw [MSplitsAt] at hf hg
  -- apply hg.comp hf -/

lemma of_comp {g : M' → N} (hg : IsRegularPoint I' J g (f x)) (hfg : IsRegularPoint I J (g ∘ f) x) :
    IsRegularPoint I I' f x := by
  sorry -- reduce to Splits.of_comp and some local computation

lemma of_comp_iff [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    {g : M' → N} (hg : IsRegularPoint I' J g (f x)) :
    IsRegularPoint I J (g ∘ f) x ↔ IsRegularPoint I I' f x :=
  ⟨fun hfg ↦ hg.of_comp hfg, fun hf ↦ hg.comp hf⟩

lemma comp_isLocalDiffeomorphAt_left [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    (hf : IsRegularPoint I I' f x) {f₀ : N → M} {y : N} (hxy : f₀ y = x)
    (hf₀ : IsLocalDiffeomorphAt J I n f₀ y) (hn : n ≠ 0) :
    IsRegularPoint J I' (f ∘ f₀) y :=
  (hxy ▸ hf).comp (hf₀.isRegularPoint hn)

lemma comp_isLocalDiffeomorphAt_left_iff [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    {f₀ : N → M} {y : N} (hxy : f₀ y = x) (hf₀ : IsLocalDiffeomorphAt J I n f₀ y) (hn : n ≠ 0) :
    IsRegularPoint I I' f x ↔ IsRegularPoint J I' (f ∘ f₀) y := by
  refine ⟨fun hf ↦ hf.comp_isLocalDiffeomorphAt_left hxy hf₀ hn, fun h ↦ ?_⟩
  have hg₀' : IsLocalDiffeomorphAt I J n hf₀.localInverse (f₀ y) :=
    hf₀.localInverse_isLocalDiffeomorphAt
  have : hf₀.localInverse x = y := hxy ▸ hf₀.localInverse_left_inv hf₀.localInverse_mem_target
  have : IsRegularPoint I I' (f ∘ f₀ ∘ hf₀.localInverse) x :=
    h.comp_isLocalDiffeomorphAt_left this (hxy ▸ hg₀') hn
  apply this.congr
  exact (hxy ▸ hf₀.localInverse_eventuallyEq_right.symm).fun_comp f

lemma comp_isLocalDiffeomorphAt_right [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    (hf : IsRegularPoint I I' f x) {g : M' → N} (hg : IsLocalDiffeomorphAt I' J n g (f x)) (hn : n ≠ 0) :
    IsRegularPoint I J (g ∘ f) x :=
  (hg.isRegularPoint hn).comp hf

-- TODO: fix the last sorry, is a small mathematical question
lemma comp_isLocalDiffeomorphAt_right_iff [CompleteSpace E] [CompleteSpace F] [CompleteSpace E']
    [IsManifold I 1 M] [IsManifold J 1 N]
    {g : M' → N} (hg : IsLocalDiffeomorphAt I' J n g (f x)) (hn : n ≠ 0) :
    IsRegularPoint I I' f x ↔ IsRegularPoint I J (g ∘ f) x := by
  refine ⟨fun hf ↦ hf.comp_isLocalDiffeomorphAt_right hg hn,
    fun h ↦ ?_⟩
  have hg' : IsLocalDiffeomorphAt J I' n hg.localInverse (g (f x)) :=
    hg.localInverse_isLocalDiffeomorphAt
  apply (h.comp_isLocalDiffeomorphAt_right hg' hn).congr
  symm
  have := hg.localInverse_eventuallyEq_left

  -- question: must we have `ContinuousAt f x`? if so, the proof is easy

  -- this certainly holds... but is not what we want!
  have aux : ContinuousAt (hg.localInverse.toPartialEquiv ∘ g ∘ f) x := by
    apply ContinuousAt.comp ?_ h.continuousAt
    sorry -- missing prereq, local inverse of a local diffeo is continuous at its point

  have hf : ContinuousAt f x := by
    -- issue: cannot apply ContinuousAt.congr_of_eventuallyEq aux as that'd be cyclic!
    sorry
  exact Filter.eventuallyEq_of_mem (hf this) (by intro; simp)

/-- If `mfderiv I J f x` is surjective and `N` is finite-dimensional,
then `x` is a regular point. -/
lemma of_surjective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E']
    (hf' : Surjective (mfderiv I I' f x)) : IsRegularPoint I I' f x := by
  unfold IsRegularPoint
  apply ContinuousLinearMap.HasBoundedRightInverse.of_surjective_of_finiteDimensional
  sorry -- use hf', and a lemma foo' for surjectivity!

end IsRegularPoint
