/-
Copyright (c) 2023 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee, Geoffrey Irving
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Analytic manifolds (possibly with boundary or corners)

An analytic manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which changes of coordinates are analytic
everywhere.  The definition mirrors `IsManifold`, but using an `analyticGroupoid` in
place of `contDiffGroupoid`.  All analytic manifolds are smooth manifolds.

This file is deprecated: one should use `IsManifold I ω M` instead
-/

noncomputable section

/- Deactivate the linter as we don't want to change the statements inside the file, only warn
the user that the definitions they are using are deprecated. -/
set_option linter.deprecated false

open Set Filter Function

open scoped Manifold Filter Topology ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]

/-!
## `analyticGroupoid`

`f ∈ PartialHomeomorph H H` is in `analyticGroupoid I` if `f` and `f.symm` are smooth everywhere,
analytic on the interior, and map the interior to itself.  This allows us to define
`AnalyticManifold` including in cases with boundary.
-/

section analyticGroupoid

/-- An identity partial homeomorphism belongs to the analytic groupoid. -/
theorem ofSet_mem_analyticGroupoid {s : Set H} (hs : IsOpen s) :
    PartialHomeomorph.ofSet s hs ∈ analyticGroupoid I := by
  rw [analyticGroupoid, mem_groupoid_of_pregroupoid]
  suffices h : AnalyticOn 𝕜 (I ∘ I.symm) (I.symm ⁻¹' s ∩ range I) by
    simp [h, analyticPregroupoid]
  have hi : AnalyticOn 𝕜 id (univ : Set E) := analyticOn_id
  exact (hi.mono (subset_univ _)).congr (fun x hx ↦ I.right_inv hx.2)

/-- The composition of a partial homeomorphism from `H` to `M` and its inverse belongs to
the analytic groupoid. -/
theorem symm_trans_mem_analyticGroupoid (e : PartialHomeomorph M H) :
    e.symm.trans e ∈ analyticGroupoid I :=
  haveI : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target e.open_target :=
    PartialHomeomorph.symm_trans_self _
  StructureGroupoid.mem_of_eqOnSource _ (ofSet_mem_analyticGroupoid e.open_target) this

/-- The analytic groupoid is closed under restriction. -/
instance : ClosedUnderRestriction (analyticGroupoid I) :=
  (closedUnderRestriction_iff_id_le _).mpr
    (by
      rw [StructureGroupoid.le_iff]
      rintro e ⟨s, hs, hes⟩
      exact (analyticGroupoid I).mem_of_eqOnSource' _ _ (ofSet_mem_analyticGroupoid hs) hes)

/-- `f ∈ analyticGroupoid` iff it and its inverse are analytic within `range I`. -/
lemma mem_analyticGroupoid {I : ModelWithCorners 𝕜 E H} {f : PartialHomeomorph H H} :
    f ∈ analyticGroupoid I ↔
      AnalyticOn 𝕜 (I ∘ f ∘ I.symm) (I.symm ⁻¹' f.source ∩ range I) ∧
      AnalyticOn 𝕜 (I ∘ f.symm ∘ I.symm) (I.symm ⁻¹' f.target ∩ range I) := by
  rfl

/-- The analytic groupoid on a boundaryless charted space modeled on a complete vector space
consists of the partial homeomorphisms which are analytic and have analytic inverse. -/
theorem mem_analyticGroupoid_of_boundaryless [I.Boundaryless] (e : PartialHomeomorph H H) :
    e ∈ analyticGroupoid I ↔ AnalyticOnNhd 𝕜 (I ∘ e ∘ I.symm) (I '' e.source) ∧
      AnalyticOnNhd 𝕜 (I ∘ e.symm ∘ I.symm) (I '' e.target) := by
  simp only [mem_analyticGroupoid, I.range_eq_univ, inter_univ, I.image_eq]
  rw [IsOpen.analyticOn_iff_analyticOnNhd, IsOpen.analyticOn_iff_analyticOnNhd]
  · exact I.continuous_symm.isOpen_preimage _ e.open_target
  · exact I.continuous_symm.isOpen_preimage _ e.open_source

/-- `analyticGroupoid` is closed under products -/
theorem analyticGroupoid_prod {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace A] {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace B] {I : ModelWithCorners 𝕜 E A} {J : ModelWithCorners 𝕜 F B}
    {f : PartialHomeomorph A A} {g : PartialHomeomorph B B}
    (fa : f ∈ analyticGroupoid I) (ga : g ∈ analyticGroupoid J) :
    f.prod g ∈ analyticGroupoid (I.prod J) := by
  have pe : range (I.prod J) = (range I).prod (range J) := I.range_prod
  simp only [mem_analyticGroupoid] at fa ga ⊢
  exact ⟨AnalyticOn.prod
      (fa.1.comp analyticOn_fst fun _ m ↦ ⟨m.1.1, (pe ▸ m.2).1⟩)
      (ga.1.comp analyticOn_snd fun _ m ↦ ⟨m.1.2, (pe ▸ m.2).2⟩),
    AnalyticOn.prod
      (fa.2.comp analyticOn_fst fun _ m ↦ ⟨m.1.1, (pe ▸ m.2).1⟩)
      (ga.2.comp analyticOn_snd fun _ m ↦ ⟨m.1.2, (pe ▸ m.2).2⟩)⟩

end analyticGroupoid

section AnalyticManifold

/-- Normed spaces are analytic manifolds over themselves. -/
instance AnalyticManifold.self : AnalyticManifold 𝓘(𝕜, E) E where

/-- `M × N` is an analytic manifold if `M` and `N` are -/
instance AnalyticManifold.prod {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace A] {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace B] {I : ModelWithCorners 𝕜 E A} {J : ModelWithCorners 𝕜 F B}
    {M : Type} [TopologicalSpace M] [ChartedSpace A M] [m : AnalyticManifold I M]
    {N : Type} [TopologicalSpace N] [ChartedSpace B N] [n : AnalyticManifold J N] :
    AnalyticManifold (I.prod J) (M × N) where
  compatible := by
    intro f g ⟨f1, f2, hf1, hf2, fe⟩ ⟨g1, g2, hg1, hg2, ge⟩
    rw [← fe, ← ge, PartialHomeomorph.prod_symm, PartialHomeomorph.prod_trans]
    exact analyticGroupoid_prod (m.toHasGroupoid.compatible f2 g2)
      (n.toHasGroupoid.compatible hf2 hg2)

/-- Analytic manifolds are smooth manifolds. -/
instance AnalyticManifold.isManifold [ChartedSpace H M]
    [cm : AnalyticManifold I M] :
    IsManifold I ∞ M where
  compatible hf hg := ⟨(cm.compatible hf hg).1.contDiffOn I.uniqueDiffOn_preimage_source,
    (cm.compatible hg hf).1.contDiffOn I.uniqueDiffOn_preimage_source⟩


end AnalyticManifold
