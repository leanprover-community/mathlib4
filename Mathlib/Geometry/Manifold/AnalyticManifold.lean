/-
Copyright (c) 2023 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee, Geoffrey Irving
-/
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
# Analytic manifolds (possibly with boundary or corners)

An analytic manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which changes of coordinates are analytic in the
interior and smooth everywhere (including at the boundary).  The definition mirrors
`SmoothManifoldWithCorners`, but using an `analyticGroupoid` in place of `contDiffGroupoid`.  All
analytic manifolds are smooth manifolds.

Completeness is required throughout, but this is nonessential: it is due to many of the lemmas about
AnalyticWithinOn` requiring completeness for ease of proof.
-/

noncomputable section

open Set Filter Function

open scoped Manifold Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {H : Type*}
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M]

/-!
## `analyticGroupoid`

`f ∈ PartialHomeomorph H H` is in `analyticGroupoid I` if `f` and `f.symm` are smooth everywhere,
analytic on the interior, and map the interior to itself.  This allows us to define
`AnalyticManifold` including in cases with boundary.
-/

section analyticGroupoid

/-- Given a model with corners `(E, H)`, we define the pregroupoid of analytic transformations of
`H` as the maps that are `AnalyticWithinOn` when read in `E` through `I`.  Using `AnalyticWithinOn`
rather than `AnalyticOn` gives us meaningful definitions at boundary points. -/
def analyticPregroupoid : Pregroupoid H where
  property f s := AnalyticWithinOn 𝕜 (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)
  comp {f g u v} hf hg _ _ _ := by
    have : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by ext x; simp
    simp only [this]
    apply hg.comp
    · exact hf.mono fun _ ⟨hx1, hx2⟩ ↦ ⟨hx1.1, hx2⟩
    · rintro x ⟨hx1, _⟩
      simpa only [mfld_simps] using hx1.2
  id_mem := by
    apply (analyticOn_id 𝕜).analyticWithinOn.congr
    rintro x ⟨_, hx2⟩
    obtain ⟨y, hy⟩ := mem_range.1 hx2
    simp only [mfld_simps, ← hy]
  locality {f u} _ H := by
    apply analyticWithinOn_of_locally_analyticWithinOn
    rintro y ⟨hy1, hy2⟩
    obtain ⟨x, hx⟩ := mem_range.1 hy2
    simp only [mfld_simps, ← hx] at hy1 ⊢
    obtain ⟨v, v_open, xv, hv⟩ := H x hy1
    have : I.symm ⁻¹' (u ∩ v) ∩ range I = I.symm ⁻¹' u ∩ range I ∩ I.symm ⁻¹' v := by
      rw [preimage_inter, inter_assoc, inter_assoc, inter_comm _ (range I)]
    exact ⟨I.symm ⁻¹' v, v_open.preimage I.continuous_symm, by simpa, this ▸ hv⟩
  congr {f g u} _ fg hf := by
    apply hf.congr
    rintro y ⟨hy1, hy2⟩
    obtain ⟨x, hx⟩ := mem_range.1 hy2
    simp only [mfld_simps, ← hx] at hy1 ⊢
    rw [fg _ hy1]

/-- Given a model with corners `(E, H)`, we define the groupoid of analytic transformations of
`H` as the maps that are `AnalyticWithinOn` when read in `E` through `I`.  Using `AnalyticWithinOn`
rather than `AnalyticOn` gives us meaningful definitions at boundary points. -/
def analyticGroupoid : StructureGroupoid H :=
  (analyticPregroupoid I).groupoid

/-- An identity partial homeomorphism belongs to the analytic groupoid. -/
theorem ofSet_mem_analyticGroupoid {s : Set H} (hs : IsOpen s) :
    PartialHomeomorph.ofSet s hs ∈ analyticGroupoid I := by
  rw [analyticGroupoid, mem_groupoid_of_pregroupoid]
  suffices h : AnalyticWithinOn 𝕜 (I ∘ I.symm) (I.symm ⁻¹' s ∩ range I) by
    simp [h, analyticPregroupoid]
  have hi : AnalyticWithinOn 𝕜 id (univ : Set E) := (analyticOn_id _).analyticWithinOn
  exact (hi.mono (subset_univ _)).congr (fun x hx ↦ (I.right_inv hx.2).symm)

/-- The composition of a partial homeomorphism from `H` to `M` and its inverse belongs to
the analytic groupoid. -/
theorem symm_trans_mem_analyticGroupoid (e : PartialHomeomorph M H) :
    e.symm.trans e ∈ analyticGroupoid I :=
  haveI : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target e.open_target :=
    PartialHomeomorph.symm_trans_self _
  StructureGroupoid.mem_of_eqOnSource _ (ofSet_mem_analyticGroupoid I e.open_target) this

/-- The analytic groupoid is closed under restriction. -/
instance : ClosedUnderRestriction (analyticGroupoid I) :=
  (closedUnderRestriction_iff_id_le _).mpr
    (by
      rw [StructureGroupoid.le_iff]
      rintro e ⟨s, hs, hes⟩
      exact (analyticGroupoid I).mem_of_eqOnSource' _ _ (ofSet_mem_analyticGroupoid I hs) hes)

/-- `f ∈ analyticGroupoid` iff it and its inverse are analytic within `range I`. -/
lemma mem_analyticGroupoid {I : ModelWithCorners 𝕜 E H} {f : PartialHomeomorph H H} :
    f ∈ analyticGroupoid I ↔
      AnalyticWithinOn 𝕜 (I ∘ f ∘ I.symm) (I.symm ⁻¹' f.source ∩ range I) ∧
      AnalyticWithinOn 𝕜 (I ∘ f.symm ∘ I.symm) (I.symm ⁻¹' f.target ∩ range I) := by
  rfl

/-- The analytic groupoid on a boundaryless charted space modeled on a complete vector space
consists of the partial homeomorphisms which are analytic and have analytic inverse. -/
theorem mem_analyticGroupoid_of_boundaryless [I.Boundaryless] (e : PartialHomeomorph H H) :
    e ∈ analyticGroupoid I ↔ AnalyticOn 𝕜 (I ∘ e ∘ I.symm) (I '' e.source) ∧
      AnalyticOn 𝕜 (I ∘ e.symm ∘ I.symm) (I '' e.target) := by
  simp only [mem_analyticGroupoid, I.range_eq_univ, inter_univ, I.image_eq]
  rw [IsOpen.analyticWithinOn_iff_analyticOn, IsOpen.analyticWithinOn_iff_analyticOn]
  · exact I.continuous_symm.isOpen_preimage _ e.open_target
  · exact I.continuous_symm.isOpen_preimage _ e.open_source

/-- `analyticGroupoid` is closed under products -/
theorem analyticGroupoid_prod {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [TopologicalSpace A] {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] [TopologicalSpace B] {I : ModelWithCorners 𝕜 E A} {J : ModelWithCorners 𝕜 F B}
    {f : PartialHomeomorph A A} {g : PartialHomeomorph B B}
    (fa : f ∈ analyticGroupoid I) (ga : g ∈ analyticGroupoid J) :
    f.prod g ∈ analyticGroupoid (I.prod J) := by
  have pe : range (I.prod J) = (range I).prod (range J) := I.range_prod
  simp only [mem_analyticGroupoid, Function.comp, image_subset_iff] at fa ga ⊢
  exact ⟨AnalyticWithinOn.prod
      (fa.1.comp (analyticOn_fst _).analyticWithinOn fun _ m ↦ ⟨m.1.1, (pe ▸ m.2).1⟩)
      (ga.1.comp (analyticOn_snd _).analyticWithinOn fun _ m ↦ ⟨m.1.2, (pe ▸ m.2).2⟩),
    AnalyticWithinOn.prod
      (fa.2.comp (analyticOn_fst _).analyticWithinOn fun _ m ↦ ⟨m.1.1, (pe ▸ m.2).1⟩)
      (ga.2.comp (analyticOn_snd _).analyticWithinOn fun _ m ↦ ⟨m.1.2, (pe ▸ m.2).2⟩)⟩

end analyticGroupoid

section AnalyticManifold

/-- An analytic manifold w.r.t. a model `I : ModelWithCorners 𝕜 E H` is a charted space over `H`
s.t. all extended chart conversion maps are analytic. -/
class AnalyticManifold (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M]
  [ChartedSpace H M] extends HasGroupoid M (analyticGroupoid I) : Prop

/-- Normed spaces are analytic manifolds over themselves. -/
instance AnalyticManifold.self : AnalyticManifold 𝓘(𝕜, E) E where

/-- `M × N` is an analytic manifold if `M` and `N` are -/
instance AnalyticManifold.prod {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [TopologicalSpace A] {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] [TopologicalSpace B] {I : ModelWithCorners 𝕜 E A} {J : ModelWithCorners 𝕜 F B}
    {M : Type} [TopologicalSpace M] [ChartedSpace A M] [m : AnalyticManifold I M]
    {N : Type} [TopologicalSpace N] [ChartedSpace B N] [n : AnalyticManifold J N] :
    AnalyticManifold (I.prod J) (M × N) where
  compatible := by
    intro f g ⟨f1, f2, hf1, hf2, fe⟩ ⟨g1, g2, hg1, hg2, ge⟩
    rw [← fe, ← ge, PartialHomeomorph.prod_symm, PartialHomeomorph.prod_trans]
    exact analyticGroupoid_prod (m.toHasGroupoid.compatible f2 g2)
      (n.toHasGroupoid.compatible hf2 hg2)

/-- Analytic manifolds are smooth manifolds. -/
instance AnalyticManifold.smoothManifoldWithCorners [ChartedSpace H M] [cm : AnalyticManifold I M] :
    SmoothManifoldWithCorners I M where
  compatible := by
    intro f g hf hg
    have m := cm.compatible hf hg
    exact ⟨m.1.contDiffOn, m.2.contDiffOn⟩

end AnalyticManifold
