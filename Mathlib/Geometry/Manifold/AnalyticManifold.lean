/-
Copyright (c) 2023 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
# Analytic manifolds (possibly with boundary or corners)

An analytic manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which changes of coordinates are analytic in the
interior and smooth everywhere (including at the boundary).  The definition mirrors
`SmoothManifoldWithCorners`, but using an `analyticGroupoid` in place of `contDiffGroupoid`.  All
analytic manifolds are smooth manifolds.

For now we define only `analyticGroupoid`; an upcoming commit will add `AnalyticManifold` (see
https://github.com/leanprover-community/mathlib4/pull/10853).
-/

noncomputable section

open Set Filter Function

open scoped Manifold Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*}
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M]

/-!
## `analyticGroupoid`

`f ∈ PartialHomeomorph H H` is in `analyticGroupoid I` if `f` and `f.symm` are smooth everywhere,
analytic on the interior, and map the interior to itself.  This allows us to define
`AnalyticManifold` including in cases with boundary.
-/

section analyticGroupoid

/-- Given a model with corners `(E, H)`, we define the groupoid of analytic transformations of `H`
as the maps that are analytic and map interior to interior when read in `E` through `I`. We also
explicitly define that they are `C^∞` on the whole domain, since we are only requiring
analyticity on the interior of the domain. -/
def analyticGroupoid : StructureGroupoid H :=
  (contDiffGroupoid ∞ I) ⊓ Pregroupoid.groupoid
    { property := fun f s => AnalyticOn 𝕜 (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ interior (range I)) ∧
        (I.symm ⁻¹' s ∩ interior (range I)).image (I ∘ f ∘ I.symm) ⊆ interior (range I)
      comp := fun {f g u v} hf hg _ _ _ => by
        simp only [] at hf hg ⊢
        have comp : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by ext x; simp
        apply And.intro
        · simp only [comp, preimage_inter]
          refine hg.left.comp (hf.left.mono ?_) ?_
          · simp only [subset_inter_iff, inter_subset_right]
            rw [inter_assoc]
            simp
          · intro x hx
            apply And.intro
            · rw [mem_preimage, comp_apply, I.left_inv]
              exact hx.left.right
            · apply hf.right
              rw [mem_image]
              exact ⟨x, ⟨⟨hx.left.left, hx.right⟩, rfl⟩⟩
        · simp only [comp]
          rw [image_comp]
          intro x hx
          rw [mem_image] at hx
          rcases hx with ⟨x', hx'⟩
          refine hg.right ⟨x', And.intro ?_ hx'.right⟩
          apply And.intro
          · have hx'1 : x' ∈ ((v.preimage f).preimage (I.symm)).image (I ∘ f ∘ I.symm) := by
              refine image_subset (I ∘ f ∘ I.symm) ?_ hx'.left
              rw [preimage_inter]
              refine Subset.trans ?_ (u.preimage I.symm).inter_subset_right
              apply inter_subset_left
            rcases hx'1 with ⟨x'', hx''⟩
            rw [hx''.right.symm]
            simp only [comp_apply, mem_preimage, I.left_inv]
            exact hx''.left
          · rw [mem_image] at hx'
            rcases hx'.left with ⟨x'', hx''⟩
            exact hf.right ⟨x'', ⟨⟨hx''.left.left.left, hx''.left.right⟩, hx''.right⟩⟩
      id_mem := by
        apply And.intro
        · simp only [preimage_univ, univ_inter]
          exact AnalyticOn.congr isOpen_interior
            (f := (1 : E →L[𝕜] E)) (fun x _ => (1 : E →L[𝕜] E).analyticAt x)
            (fun z hz => (I.right_inv (interior_subset hz)).symm)
        · intro x hx
          simp only [id_comp, comp_apply, preimage_univ, univ_inter, mem_image] at hx
          rcases hx with ⟨y, hy⟩
          rw [← hy.right, I.right_inv (interior_subset hy.left)]
          exact hy.left
      locality := fun {f u} _ h => by
        simp only [] at h
        simp only [AnalyticOn]
        apply And.intro
        · intro x hx
          rcases h (I.symm x) (mem_preimage.mp hx.left) with ⟨v, hv⟩
          exact hv.right.right.left x ⟨mem_preimage.mpr ⟨hx.left, hv.right.left⟩, hx.right⟩
        · apply mapsTo'.mp
          simp only [MapsTo]
          intro x hx
          rcases h (I.symm x) hx.left with ⟨v, hv⟩
          apply hv.right.right.right
          rw [mem_image]
          have hx' := And.intro hx (mem_preimage.mpr hv.right.left)
          rw [← mem_inter_iff, inter_comm, ← inter_assoc, ← preimage_inter, inter_comm v u] at hx'
          exact ⟨x, ⟨hx', rfl⟩⟩
      congr := fun {f g u} hu fg hf => by
        simp only [] at hf ⊢
        apply And.intro
        · refine AnalyticOn.congr (IsOpen.inter (hu.preimage I.continuous_symm) isOpen_interior)
            hf.left ?_
          intro z hz
          simp only [comp_apply]
          rw [fg (I.symm z) hz.left]
        · intro x hx
          apply hf.right
          rw [mem_image] at hx ⊢
          rcases hx with ⟨y, hy⟩
          refine ⟨y, ⟨hy.left, ?_⟩⟩
          rw [comp_apply, comp_apply, fg (I.symm y) hy.left.left] at hy
          exact hy.right }

/-- An identity partial homeomorphism belongs to the analytic groupoid. -/
theorem ofSet_mem_analyticGroupoid {s : Set H} (hs : IsOpen s) :
    PartialHomeomorph.ofSet s hs ∈ analyticGroupoid I := by
  rw [analyticGroupoid]
  refine And.intro (ofSet_mem_contDiffGroupoid ∞ I hs) ?_
  apply mem_groupoid_of_pregroupoid.mpr
  suffices h : AnalyticOn 𝕜 (I ∘ I.symm) (I.symm ⁻¹' s ∩ interior (range I)) ∧
      (I.symm ⁻¹' s ∩ interior (range I)).image (I ∘ I.symm) ⊆ interior (range I) by
    simp only [PartialHomeomorph.ofSet_apply, id_comp, PartialHomeomorph.ofSet_toPartialEquiv,
      PartialEquiv.ofSet_source, h, comp_apply, mem_range, image_subset_iff, true_and,
      PartialHomeomorph.ofSet_symm, PartialEquiv.ofSet_target, and_self]
    intro x hx
    refine mem_preimage.mpr ?_
    rw [← I.right_inv (interior_subset hx.right)] at hx
    exact hx.right
  apply And.intro
  · have : AnalyticOn 𝕜 (1 : E →L[𝕜] E) (univ : Set E) := (fun x _ => (1 : E →L[𝕜] E).analyticAt x)
    exact (this.mono (subset_univ (s.preimage (I.symm) ∩ interior (range I)))).congr
      ((hs.preimage I.continuous_symm).inter isOpen_interior)
      fun z hz => (I.right_inv (interior_subset hz.right)).symm
  · intro x hx
    simp only [comp_apply, mem_image] at hx
    rcases hx with ⟨y, hy⟩
    rw [← hy.right, I.right_inv (interior_subset hy.left.right)]
    exact hy.left.right

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
      apply (analyticGroupoid I).mem_of_eqOnSource' _ _ _ hes
      exact ofSet_mem_analyticGroupoid I hs)

/-- The analytic groupoid on a boundaryless charted space modeled on a complete vector space
consists of the partial homeomorphisms which are analytic and have analytic inverse. -/
theorem mem_analyticGroupoid_of_boundaryless [CompleteSpace E] [I.Boundaryless]
    (e : PartialHomeomorph H H) :
    e ∈ analyticGroupoid I ↔ AnalyticOn 𝕜 (I ∘ e ∘ I.symm) (I '' e.source) ∧
    AnalyticOn 𝕜 (I ∘ e.symm ∘ I.symm) (I '' e.target) := by
  apply Iff.intro
  · intro he
    have := mem_groupoid_of_pregroupoid.mp he.right
    simp only [I.image_eq, I.range_eq_univ, interior_univ, subset_univ, and_true] at this ⊢
    exact this
  · intro he
    apply And.intro
    all_goals apply mem_groupoid_of_pregroupoid.mpr; simp only [I.image_eq, I.range_eq_univ,
      interior_univ, subset_univ, and_true, contDiffPregroupoid] at he ⊢
    · exact ⟨he.left.contDiffOn, he.right.contDiffOn⟩
    · exact he

end analyticGroupoid
