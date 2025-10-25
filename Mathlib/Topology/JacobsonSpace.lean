/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Separation.Regular
import Mathlib.Tactic.StacksAttribute

/-!

# Jacobson spaces

## Main results
- `JacobsonSpace`: The class of Jacobson spaces, i.e.
  spaces such that the set of closed points are dense in every closed subspace.
- `jacobsonSpace_iff_locallyClosed`:
  `X` is a Jacobson space iff every locally closed subset contains a closed point of `X`.
- `JacobsonSpace.discreteTopology`:
  If `X` only has finitely many closed points, then the topology on `X` is discrete.

## References
- https://stacks.math.columbia.edu/tag/005T

-/

open Topology TopologicalSpace

variable (X) {Y} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

section closedPoints

/-- The set of closed points. -/
def closedPoints : Set X := setOf (IsClosed {·})

variable {X}

@[simp]
lemma mem_closedPoints_iff {x} : x ∈ closedPoints X ↔ IsClosed {x} := Iff.rfl

lemma preimage_closedPoints_subset (hf : Function.Injective f) (hf' : Continuous f) :
    f ⁻¹' closedPoints Y ⊆ closedPoints X := by
  intro x hx
  rw [mem_closedPoints_iff]
  convert continuous_iff_isClosed.mp hf' _ hx
  rw [← Set.image_singleton, Set.preimage_image_eq _ hf]

lemma Topology.IsClosedEmbedding.preimage_closedPoints (hf : IsClosedEmbedding f) :
    f ⁻¹' closedPoints Y = closedPoints X := by
  ext x
  simp [mem_closedPoints_iff, ← Set.image_singleton, hf.isClosed_iff_image_isClosed]

lemma closedPoints_eq_univ [T1Space X] :
    closedPoints X = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun _ ↦ isClosed_singleton

end closedPoints

/-- The class of Jacobson spaces, i.e.
spaces such that the set of closed points are dense in every closed subspace. -/
@[mk_iff, stacks 005U]
class JacobsonSpace : Prop where
  closure_inter_closedPoints : ∀ {Z}, IsClosed Z → closure (Z ∩ closedPoints X) = Z

export JacobsonSpace (closure_inter_closedPoints)

variable {X}

lemma closure_closedPoints [JacobsonSpace X] : closure (closedPoints X) = Set.univ := by
  simpa using closure_inter_closedPoints isClosed_univ

lemma jacobsonSpace_iff_locallyClosed :
    JacobsonSpace X ↔ ∀ Z, Z.Nonempty → IsLocallyClosed Z → (Z ∩ closedPoints X).Nonempty := by
  rw [jacobsonSpace_iff]
  constructor
  · simp_rw [isLocallyClosed_iff_isOpen_coborder, coborder, isOpen_compl_iff,
      Set.nonempty_iff_ne_empty]
    intro H Z hZ hZ' e
    have : Z ⊆ closure Z \ Z := by
      refine subset_closure.trans ?_
      nth_rw 1 [← H isClosed_closure]
      rw [hZ'.closure_subset_iff, Set.subset_diff, Set.disjoint_iff, Set.inter_assoc,
        Set.inter_comm _ Z, e]
      exact ⟨Set.inter_subset_left, Set.inter_subset_right⟩
    rw [Set.subset_diff, disjoint_self, Set.bot_eq_empty] at this
    exact hZ this.2
  · intro H Z hZ
    refine subset_antisymm (hZ.closure_subset_iff.mpr Set.inter_subset_left) ?_
    rw [← Set.disjoint_compl_left_iff_subset, Set.disjoint_iff_inter_eq_empty,
      ← Set.not_nonempty_iff_eq_empty]
    intro H'
    have := H _ H' (isClosed_closure.isOpen_compl.isLocallyClosed.inter hZ.isLocallyClosed)
    rw [Set.nonempty_iff_ne_empty, Set.inter_assoc, ne_eq,
      ← Set.disjoint_iff_inter_eq_empty, Set.disjoint_compl_left_iff_subset] at this
    exact this subset_closure

lemma nonempty_inter_closedPoints [JacobsonSpace X] {Z : Set X}
    (hZ : Z.Nonempty) (hZ' : IsLocallyClosed Z) : (Z ∩ closedPoints X).Nonempty :=
  jacobsonSpace_iff_locallyClosed.mp inferInstance Z hZ hZ'

lemma isClosed_singleton_of_isLocallyClosed_singleton [JacobsonSpace X] {x : X}
    (hx : IsLocallyClosed {x}) : IsClosed {x} := by
  obtain ⟨_, ⟨y, rfl : y = x, rfl⟩, hy'⟩ :=
    nonempty_inter_closedPoints (Set.singleton_nonempty x) hx
  exact hy'

lemma Topology.IsOpenEmbedding.preimage_closedPoints (hf : IsOpenEmbedding f) [JacobsonSpace Y] :
    f ⁻¹' closedPoints Y = closedPoints X := by
  apply subset_antisymm (preimage_closedPoints_subset hf.injective hf.continuous)
  intro x hx
  apply isClosed_singleton_of_isLocallyClosed_singleton
  rw [← Set.image_singleton]
  exact (hx.isLocallyClosed.image hf.isInducing hf.isOpen_range.isLocallyClosed)

lemma JacobsonSpace.of_isOpenEmbedding [JacobsonSpace Y] (hf : IsOpenEmbedding f) :
    JacobsonSpace X := by
  rw [jacobsonSpace_iff_locallyClosed, ← hf.preimage_closedPoints]
  intro Z hZ hZ'
  obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := nonempty_inter_closedPoints
    (hZ.image f) (hZ'.image hf.isInducing hf.isOpen_range.isLocallyClosed)
  exact ⟨_, hx, hx'⟩

lemma JacobsonSpace.of_isClosedEmbedding [JacobsonSpace Y] (hf : IsClosedEmbedding f) :
    JacobsonSpace X := by
  rw [jacobsonSpace_iff_locallyClosed, ← hf.preimage_closedPoints]
  intro Z hZ hZ'
  obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := nonempty_inter_closedPoints
    (hZ.image f) (hZ'.image hf.isInducing hf.isClosed_range.isLocallyClosed)
  exact ⟨_, hx, hx'⟩

lemma JacobsonSpace.discreteTopology [JacobsonSpace X]
    (h : (closedPoints X).Finite) : DiscreteTopology X := by
  have : closedPoints X = Set.univ := by
    rw [← Set.univ_subset_iff, ← closure_closedPoints,
      closure_subset_iff_isClosed, ← (closedPoints X).biUnion_of_singleton]
    exact h.isClosed_biUnion fun _ ↦ id
  have inst : Finite X := Set.finite_univ_iff.mp (this ▸ h)
  rw [discreteTopology_iff_forall_isOpen]
  intro s
  rw [← isClosed_compl_iff, ← sᶜ.biUnion_of_singleton]
  refine sᶜ.toFinite.isClosed_biUnion fun x _ ↦ ?_
  rw [← mem_closedPoints_iff, this]
  trivial

instance (priority := 100) [Finite X] [JacobsonSpace X] : DiscreteTopology X :=
  JacobsonSpace.discreteTopology (Set.toFinite _)

instance (priority := 100) [T1Space X] : JacobsonSpace X :=
  ⟨by simp [closedPoints_eq_univ, closure_eq_iff_isClosed]⟩

lemma TopologicalSpace.IsOpenCover.jacobsonSpace_iff {ι : Type*} {U : ι → Opens X}
    (hU : IsOpenCover U) : JacobsonSpace X ↔ ∀ i, JacobsonSpace (U i) := by
  refine ⟨fun H i ↦ .of_isOpenEmbedding (U i).2.isOpenEmbedding_subtypeVal, fun H ↦ ?_⟩
  rw [jacobsonSpace_iff_locallyClosed]
  intro Z hZ hZ'
  rw [← hU.iUnion_inter Z, Set.nonempty_iUnion] at hZ
  obtain ⟨i, x, hx, hx'⟩ := hZ
  obtain ⟨y, hy, hy'⟩ := (jacobsonSpace_iff_locallyClosed.mp (H i)) _ ⟨⟨x, hx'⟩, hx⟩
    (hZ'.preimage continuous_subtype_val)
  refine ⟨y, hy, hU.isClosed_iff_coe_preimage.mpr fun j ↦ ?_⟩
  by_cases h : (y : X) ∈ U j
  · convert_to IsClosed {(⟨y, h⟩ : U j)}
    · ext; simp [← Subtype.coe_inj]
    apply isClosed_singleton_of_isLocallyClosed_singleton
    convert (hy'.isLocallyClosed.image IsEmbedding.subtypeVal.isInducing
      (U i).2.isOpenEmbedding_subtypeVal.isOpen_range.isLocallyClosed).preimage
      continuous_subtype_val
    ext
    simp [← Subtype.coe_inj]
  · convert isClosed_empty
    rw [Set.eq_empty_iff_forall_notMem]
    intro z (hz : z.1 = y.1)
    exact h (hz ▸ z.2)
