/-
Copyright (c) 2025 Daniel Figueroa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Figueroa
-/
module

public import Mathlib.Dynamics.Minimal
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.Closure
import Mathlib.Topology.Continuous

/-!
# Topologically transitive monoid actions

In this file we define an action of a monoid `M` on a topological space `α` to be
*topologically transitive* if for any pair of nonempty open sets `U` and `V` in `α` there exists an
`m : M` such that `(m • U) ∩ V` is nonempty. We also provide an additive version of this definition
and prove basic facts about topologically transitive actions.

## Tags

group action, topologically transitive
-/

@[expose] public section


open scoped Pointwise

/-- An action of an additive monoid `M` on a topological space `α` is called
*topologically transitive* if for any pair of nonempty open sets `U` and `V` in `α` there exists an
`m : M` such that `(m +ᵥ U) ∩ V` is nonempty. -/
class AddAction.IsTopologicallyTransitive (M α : Type*) [AddMonoid M] [TopologicalSpace α]
    [AddAction M α] : Prop where
  exists_vadd_inter : ∀ {U V : Set α}, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
    ∃ m : M, ((m +ᵥ U) ∩ V).Nonempty

/-- An action of a monoid `M` on a topological space `α` is called *topologically transitive* if for
any pair of nonempty open sets `U` and `V` in `α` there exists an `m : M` such that `(m • U) ∩ V` is
nonempty. -/
@[to_additive]
class MulAction.IsTopologicallyTransitive (M α : Type*) [Monoid M] [TopologicalSpace α]
    [MulAction M α] : Prop where
  exists_smul_inter : ∀ {U V : Set α}, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
    ∃ m : M, ((m • U) ∩ V).Nonempty

open MulAction Set

variable (M : Type*) {α : Type*} [TopologicalSpace α] [Monoid M] [MulAction M α]

section IsTopologicallyTransitive

@[to_additive]
theorem MulAction.isTopologicallyTransitive_iff :
    IsTopologicallyTransitive M α ↔ ∀ {U V : Set α}, IsOpen U → U.Nonempty → IsOpen V →
    V.Nonempty → ∃ m : M, ((m • U) ∩ V).Nonempty := ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

/-- An action of a monoid `M` on `α` is topologically transitive if and only if for any nonempty
open subset `U` of `α` the union over the elements of `M` of images of `U` is dense in `α`. -/
@[to_additive /-- An action of an additive monoid `M` on `α` is topologically transitive if and only
if for any nonempty open subset `U` of `α` the union over the elements of `M` of images of `U` is
dense in `α`. -/]
theorem MulAction.isTopologicallyTransitive_iff_dense_iUnion :
    IsTopologicallyTransitive M α ↔
    ∀ {U : Set α}, IsOpen U → U.Nonempty → Dense (⋃ m : M, m • U) := by
  simp only [isTopologicallyTransitive_iff, inter_comm, dense_iff_inter_open, inter_iUnion,
    nonempty_iUnion]
  exact ⟨fun h _ h₁ h₂ _ h₃ h₄ ↦ h h₁ h₂ h₃ h₄, fun h _ _ h₁ h₂ h₃ h₄ ↦ h h₁ h₂ _ h₃ h₄⟩

/-- An action of a monoid `M` on `α` is topologically transitive if and only if for any nonempty
open subset `U` of `α` the union of the preimages of `U` over the elements of `M` is dense in `α`.
-/
@[to_additive /-- An action of an additive monoid `M` on `α` is topologically transitive if and only
if for any nonempty open subset `U` of `α` the union of the preimages of `U` over the elements of
`M` is dense in `α`. -/]
theorem MulAction.isTopologicallyTransitive_iff_dense_iUnion_preimage :
    IsTopologicallyTransitive M α ↔
    ∀ {U : Set α}, IsOpen U → U.Nonempty → Dense (⋃ m : M, (m • ·) ⁻¹' U) := by
  simp only [dense_iff_inter_open, inter_iUnion, nonempty_iUnion, ← image_inter_nonempty_iff]
  exact ⟨fun h _ h₁ h₂ _ h₃ h₄ ↦ h.1 h₃ h₄ h₁ h₂, fun h ↦ ⟨fun h₁ h₂ h₃ h₄ ↦ h h₃ h₄ _ h₁ h₂⟩⟩

@[to_additive]
theorem IsOpen.dense_iUnion_smul [h : IsTopologicallyTransitive M α] {U : Set α}
    (hUo : IsOpen U) (hUne : U.Nonempty) : Dense (⋃ m : M, m • U) :=
  (isTopologicallyTransitive_iff_dense_iUnion M).mp h hUo hUne

@[to_additive]
theorem IsOpen.dense_iUnion_preimage_smul [h : IsTopologicallyTransitive M α]
    {U : Set α} (hUo : IsOpen U) (hUne : U.Nonempty) : Dense (⋃ m : M, (m • ·) ⁻¹' U) :=
  (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mp h hUo hUne

/-- Let `M` be a monoid with a topologically transitive action on `α`. If `U` is a nonempty open
subset of `α` and `(m • ·) ⁻¹' U ⊆ U` for all `m : M` then `U` is dense in `α`. -/
@[to_additive /-- Let `M` be an additive monoid with a topologically transitive action on `α`. If
`U` is a nonempty open subset of `α` and `(m +ᵥ ·) ⁻¹' U ⊆ U` for all `m : M` then `U` is dense in
`α`. -/]
theorem IsOpen.dense_of_preimage_smul_invariant [IsTopologicallyTransitive M α] {U : Set α}
    (hUo : IsOpen U) (hUne : U.Nonempty) (hUinv : ∀ m : M, (m • ·) ⁻¹' U ⊆ U) : Dense U :=
  .mono (by simpa only [iUnion_subset_iff]) (hUo.dense_iUnion_preimage_smul M hUne)

/-- An action of a monoid `M` on `α` that is continuous in the second argument is topologically
transitive if and only if any nonempty open subset `U` of `α` with `(m • ·) ⁻¹' U ⊆ U` for all
`m : M` is dense in `α`. -/
@[to_additive /-- An action of an additive monoid `M` on `α` that is continuous in the second
argument is topologically transitive if and only if any nonempty open subset `U` of `α` with
`(m +ᵥ ·) ⁻¹' U ⊆ U` for all `m : M` is dense in `α`. -/]
theorem MulAction.isTopologicallyTransitive_iff_dense_of_preimage_invariant
    [h : ContinuousConstSMul M α] : IsTopologicallyTransitive M α ↔
    ∀ {U : Set α}, IsOpen U → U.Nonempty → (∀ m : M, (m • ·) ⁻¹' U ⊆ U) → Dense U := by
  refine ⟨fun _ _ h₀ h₁ h₂ ↦ h₀.dense_of_preimage_smul_invariant M h₁ h₂, fun h₄ ↦ ?_⟩
  refine (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mpr ?_
  refine fun hU _ ↦ h₄ (isOpen_iUnion fun a ↦ hU.preimage (h.1 a)) ?_ fun b _ ↦ ?_
  · exact nonempty_iUnion.mpr ⟨1, by simpa only [one_smul]⟩
  · simp only [preimage_iUnion, mem_iUnion, mem_preimage, smul_smul, forall_exists_index]
    exact fun c hc ↦ ⟨c * b, hc⟩

@[to_additive]
instance MulAction.isTopologicallyTransitive_of_isMinimal [IsMinimal M α] :
    IsTopologicallyTransitive M α := by
  refine (isTopologicallyTransitive_iff_dense_iUnion_preimage M).mpr fun h hn ↦ ?_
  simp only [h.iUnion_preimage_smul M hn, dense_univ]

end IsTopologicallyTransitive
