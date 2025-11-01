/-
Copyright (c) 2025 Daniel Figueroa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Figueroa
-/
import Mathlib.Dynamics.Minimal
import Mathlib.Topology.Baire.Lemmas

/-!
# Topologically transitive and point transitive actions of monoids

In this file we define an action of a monoid `M` on a topological space `α` to be
*point transitive* if there exists a point in `α` with dense `M`-orbit and we define the set of
*transitive points* to be the points for which the orbit under `M` is dense. We define an action to
be *topologically transitive* if for any pair of nonempty open sets `U` and `V` in `α` there exists
an `m : M` such that `(m • U) ∩ V` is nonempty. We also provide additive versions of point
transitive and topologically transitive actions and prove basic facts about the multiplicative and
additive versions.

## Tags

group action, transitive points, point transitive, topologically transitive
-/


open scoped Pointwise

/-- An action of an additive monoid `M` on a topological space is called *point transitive* if
there exists a point `x : α` with dense `M`-orbit. -/
class AddAction.IsPointTransitive (M α : Type*) [AddMonoid M] [TopologicalSpace α] [AddAction M α] :
    Prop where
  exists_dense_orbit : ∃ x : α, Dense (orbit M x)

/-- An action of a monoid `M` on a topological space is called *point transitive* if there exists a
point `x : α` with dense `M`-orbit. -/
@[to_additive]
class MulAction.IsPointTransitive (M α : Type*) [Monoid M] [TopologicalSpace α] [MulAction M α] :
    Prop where
  exists_dense_orbit : ∃ x : α, Dense (orbit M x)

/-- Given an action of a monoid on a topological space `α`, a point `x` is said to be *transitive*
if the orbit of `x` under `M` is dense in `α`. -/
@[to_additive /-- Given an action of an additive monoid on a topological space `α`, a point `x` is
said to be *transitive* if the orbit of `x` under `M` is dense in `α`. -/]
def MulAction.transitivePoints (M α : Type*) [Monoid M] [TopologicalSpace α] [MulAction M α] :
    Set α := {x : α | Dense (orbit M x)}

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

variable (M G : Type*) {α : Type*} [TopologicalSpace α] [Monoid M] [Group G] [MulAction M α]
  [MulAction G α]

section IsPointTransitive

@[to_additive]
theorem MulAction.isPointTransitive_iff_transitivePoints_nonempty :
    IsPointTransitive M α ↔ (transitivePoints M α).Nonempty :=
  ⟨fun ⟨x , hx⟩ ↦ ⟨x, hx⟩, fun ⟨x, hx⟩ ↦ ⟨x, hx⟩⟩

@[to_additive]
theorem MulAction.preimage_smul_transitivePoints_subset (m : M) :
    (m • ·) ⁻¹' transitivePoints M α ⊆ transitivePoints M α := fun _ ↦ .mono (orbit_smul_subset ..)

@[to_additive]
theorem MulAction.mem_transitivePoints_of_smul {m : M} {x : α} (h : m • x ∈ transitivePoints M α) :
    x ∈ transitivePoints M α := preimage_subset_iff.1 (preimage_smul_transitivePoints_subset ..) x h

@[to_additive]
theorem MulAction.mem_transitivePoints_of_isMinimal [IsMinimal M α] (x : α) :
    x ∈ transitivePoints M α := dense_orbit M x

@[to_additive]
theorem MulAction.isMinimal_iff_transitivePoints_eq_univ :
    IsMinimal M α ↔ transitivePoints M α = univ :=
  .trans ⟨fun _ ↦ dense_orbit M, fun h ↦ ⟨h⟩⟩ eq_univ_iff_forall.symm

@[to_additive]
theorem MulAction.smul_transitivePoints_eq (g : G) :
    g • transitivePoints G α = transitivePoints G α := by
  refine Set.ext fun x ↦ ⟨fun ⟨y, _, _⟩ ↦ by simp_all [transitivePoints, ← orbit_smul g y], ?_⟩
  exact fun _ ↦ mem_smul_set.2 ⟨g⁻¹ • x, by simpa [transitivePoints]⟩

@[to_additive]
theorem MulAction.denseRange_smul_of_mem_transitivePoints {x : α} (hx : x ∈ transitivePoints M α) :
    DenseRange fun m : M ↦ m • x := hx

@[to_additive]
instance MulAction.isPointTransitive_of_isMinimal [IsMinimal M α] [h : Nonempty α] :
    IsPointTransitive M α :=
  (isPointTransitive_iff_transitivePoints_nonempty M).2 (h.elim fun x ↦ ⟨x, dense_orbit M x⟩)

@[to_additive]
theorem IsOpen.exists_smul_mem_of_mem_transitivePoints {x : α} (hx : x ∈ transitivePoints M α)
    {U : Set α} (hUo : IsOpen U) (hUne : U.Nonempty) : ∃ m : M, m • x ∈ U :=
  (denseRange_smul_of_mem_transitivePoints M hx).exists_mem_open hUo hUne

@[to_additive]
theorem dense_of_smul_invariant {s : Set α} (hsmul : ∀ m : M, m • s ⊆ s)
    (hs : (s ∩ transitivePoints M α).Nonempty) : Dense s :=
  hs.elim fun x h ↦ h.elim fun h₁ h₂ ↦ .mono (range_subset_iff.2 fun _ ↦ hsmul _ ⟨x, h₁, rfl⟩) h₂

@[to_additive]
theorem IsClosed.eq_univ_of_smul_invariant {s : Set α} (hc : IsClosed s)
    (hsmul : ∀ m : M, m • s ⊆ s) (hs : (s ∩ transitivePoints M α).Nonempty) : s = univ :=
  hc.closure_eq ▸ (dense_of_smul_invariant M hsmul hs).closure_eq

end IsPointTransitive

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

/-- If `α` is a nonempty Baire space with a second-countable topology, then any topologically
transitive action of a monoid on `α` that is continuous in the second argument is point transitive.
-/
@[to_additive /-- If `α` is a nonempty Baire space with a second-countable topology, then any
topologically transitive action of an additive monoid on `α` that is continuous in the second
argument is point transitive. -/]
theorem MulAction.IsTopologicallyTransitive.isPointTransitive [Nonempty α] [BaireSpace α]
    [SecondCountableTopology α] [hc : ContinuousConstSMul M α] [IsTopologicallyTransitive M α] :
    IsPointTransitive M α := by
  refine ⟨match TopologicalSpace.exists_countable_basis α with | ⟨b, h₁, h₂, h₃⟩ => ?_⟩
  suffices hd : Dense (⋂ s ∈ b, ⋃ m, (m • ·) ⁻¹' s) by
    rcases Dense.nonempty (X := α) hd with ⟨y, hy⟩
    simp only [mem_iInter, mem_iUnion, mem_preimage, h₃.dense_iff, inter_nonempty] at hy ⊢
    exact ⟨y, fun _ h _ ↦ match hy _ h with | ⟨z, hd⟩ => ⟨z • y, hd, mem_orbit y z⟩⟩
  refine dense_biInter_of_isOpen ?_ h₁ fun s hs ↦ (h₃.isOpen hs).dense_iUnion_preimage_smul M ?_
  · exact fun V ↦ fun hV ↦ isOpen_iUnion fun m ↦ by simp only [(h₃.isOpen hV).preimage (hc.1 m)]
  · exact s.nonempty_iff_ne_empty.2 (ne_of_mem_of_not_mem hs h₂)

/-- A point transitive action of a group is topologically transitive -/
@[to_additive /-- A point transitive action of an additive group is topologically transitive -/]
instance MulAction.isTopologicallyTransitive_of_isPointTransitive [h : IsPointTransitive G α] :
    IsTopologicallyTransitive G α := by
  refine ⟨match h.exists_dense_orbit with | ⟨x, hx⟩ => fun ho hne hVo hVne ↦ ?_⟩
  simp only [dense_iff_inter_open, inter_nonempty, mem_smul_set, exists_exists_and_eq_and] at hx ⊢
  obtain ⟨⟨y, hy, a, ha⟩, ⟨_, _, b, hb⟩⟩ := And.intro (hx _ ho hne) (hx _ hVo hVne)
  exact ⟨b • a⁻¹, y, ⟨hy, by simpa only [← ha, smul_assoc, inv_smul_smul, hb]⟩⟩
