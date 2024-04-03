/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Topology.Order.LowerUpperTopology
import Mathlib.Topology.Order.ScottTopology

/-!
# Lawson topology

This file introduces the Lawson topology on a preorder.

## Main definitions

- `LawsonTopology'` - the Lawson topology is defined as the meet of the `LowerTopology` and the
  `ScottTopology`.

## Main statements

## Implementation notes

A type synonym `WithLawsonTopology` is introduced and for a preorder `α`, `WithLawsonTopology α`
is made an instance of `topological_space` by the `LawsonTopology'`.

We define a mixin class `LawsonTopology` for the class of types which are both a preorder and a
topology and where the topology is the `LawsonTopology'`.
It is shown that `WithLawsonTopology α` is an instance of `LawsonTopology`.

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]

## Tags
Lawson topology, preorder
-/

open Set

open TopologicalSpace

variable {α β : Type*}

namespace Topology

/-! ### Lawson topology -/

section Lawson
section Preorder

/--
The Lawson topology is defined as the meet of the `LowerTopology` and the `ScottTopology`.
-/
def lawson (α : Type*) [Preorder α] : TopologicalSpace α := lower α ⊓ scott α

variable (α) [Preorder α] [TopologicalSpace α]

/-- Predicate for an ordered topological space to be equipped with its Lawson topology.

The Lawson topology is defined as the meet of the `LowerTopology` and the `ScottTopology`.
-/
class IsLawson : Prop where
  topology_eq_lawson : ‹TopologicalSpace α› = lawson α

end Preorder

namespace IsLawson
section Preorder
variable (α) [Preorder α] [TopologicalSpace α] [IsLawson α]

lemma topology_eq : ‹_› = lawson α := topology_eq_lawson

/-- The complements of the upper closures of finite sets intersected with Scott open sets form
a basis for the lawson topology. -/
def lawsonBasis (α : Type*) [Preorder α] :=
  { s : Set α | ∃ u : Set α, IsOpen[scott α] u ∧ ∃ t : Set α, t.Finite ∧
    u ∩ (upperClosure t : Set α)ᶜ = s }

open TopologicalSpace

/-- The complements of the upper closures of finite sets intersected with Scott open sets form
a basis for the lawson topology. -/
def lawson_basis := { s : Set α | ∃ t : Set α, t.Finite ∧ ∃ u : Set α, IsOpen[scott α] u ∧
      (upperClosure t : Set α)ᶜ ∩ u = s }

protected theorem isTopologicalBasis : TopologicalSpace.IsTopologicalBasis (lawson_basis α) := by
  have lawson_basis_image2 : lawson_basis α =
      (image2 (fun x x_1 ↦ ⇑WithLower.toLower ⁻¹' x ∩ ⇑WithScott.toScott ⁻¹' x_1)
        (IsLower.lowerBasis (WithLower α)) {U | @IsOpen (WithScott α) _ U}) := by
    rw [lawson_basis, image2, IsLower.lowerBasis]
    aesop
  rw [lawson_basis_image2]
  convert IsTopologicalBasis.inf_induced IsLower.isTopologicalBasis
    (TopologicalSpace.isTopologicalBasis_opens (α := WithScott α))
    WithLower.toLower WithScott.toScott
  erw [topology_eq α]
  rw [lawson]
  apply (congrArg₂ Inf.inf _) _
  letI _ := lower α; exact @IsLower.withLowerHomeomorph α ‹_› (lower α) ⟨rfl⟩ |>.inducing.induced
  letI _ := scott α; exact @IsScott.withScottHomeomorph α _ (scott α) ⟨rfl⟩ |>.inducing.induced

end Preorder
end IsLawson

/--
Type synonym for a preorder equipped with the Lawson topology
-/
def WithLawson (α : Type*) := α

namespace WithLawson

/-- `toLawson` is the identity function to the `WithLawson` of a type.  -/
@[match_pattern] def toLawson : α ≃ WithLawson α := Equiv.refl _

/-- `ofLawson` is the identity function from the `WithLawson` of a type.  -/
@[match_pattern] def ofLawson : WithLawson α ≃ α := Equiv.refl _

@[simp] lemma to_Lawson_symm_eq : (@toLawson α).symm = ofLawson := rfl
@[simp] lemma of_Lawson_symm_eq : (@ofLawson α).symm = toLawson := rfl
@[simp] lemma toLawson_ofLawson (a : WithLawson α) : toLawson (ofLawson a) = a := rfl
@[simp] lemma ofLawson_toLawson (a : α) : ofLawson (toLawson a) = a := rfl

@[simp, nolint simpNF]
lemma toLawson_inj {a b : α} : toLawson a = toLawson b ↔ a = b := Iff.rfl

@[simp, nolint simpNF]
lemma ofLawson_inj {a b : WithLawson α} : ofLawson a = ofLawson b ↔ a = b :=
Iff.rfl

/-- A recursor for `WithLawson`. Use as `induction x using WithLawson.rec`. -/
protected def rec {β : WithLawson α → Sort _}
    (h : ∀ a, β (toLawson a)) : ∀ a, β a := fun a => h (ofLawson a)

instance [Nonempty α] : Nonempty (WithLawson α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithLawson α) := ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithLawson α) := ‹Preorder α›
instance : TopologicalSpace (WithLawson α) := lawson α
instance : IsLawson (WithLawson α) := ⟨rfl⟩

/-- If `α` is equipped with the Lawson topology, then it is homeomorphic to `WithLawson α`.
-/
def withLawsonTopologyHomeomorph [TopologicalSpace α] [IsLawson α]  : WithLawson α ≃ₜ α :=
  WithLawson.ofLawson.toHomeomorphOfInducing ⟨by erw [IsLawson.topology_eq α, induced_id]; rfl⟩

theorem isOpen_preimage_ofLawson (S : Set α) :
    IsOpen (Topology.WithLawson.ofLawson ⁻¹' S) ↔
      (lawson α).IsOpen S :=
  Iff.rfl

theorem isClosed_preimage_ofLawson (S : Set α) :
    IsClosed (Topology.WithLawson.ofLawson ⁻¹' S) ↔
      @IsClosed (WithLawson α) _ S :=
  Iff.rfl

theorem isOpen_def (T : Set (Topology.WithLawson α)) :
    IsOpen T ↔
      (lawson α).IsOpen (Topology.WithLawson.toLawson ⁻¹' T) :=
  Iff.rfl

end WithLawson
end Lawson


namespace IsLawson

section preorder

variable [Preorder α] [TopologicalSpace α] [Topology.IsLawson α]

theorem isClosed_preimage_ofLawson (S : Set α) :
    IsClosed (Topology.WithLawson.ofLawson ⁻¹' S) ↔ IsClosed S := by
  rw [WithLawson.isClosed_preimage_ofLawson]
  simp only [IsLawson.topology_eq]

end preorder

end IsLawson

section ts

variable [Preorder α]

lemma Lawson_le_Scott' : lawson α ≤ scott α := inf_le_right

lemma Lawson_le_Lower' : lawson α ≤ lower α := inf_le_left

lemma Scott_Hausdorff_le_Lawson' : scottHausdorff α  ≤ lawson α := by
  rw [lawson, le_inf_iff]
  exact ⟨@Scott_Hausdorff_le_Lower' α _, @scottHausdorff_le_scott α _⟩

lemma LawsonOpen_implies_ScottHausdorffOpen''' (s : Set α) :
    IsOpen (Topology.WithLawson.ofLawson ⁻¹' s) → (scottHausdorff α).IsOpen s :=
  Scott_Hausdorff_le_Lawson' _

lemma ScottOpen_implies_LawsonOpen (s : Set α) :
    IsOpen (Topology.WithScott.ofScott ⁻¹' s) → IsOpen (Topology.WithLawson.ofLawson ⁻¹' s) :=
  Lawson_le_Scott' _

lemma ScottClosed_implies_LawsonClosed (s : Set α) :
    IsClosed (Topology.WithScott.ofScott ⁻¹' s) →
    IsClosed (Topology.WithLawson.ofLawson ⁻¹' s) := by
  rw [← isOpen_compl_iff, ← isOpen_compl_iff]
  exact Lawson_le_Scott' _

lemma LowerClosed_implies_LawsonClosed (s : Set α) :
    IsClosed (Topology.WithLower.ofLower ⁻¹' s) →
    IsClosed (Topology.WithLawson.ofLawson ⁻¹' s) := by
  rw [← isOpen_compl_iff, ← isOpen_compl_iff]
  exact Lawson_le_Lower' _

end ts


section csh

variable [Preorder α] [TopologicalSpace α] [Topology.IsScott α] (s : Set α)

lemma ScottLawsonCont' [Preorder α] :
    Continuous (WithScott.toScott ∘ WithLawson.ofLawson : WithLawson α → _) := by
  rw [continuous_def]
  intro s hs
  apply ScottOpen_implies_LawsonOpen _ hs

/-- An upper set is Lawson open if and only if it is Scott open -/
lemma LawsonOpen_iff_ScottOpen' [Preorder α] (s : Set α) (h : IsUpperSet s) :
    IsOpen (Topology.WithScott.ofScott ⁻¹' s) ↔ IsOpen (Topology.WithLawson.ofLawson ⁻¹' s) := by
  constructor
  · exact ScottOpen_implies_LawsonOpen _
  · intro hs
    rw [Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open]
    exact ⟨h, LawsonOpen_implies_ScottHausdorffOpen''' _ hs⟩

variable (L : TopologicalSpace α) (l : TopologicalSpace α) (S : TopologicalSpace α)
variable [Preorder α] [@Topology.IsLawson α _ L] [@Topology.IsLower α l _] [@Topology.IsScott α _ S]

lemma Scott_le_Lawson : L ≤ S := by
  rw [@Topology.IsScott.topology_eq α _ S _, @Topology.IsLawson.topology_eq α _ L _]
  exact inf_le_right

lemma Scott_Hausdorff_le_Lawson : (scottHausdorff α) ≤ L := by
  rw [@Topology.IsLawson.topology_eq α _ L _,  lawson, le_inf_iff,
    ← @Topology.IsLower.topology_eq α _ l _, ← @Topology.IsScott.topology_eq α _ S _]
  constructor
  · exact @IsLower.scottHausdorff_le  α _ l _
  · convert scottHausdorff_le_scott
    exact IsScott.topology_eq_scott

open Topology

lemma LawsonOpen_implies_ScottHausdorffOpen : IsOpen[L] ≤ IsOpen[scottHausdorff α] :=
  (@Scott_Hausdorff_le_Lawson _ L l _ _ _ _ _)

lemma LawsonOpen_implies_ScottHausdorffOpen' (s : Set α) :
    IsOpen[L] s → IsOpen[scottHausdorff α] s := by
  apply (@LawsonOpen_implies_ScottHausdorffOpen _ _ l _ _)

end csh


section Preorder

open Topology

variable [Preorder α]
  (S :TopologicalSpace α) (l : TopologicalSpace α) (L : TopologicalSpace α)
  [@IsScott α _ S]  [@IsLawson α _ L] [@IsLower α l _]

/-- An upper set is Lawson open if and only if it is Scott open -/
lemma lawsonOpen_iff_scottOpen_of_isUpperSet (s : Set α) (h : IsUpperSet s) :
    IsOpen[L] s ↔ IsOpen[S] s := by
  constructor
  · intro hs
    rw [@Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open α _ S]
    exact ⟨h, fun d d₁ d₂ => (@LawsonOpen_implies_ScottHausdorffOpen' _ _ l S _ _ _ _ s) hs d₁ d₂⟩
  · apply TopologicalSpace.le_def.mp (Scott_le_Lawson _ _)

lemma lawsonClosed_iff_scottClosed_of_isLowerSet (s : Set α) (h : IsLowerSet s) :
    IsClosed[L] s ↔ IsClosed[S] s := by
    rw [← isUpperSet_compl] at h
    rw [← isOpen_compl_iff, ← @isOpen_compl_iff,
      (lawsonOpen_iff_scottOpen_of_isUpperSet S l L _ h)]

/-- A lower set is Lawson closed if and only if it is closed under sups of directed sets -/
lemma lawsonClosed_iff_dirSupClosed_of_isLowerSet (s : Set α) (h : IsLowerSet s) :
    IsClosed[L] s ↔ DirSupClosed s := by
  rw [(lawsonClosed_iff_scottClosed_of_isLowerSet S l L _ h),
    @Topology.IsScott.isClosed_iff_isLowerSet_and_dirSupClosed]
  aesop

end Preorder

namespace IsLawson

section PartialOrder

variable [PartialOrder α] [TopologicalSpace α] [IsLawson α]

lemma singletonIsClosed (a : α) : IsClosed ({a} : Set α) := by
  rw [← (Set.OrdConnected.upperClosure_inter_lowerClosure ordConnected_singleton),
    ← isClosed_preimage_ofLawson]
  apply IsClosed.inter
    (LowerClosed_implies_LawsonClosed _ (IsLower.isClosed_upperClosure (finite_singleton a)))
  rw [← isClosed_preimage_ofLawson, lowerClosure_singleton, LowerSet.coe_Iic]
  apply ScottClosed_implies_LawsonClosed
  exact Topology.IsScott.isClosed_Iic

-- see Note [lower instance priority]
/-- The Lawson topology on a partial order is T₀. -/
instance (priority := 90) t0Space : T0Space α :=
  (t0Space_iff_inseparable α).2 fun a b h => by
    simpa only [inseparable_iff_closure_eq, closure_eq_iff_isClosed.mpr (singletonIsClosed a),
      closure_eq_iff_isClosed.mpr (singletonIsClosed b), singleton_eq_singleton_iff] using h

end PartialOrder

end IsLawson
