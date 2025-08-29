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

- `Topology.lawson` - the Lawson topology is defined as the meet of the lower topology and the
  Scott topology.
- `Topology.IsLawson.lawsonBasis` - The complements of the upper closures of finite sets
  intersected with Scott open sets.

## Main statements

- `Topology.IsLawson.isTopologicalBasis` - `Topology.IsLawson.lawsonBasis` is a basis for
  `Topology.IsLawson`
- `Topology.lawsonOpen_iff_scottOpen_of_isUpperSet'` - An upper set is Lawson open if and only if it
  is Scott open
- `Topology.lawsonClosed_iff_dirSupClosed_of_isLowerSet` - A lower set is Lawson closed if and only
  if it is closed under sups of directed sets
- `Topology.IsLawson.t0Space` - The Lawson topology is T₀

## Implementation notes

A type synonym `Topology.WithLawson` is introduced and for a preorder `α`, `Topology.WithLawson α`
is made an instance of `TopologicalSpace` by `Topology.lawson`.

We define a mixin class `Topology.IsLawson` for the class of types which are both a preorder and a
topology and where the topology is `Topology.lawson`.
It is shown that `Topology.WithLawson α` is an instance of `Topology.IsLawson`.

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]

## Tags

Lawson topology, preorder
-/

open Set TopologicalSpace

variable {α : Type*}

namespace Topology

/-! ### Lawson topology -/

section Lawson
section Preorder

/--
The Lawson topology is defined as the meet of `Topology.lower` and the `Topology.scott`.
-/
def lawson (α : Type*) [Preorder α] : TopologicalSpace α := lower α ⊓ scott α univ

variable (α) [Preorder α] [TopologicalSpace α]

/-- Predicate for an ordered topological space to be equipped with its Lawson topology.

The Lawson topology is defined as the meet of `Topology.lower` and the `Topology.scott`.
-/
class IsLawson : Prop where
  topology_eq_lawson : ‹TopologicalSpace α› = lawson α

end Preorder

namespace IsLawson
section Preorder
variable (α) [Preorder α] [TopologicalSpace α] [IsLawson α]

/-- The complements of the upper closures of finite sets intersected with Scott open sets form
a basis for the lawson topology. -/
def lawsonBasis := { s : Set α | ∃ t : Set α, t.Finite ∧ ∃ u : Set α, IsOpen[scott α univ] u ∧
      u \ upperClosure t = s }

protected theorem isTopologicalBasis : TopologicalSpace.IsTopologicalBasis (lawsonBasis α) := by
  have lawsonBasis_image2 : lawsonBasis α =
      (image2 (fun x x_1 ↦ ⇑WithLower.toLower ⁻¹' x ∩ ⇑WithScott.toScott ⁻¹' x_1)
        (IsLower.lowerBasis (WithLower α)) {U | IsOpen[scott α univ] U}) := by
    rw [lawsonBasis, image2, IsLower.lowerBasis]
    simp_rw [diff_eq_compl_inter]
    aesop
  rw [lawsonBasis_image2]
  convert IsTopologicalBasis.inf_induced IsLower.isTopologicalBasis
    (isTopologicalBasis_opens (α := WithScott α))
    WithLower.toLower WithScott.toScott
  rw [@topology_eq_lawson α _ _ _, lawson]
  apply (congrArg₂ min _) _
  · letI _ := lower α
    exact (@IsLower.withLowerHomeomorph α ‹_› (lower α) ⟨rfl⟩).isInducing.eq_induced
  · letI _ := scott α univ
    exact (@IsScott.withScottHomeomorph α _ (scott α univ) ⟨rfl⟩).isInducing.eq_induced

end Preorder
end IsLawson

/--
Type synonym for a preorder equipped with the Lawson topology.
-/
def WithLawson (α : Type*) := α

namespace WithLawson

/-- `toLawson` is the identity function to the `WithLawson` of a type. -/
@[match_pattern] def toLawson : α ≃ WithLawson α := Equiv.refl _

/-- `ofLawson` is the identity function from the `WithLawson` of a type. -/
@[match_pattern] def ofLawson : WithLawson α ≃ α := Equiv.refl _

@[simp] lemma to_Lawson_symm_eq : (@toLawson α).symm = ofLawson := rfl
@[simp] lemma of_Lawson_symm_eq : (@ofLawson α).symm = toLawson := rfl
@[simp] lemma toLawson_ofLawson (a : WithLawson α) : toLawson (ofLawson a) = a := rfl
@[simp] lemma ofLawson_toLawson (a : α) : ofLawson (toLawson a) = a := rfl

lemma toLawson_inj {a b : α} : toLawson a = toLawson b ↔ a = b := Iff.rfl

lemma ofLawson_inj {a b : WithLawson α} : ofLawson a = ofLawson b ↔ a = b := Iff.rfl

/-- A recursor for `WithLawson`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : WithLawson α → Sort*}
    (h : ∀ a, β (toLawson a)) : ∀ a, β a := fun a => h (ofLawson a)

instance [Nonempty α] : Nonempty (WithLawson α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithLawson α) := ‹Inhabited α›

variable [Preorder α]

instance instPreorder : Preorder (WithLawson α) := ‹Preorder α›
instance instTopologicalSpace : TopologicalSpace (WithLawson α) := lawson α
instance instIsLawson : IsLawson (WithLawson α) := ⟨rfl⟩

/-- If `α` is equipped with the Lawson topology, then it is homeomorphic to `WithLawson α`.
-/
def homeomorph [TopologicalSpace α] [IsLawson α] : WithLawson α ≃ₜ α :=
  ofLawson.toHomeomorphOfIsInducing ⟨IsLawson.topology_eq_lawson (α := α) ▸ induced_id.symm⟩

theorem isOpen_preimage_ofLawson {S : Set α} :
    IsOpen (ofLawson ⁻¹' S) ↔ (lawson α).IsOpen S := Iff.rfl

theorem isClosed_preimage_ofLawson {S : Set α} :
    IsClosed (ofLawson ⁻¹' S) ↔ IsClosed[lawson α] S := Iff.rfl

theorem isOpen_def {T : Set (WithLawson α)} :
    IsOpen T ↔ (lawson α).IsOpen (toLawson ⁻¹' T) := Iff.rfl

end WithLawson
end Lawson

section Preorder

variable [Preorder α]

lemma lawson_le_scott : lawson α ≤ scott α univ := inf_le_right

lemma lawson_le_lower : lawson α ≤ lower α := inf_le_left

lemma scottHausdorff_le_lawson : scottHausdorff α univ ≤ lawson α :=
  le_inf scottHausdorff_le_lower scottHausdorff_le_scott

lemma lawsonClosed_of_scottClosed (s : Set α) (h : IsClosed (WithScott.ofScott ⁻¹' s)) :
    IsClosed (WithLawson.ofLawson ⁻¹' s) := h.mono lawson_le_scott

lemma lawsonClosed_of_lowerClosed (s : Set α) (h : IsClosed (WithLower.ofLower ⁻¹' s)) :
    IsClosed (WithLawson.ofLawson ⁻¹' s) := h.mono lawson_le_lower

/-- An upper set is Lawson open if and only if it is Scott open -/
lemma lawsonOpen_iff_scottOpen_of_isUpperSet {s : Set α} (h : IsUpperSet s) :
    IsOpen (WithLawson.ofLawson ⁻¹' s) ↔ IsOpen (WithScott.ofScott ⁻¹' s) :=
  ⟨fun hs => IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open (D := univ).mpr
    ⟨h, (scottHausdorff_le_lawson s) hs⟩, lawson_le_scott _⟩

variable (L : TopologicalSpace α) (S : TopologicalSpace α)
variable [@IsLawson α _ L] [@IsScott α univ _ S]

lemma isLawson_le_isScott : L ≤ S := by
  rw [@IsScott.topology_eq α univ _ S _, @IsLawson.topology_eq_lawson α _ L _]
  exact inf_le_right

lemma scottHausdorff_le_isLawson : scottHausdorff α univ ≤ L := by
  rw [@IsLawson.topology_eq_lawson α _ L _]
  exact scottHausdorff_le_lawson

/-- An upper set is Lawson open if and only if it is Scott open -/
lemma lawsonOpen_iff_scottOpen_of_isUpperSet' (s : Set α) (h : IsUpperSet s) :
    IsOpen[L] s ↔ IsOpen[S] s := by
  rw [@IsLawson.topology_eq_lawson α _ L _, @IsScott.topology_eq α univ _ S _]
  exact lawsonOpen_iff_scottOpen_of_isUpperSet h

lemma lawsonClosed_iff_scottClosed_of_isLowerSet (s : Set α) (h : IsLowerSet s) :
    IsClosed[L] s ↔ IsClosed[S] s := by
  rw [← @isOpen_compl_iff, ← isOpen_compl_iff,
    (lawsonOpen_iff_scottOpen_of_isUpperSet' L S _ (isUpperSet_compl.mpr h))]

include S in
/-- A lower set is Lawson closed if and only if it is closed under sups of directed sets -/
lemma lawsonClosed_iff_dirSupClosed_of_isLowerSet (s : Set α) (h : IsLowerSet s) :
    IsClosed[L] s ↔ DirSupClosed s := by
  rw [lawsonClosed_iff_scottClosed_of_isLowerSet L S _ h,
    @IsScott.isClosed_iff_isLowerSet_and_dirSupClosed]
  simp_all

end Preorder

namespace IsLawson
variable [PartialOrder α] [TopologicalSpace α] [IsLawson α]

/-- The Lawson topology on a partial order is T₁. -/
-- see Note [lower instance priority]
instance (priority := 90) toT1Space : T1Space α where
  t1 a := by
    simp only [IsLawson.topology_eq_lawson]
    rw [← (Set.OrdConnected.upperClosure_inter_lowerClosure ordConnected_singleton),
      ← WithLawson.isClosed_preimage_ofLawson]
    apply IsClosed.inter
      (lawsonClosed_of_lowerClosed _ (IsLower.isClosed_upperClosure (finite_singleton a)))
    rw [lowerClosure_singleton, LowerSet.coe_Iic, ← WithLawson.isClosed_preimage_ofLawson]
    exact lawsonClosed_of_scottClosed _ isClosed_Iic

@[deprecated (since := "2025-07-02")] protected alias singleton_isClosed := isClosed_singleton

end IsLawson

end Topology
