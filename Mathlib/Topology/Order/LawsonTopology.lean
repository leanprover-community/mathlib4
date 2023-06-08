/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Topology.Order.ScottTopology
import Mathlib.Tactic.LibrarySearch

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

variable (α β : Type _)

open Set

section preorder

variable {α} {β}

variable [Preorder α]

/--
The Lawson topology is defined as the meet of the `LowerTopology` and the `ScottTopology`.
-/
def LawsonTopology' : TopologicalSpace α :=
  LowerTopology' ⊓ ScottTopology'

end preorder

/--
Type synonym for a preorder equipped with the Lawson topology
-/
def WithLawsonTopology := α

variable {α β}

namespace WithLawsonTopology

/-- `toLawson` is the identity function to the `WithLawsonTopology` of a type.  -/
@[match_pattern] def toLawson : α ≃ WithLawsonTopology α := Equiv.refl _

/-- `ofLawson` is the identity function from the `WithLawsonTopology` of a type.  -/
@[match_pattern] def ofLawson : WithLawsonTopology α ≃ α := Equiv.refl _

@[simp] lemma to_Lawson_symm_eq : (@toLawson α).symm = ofLawson := rfl
@[simp] lemma of_Lawson_symm_eq : (@ofLawson α).symm = toLawson := rfl
@[simp] lemma toLawson_ofLawson (a : WithLawsonTopology α) : toLawson (ofLawson a) = a := rfl
@[simp] lemma ofLawson_toLawson (a : α) : ofLawson (toLawson a) = a := rfl
-- porting note: removed @[simp] to make linter happy
lemma toLawson_inj {a b : α} : toLawson a = toLawson b ↔ a = b := Iff.rfl
-- porting note: removed @[simp] to make linter happy
lemma ofLawson_inj {a b : WithLawsonTopology α} : ofLawson a = ofLawson b ↔ a = b :=
Iff.rfl

/-- A recursor for `WithLawsonTopology`. Use as `induction x using WithLawsonTopology.rec`. -/
protected def rec {β : WithLawsonTopology α → Sort _}
  (h : ∀ a, β (toLawson a)) : ∀ a, β a := fun a => h (ofLawson a)

instance [Nonempty α] : Nonempty (WithLawsonTopology α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithLawsonTopology α) := ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithLawsonTopology α) := ‹Preorder α›

instance : TopologicalSpace (WithLawsonTopology α) := LawsonTopology'

theorem isOpen_preimage_ofLawson (S : Set α) :
    IsOpen (WithLawsonTopology.ofLawson ⁻¹' S) ↔
      LawsonTopology'.IsOpen S :=
  Iff.rfl

theorem isOpen_def (T : Set (WithLawsonTopology α)) :
    IsOpen T ↔
      LawsonTopology'.IsOpen (WithLawsonTopology.toLawson ⁻¹' T) :=
  Iff.rfl

end WithLawsonTopology

/--
The Lawson topology is defined as the meet of the `LowerTopology` and the `ScottTopology`
-/
class LawsonTopology (α : Type _) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_LawsonTopology : t = LawsonTopology'

instance [Preorder α] : LawsonTopology (WithLawsonTopology α) := ⟨rfl⟩

namespace LawsonTopology

section preorder

variable [Preorder α]

variable [TopologicalSpace α] [LawsonTopology α]

variable (α)

lemma topology_eq : ‹_› = LawsonTopology' := topology_eq_LawsonTopology

variable {α}

/-- If `α` is equipped with the Lawson topology, then it is homeomorphic to `WithLawsonTopology α`.
-/
def withLawsonTopologyHomeomorph : WithLawsonTopology α ≃ₜ α :=
  WithLawsonTopology.ofLawson.toHomeomorphOfInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩

/-
lemma isOpen_iff_Lower_and_Scott_Open (u : Set α) : LawsonTopology'.IsOpen u
↔ (LowerTopology'.IsOpen u ∧ ScottTopology'.IsOpen u) := by
-/



lemma isOpen_iff_Lower_and_Scott_Open (u : Set α) : IsOpen (WithLawsonTopology.ofLawson ⁻¹' u) ↔
  IsOpen (WithLowerTopology.toLower u) ∧  IsOpen (WithScottTopology.toScott u) := by
  rw [WithLawsonTopology.isOpen_preimage_ofLawson]
  sorry



end preorder

end LawsonTopology

section ts

variable [Preorder α]

lemma Lawson_le_Scott' : @LawsonTopology' α ≤ @ScottTopology' α := inf_le_right

lemma Lawson_le_Lower' : @LawsonTopology' α ≤ @LowerTopology' α := inf_le_left

lemma Scott_Hausdorff_le_Lawson' : @ScottHausdorffTopology α _ ≤ @LawsonTopology' α _ := by
  rw [LawsonTopology', le_inf_iff]
  constructor
  . exact @Scott_Hausdorff_le_Lower' α _
  . exact @Scott_Hausdorff_le_Scott' α _



lemma LawsonOpen_implies_ScottHausdorffOpen''' (s : Set α) :
  IsOpen (WithLawsonTopology.ofLawson ⁻¹' s) → ScottHausdorffTopology.IsOpen s :=
  Scott_Hausdorff_le_Lawson' _

lemma LawsonOpen_implies_ScottOpen''' (s : Set α) :
  IsOpen (WithScottTopology.ofScott ⁻¹' s) → IsOpen (WithLawsonTopology.ofLawson ⁻¹' s) :=
  Lawson_le_Scott' _ s

lemma LawsonOpen_implies_LowerOpen''' (s : Set α) :
  IsOpen (WithLowerTopology.ofLower ⁻¹' s) → IsOpen (WithLawsonTopology.ofLawson ⁻¹' s) :=
  Lawson_le_Lower' _ s

end ts

section csh

/-
-- Not true!
lemma isOpen_iff_Lower_and_Scott_Open [Preorder α] (u : Set α) : IsOpen (WithLawsonTopology.ofLawson ⁻¹' u ) ↔
  IsOpen (WithLowerTopology.ofLower ⁻¹' u) ∧  IsOpen (WithScottTopology.ofScott ⁻¹' u) := by
  constructor
  . intro h
    constructor
    . sorry
    . apply LawsonOpen_implies_ScottOpen''' u
  . sorry
-/


lemma ScottLawsonCont' [Preorder α] :
  Continuous (WithScottTopology.toScott ∘ WithLawsonTopology.ofLawson : WithLawsonTopology α → _) :=
by
  rw [continuous_def]
  intro s hs
  apply LawsonOpen_implies_ScottOpen''' _ hs



variable  (L : TopologicalSpace α) (l : TopologicalSpace α) (S : TopologicalSpace α)

variable [Preorder α]  [@LawsonTopology α L _] [@LowerTopology α l _] [@ScottTopology α S _]

lemma Scott_le_Lawson : L ≤ S := by
  rw [@ScottTopology.topology_eq α _ S _, @LawsonTopology.topology_eq α _ L _,  LawsonTopology']
  apply inf_le_right

lemma Scott_Hausdorff_le_Lawson : (@ScottHausdorffTopology α _) ≤ L := by
  rw [@LawsonTopology.topology_eq α _ L _,  LawsonTopology', le_inf_iff,
    ← @LowerTopology.topology_eq α _ l _, ← @ScottTopology.topology_eq α _ S _]
  constructor
  . exact @Scott_Hausdorff_le_Lower  α _ l _
  . exact Scott_Hausdorff_le_Scott

open Topology

lemma LawsonOpen_implies_ScottHausdorffOpen : IsOpen[L] ≤ IsOpen[ScottHausdorffTopology] := by
  rw [←TopologicalSpace.le_def]
  apply (@Scott_Hausdorff_le_Lawson _ L l _ _ _)


lemma LawsonOpen_implies_ScottHausdorffOpen' (s : Set α) :
IsOpen[L] s → IsOpen[ScottHausdorffTopology] s := by
  apply (@LawsonOpen_implies_ScottHausdorffOpen _ _ l)

end csh

-- Can we say something without CL?
section CompleteLattice

variable [CompleteLattice α]
  (S :TopologicalSpace α) (l : TopologicalSpace α) (L : TopologicalSpace α)
  [@ScottTopology α S _]  [@LawsonTopology α L _] [@LowerTopology α l _]

-- Scott open iff UpperSet and STopology open

open Topology

lemma LawsonOpen_iff_ScottOpen (s : Set α) (h : IsUpperSet s) :
  IsOpen[L] s ↔ IsOpen[S] s := by
  constructor
  . intro hs
    rw [@ScottTopology.isOpen_iff_upper_and_Scott_Hausdorff_Open α _ S]
    constructor
    . exact h
    . exact fun d d₁ d₂ d₃ => (@LawsonOpen_implies_ScottHausdorffOpen' _ _ l S _ _ _ _ s)
        hs d d₁ d₂ d₃
  . apply TopologicalSpace.le_def.mp (Scott_le_Lawson _ _)

end CompleteLattice
