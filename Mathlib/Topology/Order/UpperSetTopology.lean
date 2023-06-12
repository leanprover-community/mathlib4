/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Order.Lattice
import Mathlib.Order.Hom.CompleteLattice

/-!
# UpperSet topology

This file introduces the upper set topology on a preorder as the topology where the open sets are
the upper sets.

## Main statements

## Implementation notes

A type synonym `WithUpperSetTopology` is introduced and for a preorder `α`, `WithUpperSetTopology α`
is made an instance of `TopologicalSpace` by the topology where the upper sets are the open sets.

We define a mixin class `UpperSetTopology` for the class of types which are both a preorder and a
topology and where the open sets are the upper sets. It is shown that `WithUpperSetTopology α` is an
instance of `UpperSetTopology`.

## Motivation

I need to take a run at this.

## Tags

upper set topology, preorder, Alexandrov
-/


variable (α β : Type _)

section preorder

variable [Preorder α]

/--
The set of upper sets forms a topology
-/
def upperSetTopology' : TopologicalSpace α :=
{ IsOpen := IsUpperSet,
  isOpen_univ := isUpperSet_univ,
  isOpen_inter := fun _ _ => IsUpperSet.inter,
  isOpen_sUnion := fun _ h => isUpperSet_sUnion h, }

end preorder

open Set TopologicalSpace

/-- Type synonym for a preorder equipped with the upper set topology. -/
def WithUpperSetTopology := α

variable {α β}

namespace WithUpperSetTopology

/-- `toUpperSet` is the identity function to the `WithUpperSetTopology` of a type.  -/
@[match_pattern]
def toUpperSet : α ≃ WithUpperSetTopology α := Equiv.refl _

/-- `ofUpperSet` is the identity function from the `WithUpperSetTopology` of a type.  -/
@[match_pattern]
def ofUpperSet : WithUpperSetTopology α ≃ α := Equiv.refl _

@[simp]
theorem to_withUpperSetTopology_symm_eq : (@toUpperSet α).symm = ofUpperSet :=
  rfl

@[simp]
theorem of_withUpperSetTopology_symm_eq : (@ofUpperSet α).symm = toUpperSet :=
  rfl

@[simp]
theorem toUpperSet_ofUpperSet (a : WithUpperSetTopology α) : toUpperSet (ofUpperSet a) = a :=
  rfl

@[simp]
theorem ofUpperSet_toUpperSet (a : α) : ofUpperSet (toUpperSet a) = a :=
  rfl

theorem toUpperSet_inj {a b : α} : toUpperSet a = toUpperSet b ↔ a = b :=
  Iff.rfl

theorem ofUpperSet_inj {a b : WithUpperSetTopology α} : ofUpperSet a = ofUpperSet b ↔ a = b :=
  Iff.rfl

/-- A recursor for `WithUpperSetTopology`. Use as `induction x using WithUpperSetTopology.rec`. -/
protected def rec {β : WithUpperSetTopology α → Sort _} (h : ∀ a, β (toUpperSet a)) : ∀ a, β a :=
fun a => h (ofUpperSet a)

instance [Nonempty α] : Nonempty (WithUpperSetTopology α) :=
  ‹Nonempty α›

instance [Inhabited α] : Inhabited (WithUpperSetTopology α) :=
  ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithUpperSetTopology α) :=
  ‹Preorder α›

instance : TopologicalSpace (WithUpperSetTopology α) := upperSetTopology' α

end WithUpperSetTopology

/--
The upper set topology is the topology where the open sets are the upper sets.
-/
class UpperSetTopology (α : Type _) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_upperSetTopology : t = upperSetTopology' α

instance [Preorder α] : UpperSetTopology (WithUpperSetTopology α) :=
  ⟨rfl⟩

namespace UpperSetTopology

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [UpperSetTopology α] {s : Set α}

lemma topology_eq : ‹_› = upperSetTopology' α := topology_eq_upperSetTopology

variable {α}

/-- If `α` is equipped with the upper set topology, then it is homeomorphic to
`WithUpperSetTopology α`.
-/
def withUpperSetTopologyHomeomorph : WithUpperSetTopology α ≃ₜ α :=
  WithUpperSetTopology.ofUpperSet.toHomeomorphOfInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩

end Preorder

end UpperSetTopology
