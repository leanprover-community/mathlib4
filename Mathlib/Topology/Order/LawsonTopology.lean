/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Topology.Order.LowerTopology
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Tactic.LibrarySearch

/-!
# Lawson topology

This file introduces the Lawson topology on a preorder.

## Main definitions

- `LawsonTopology'` - the Lawson topology is defined as the join of the `LowerTopology` and the
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
The Lawson topology is defined as the join of the `LowerTopology` and the `ScottTopology`.
-/
def LawsonTopology' : TopologicalSpace α :=
  TopologicalSpace.generateFrom { s | ∃ a, Ici aᶜ = s } ⊔ ScottTopology'

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

end WithLawsonTopology

/--
The Lawson topology is defined as the join of the `LowerTopology` and the `ScottTopology`
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

end preorder

end LawsonTopology

variable (S : TopologicalSpace α) (L : TopologicalSpace α)

variable [Preorder α] [@ScottTopology α S _] [@LawsonTopology α L _]

lemma Scott_le_Lawson : S ≤ L := by
  rw [@ScottTopology.topology_eq α _ S _, @LawsonTopology.topology_eq α _ L _,  LawsonTopology']
  apply le_sup_right

open Topology

example : IsOpen[L] ≤ IsOpen[S] := TopologicalSpace.le_def.mp (Scott_le_Lawson _ _)


/-
lemma LawsonOpen_iff_ScottOpen (s : Set α) (h : IsUpperSet s) :
  IsOpen[L] s ↔ IsOpen[S] s := by
  constructor
  . sorry
  . sorry
-/
  /-
lemma LawsonOpen_iff_ScottOpen (s : Set α) [Preorder α] (h : IsUpperSet s) :
  LawsonTopology'.IsOpen s ↔ ScottTopology'.IsOpen s := by
  constructor
  . sorry
  . rw [← Pi.le_def]

  --apply (TopologicalSpace.le_def s)
-/
