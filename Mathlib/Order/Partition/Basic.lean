/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.SupIndep

/-!
# Partitions

A `Partition` of an element `a` in a complete lattice is an independent family of nontrivial
elements whose supremum is `a`.

An important special case is where `s : Set α`, where a `Partition s` corresponds to a partition
of the elements of `s` into a family of nonempty sets.
This is equivalent to a transitive and symmetric binary relation `r : α → α → Prop`
where `s` is the set of all `x` for which `r x x`.

## Main definitions

* For `[CompleteLattice α]` and `s : α`, a `Set.Partition s` is an independent collection of
  nontrivial elements whose supremum is `s`.

## TODO

* Link this to `Finpartition`.
* Give API lemmas for the specialization to the `Set` case.

-/
variable {α : Type*} {s x y : α}

open Set

/-- A `Partition` of an element `s` of a `CompleteLattice` is a collection of
independent nontrivial elements whose supremum is `s`. -/
structure Partition [CompleteLattice α] (s : α) where
  /-- The collection of parts -/
  parts : Set α
  /-- The parts are `sSupIndep`. -/
  sSupIndep' : sSupIndep parts
  /-- The bottom element is not a part. -/
  bot_notMem' : ⊥ ∉ parts
  /-- The supremum of all parts is `s`. -/
  sSup_eq' : sSup parts = s

namespace Partition

@[deprecated (since := "2025-05-23")] alias bot_not_mem' := bot_notMem'

section Basic

variable [CompleteLattice α] {P : Partition s}

instance {s : α} : SetLike (Partition s) α where
  coe := Partition.parts
  coe_injective' p p' h := by cases p; cases p'; simpa using h

/-- See Note [custom simps projection]. -/
def Simps.coe {s : α} (P : Partition s) : Set α := P

initialize_simps_projections Partition (parts → coe, as_prefix coe)

@[simp] lemma coe_parts : P.parts = P := rfl

@[ext] lemma ext {P Q : Partition s} (hP : ∀ x, x ∈ P ↔ x ∈ Q) : P = Q :=
  SetLike.ext hP

@[simp]
lemma sSupIndep (P : Partition s) : sSupIndep (P : Set α) :=
  P.sSupIndep'

lemma disjoint (hx : x ∈ P) (hy : y ∈ P) (hxy : x ≠ y) :
    Disjoint x y :=
  P.sSupIndep.pairwiseDisjoint hx hy hxy

lemma pairwiseDisjoint : Set.PairwiseDisjoint (P : Set α) id :=
  P.sSupIndep'.pairwiseDisjoint

@[simp]
lemma sSup_eq (P : Partition s) : sSup P = s :=
  P.sSup_eq'

@[simp]
lemma iSup_eq (P : Partition s) : ⨆ x ∈ P, x = s := by
  simp_rw [← P.sSup_eq, sSup_eq_iSup]
  rfl

lemma le_of_mem (P : Partition s) (hx : x ∈ P) : x ≤ s :=
  (le_sSup hx).trans_eq P.sSup_eq

lemma parts_nonempty (P : Partition s) (hs : s ≠ ⊥) : (P : Set α).Nonempty :=
  nonempty_iff_ne_empty.2 fun hP ↦ by simp [← P.sSup_eq, hP, sSup_empty] at hs

@[simp]
lemma bot_notMem (P : Partition s) : ⊥ ∉ P :=
  P.bot_notMem'

@[deprecated (since := "2025-05-23")] alias bot_not_mem := bot_notMem

lemma ne_bot_of_mem (hx : x ∈ P) : x ≠ ⊥ :=
  fun h ↦ P.bot_notMem <| h ▸ hx

lemma bot_lt_of_mem (hx : x ∈ P) : ⊥ < x :=
  bot_lt_iff_ne_bot.2 <| P.ne_bot_of_mem hx

/-- Convert a `Partition s` into a `Partition t` via an equality `s = t`. -/
@[simps]
protected def copy {t : α} (P : Partition s) (hst : s = t) : Partition t where
  parts := P
  sSupIndep' := P.sSupIndep
  bot_notMem' := P.bot_notMem
  sSup_eq' := hst ▸ P.sSup_eq

@[simp]
lemma mem_copy_iff {t x : α} {P : Partition s} (hst : s = t) : x ∈ P.copy hst ↔ x ∈ P := Iff.rfl

/-- The natural equivalence between the subtype of parts and the subtype of parts of a copy. -/
@[simps!]
def partscopyEquiv {t : α} (P : Partition s) (hst : s = t) : ↥(P.copy hst) ≃ ↥P :=
  Equiv.setCongr rfl

/-- A constructor for `Partition s` that removes `⊥` from the set of parts. -/
@[simps]
def removeBot (P : Set α) (indep : _root_.sSupIndep P) (sSup_eq : sSup P = s) : Partition s where
  parts := P \ {⊥}
  sSupIndep' := indep.mono diff_subset
  bot_notMem' := by simp
  sSup_eq' := by simp [← sSup_eq]

end Basic

end Partition
