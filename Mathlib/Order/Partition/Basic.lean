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

-/
variable {α : Type*} {s x y z : α}

open Set

/-- A `Partition` of an element `s` of a `CompleteLattice` is a collection of
independent nontrivial elements whose supremum is `s`.  -/
structure Partition [CompleteLattice α] (s : α) where
  /-- The collection of parts-/
  parts : Set α
  /-- The parts are `sSupIndep`-/
  indep : sSupIndep parts
  /-- The bottom element is not a part-/
  bot_not_mem : ⊥ ∉ parts
  /-- The supremum of all parts is `s`-/
  sSup_eq' : sSup parts = s

namespace Partition

section Basic

variable [CompleteLattice α] {P : Partition s}

instance {α : Type*} [CompleteLattice α] {s : α} : SetLike (Partition s) α where
  coe := Partition.parts
  coe_injective' p p' h := by cases p; cases p'; simpa using h

@[simp] lemma mem_parts {x : α} : x ∈ P.parts ↔ x ∈ (P : Set α) := Iff.rfl

@[ext] lemma ext {P Q : Partition s} (hP : ∀ x, x ∈ P ↔ x ∈ Q) : P = Q := by
  cases P
  cases Q
  simp only [mk.injEq]
  ext x
  simpa using hP x

lemma disjoint (hx : x ∈ P) (hy : y ∈ P) (hxy : x ≠ y) :
    Disjoint x y :=
  P.indep.pairwiseDisjoint hx hy hxy

lemma pairwiseDisjoint : Set.PairwiseDisjoint (P : Set α) id :=
  fun _ hx _ hy hxy ↦ P.disjoint hx hy hxy

lemma ne_bot_of_mem (hx : x ∈ P) : x ≠ ⊥ :=
  fun h ↦ P.bot_not_mem <| h ▸ hx

lemma bot_lt_of_mem (hx : x ∈ P) : ⊥ < x :=
  bot_lt_iff_ne_bot.2 <| P.ne_bot_of_mem hx

@[simp]
lemma iSup_eq (P : Partition s) : ⨆ x ∈ P, x = s := by
  simp_rw [← P.sSup_eq', sSup_eq_iSup]
  rfl

@[simp]
lemma sSup_eq (P : Partition s) : sSup P = s :=
  P.sSup_eq'

lemma le_of_mem (P : Partition s) (hx : x ∈ P) : x ≤ s :=
  (le_sSup hx).trans_eq P.sSup_eq

lemma parts_nonempty (P : Partition s) (hs : s ≠ ⊥) : (P : Set α).Nonempty :=
  nonempty_iff_ne_empty.2 fun hP ↦ by simp [← P.sSup_eq, hP, sSup_empty] at hs

/-- Convert a `Partition s` into a `Partition t` via an equality `s = t`. -/
@[simps]
protected def copy {t : α} (P : Partition s) (hst : s = t) : Partition t where
  parts := P.parts
  indep := P.indep
  bot_not_mem := P.bot_not_mem
  sSup_eq' := hst ▸ P.sSup_eq'

@[simp]
lemma coe_copy_eq {t : α} {P : Partition s} (hst : s = t) :
    (P.copy hst : Set α) = P := rfl

@[simp]
lemma mem_copy_iff {t x : α} {P : Partition s} (hst : s = t) :
    x ∈ P.copy hst ↔ x ∈ P := Iff.rfl

@[simps!]
def partscopyEquiv {t : α} (P : Partition s) (hst : s = t) :
    (P : Set α) ≃ (P.copy hst : Set α) := Equiv.Set.ofEq rfl

end Basic

end Partition
