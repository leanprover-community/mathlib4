/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Rel

/-!
# Uniform separation

This file defines a notion of separation of a set relative to an relation.

For a relation `R`, a `R`-separated set `s` is a set such that every pair of elements of `s` is
`R`-unrelated.

The concept of uniformly separated sets is used to define two further notions of separation:
* Metric separation: `Metric.IsSeparated`, defined using the small distance relation.
* Dynamical nets: `Dynamics.IsDynNetIn`, defined using the dynamical relation.

## TODO

* Actually use `SetRel.IsSeparated` to define the above two notions.
* Link to the notion of separation given by pairwise disjoint balls.
-/

open Set

namespace SetRel
variable {X : Type*} {R S : SetRel X X} {s t : Set X} {x : X}

/-- Given a relation `R`, a set `s` is `R`-separated if its elements are pairwise `R`-unrelated from
each other. -/
def IsSeparated (R : SetRel X X) (s : Set X) : Prop := s.Pairwise fun x y ↦ ¬ x ~[R] y

protected lemma IsSeparated.empty : IsSeparated R (∅ : Set X) := pairwise_empty _
protected lemma IsSeparated.singleton : IsSeparated R {x} := pairwise_singleton ..

@[simp] lemma IsSeparated.of_subsingleton (hs : s.Subsingleton) : IsSeparated R s := hs.pairwise _

alias _root_.Set.Subsingleton.relIsSeparated := IsSeparated.of_subsingleton

nonrec lemma IsSeparated.mono_left (hUV : R ⊆ S) (hs : IsSeparated S s) : IsSeparated R s :=
  hs.mono' fun _x _y hxy h ↦ hxy <| hUV h

lemma IsSeparated.mono_right (hst : s ⊆ t) (ht : IsSeparated R t) : IsSeparated R s := ht.mono hst

lemma isSeparated_insert' :
    IsSeparated R (insert x s) ↔ IsSeparated R s ∧ (∀ y ∈ s, x ~[R] y → x = y) ∧
        ∀ y ∈ s, y ~[R] x → x = y := by
  simp [IsSeparated, pairwise_insert, not_imp_comm (a := _ = _), -not_and, forall_and]

lemma isSeparated_insert [R.IsSymm] :
    IsSeparated R (insert x s) ↔ IsSeparated R s ∧ ∀ y ∈ s, x ~[R] y → x = y := by
  simpa [not_imp_not, IsSeparated] using pairwise_insert_of_symmetric fun _ _ ↦ mt R.symm

lemma isSeparated_insert_of_notMem [R.IsSymm] (hx : x ∉ s) :
    IsSeparated R (insert x s) ↔ IsSeparated R s ∧ ∀ y ∈ s, ¬ x ~[R] y :=
  pairwise_insert_of_symmetric_of_notMem (fun _ _ ↦ mt R.symm) hx

protected lemma IsSeparated.insert [R.IsSymm] (hs : IsSeparated R s)
    (h : ∀ y ∈ s, x ~[R] y → x = y) : IsSeparated R (insert x s) :=
  isSeparated_insert.2 ⟨hs, h⟩

end SetRel
