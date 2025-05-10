/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Topology.UniformSpace.Entourage

/-!
# Uniform separation

This file defines a notion of separation of a set given a uniformity.

A `U`-separated set `s` is a set such that every pair of elements of `s` is `U`-far.

The concept of uniformly separated sets is used to define two further notions of separation:
* Metric separation: `Metric.IsSeparated`, defined using the distance entourage.
* Dynamical nets: `Dynamics.IsDynNetIn`, defined using the dynamical entourage.
-/

open Set

namespace UniformSpace
variable {X : Type*} {U V : Set (X × X)} {s t : Set X} {x : X}

/-- Given a uniformity `U`, a set `s` is `U`-separated if its elements are pairwise `U`-far from
each other. -/
def IsSeparated (U : Set (X × X)) (s : Set X) : Prop := s.Pairwise fun x y ↦ (x, y) ∉ U

protected lemma IsSeparated.empty : IsSeparated U (∅ : Set X) := pairwise_empty _
protected lemma IsSeparated.singleton : IsSeparated U {x} := pairwise_singleton ..

@[simp] lemma IsSeparated.of_subsingleton (hs : s.Subsingleton) : IsSeparated U s := hs.pairwise _

alias _root_.Set.Subsingleton.uniformSpaceIsSeparated := IsSeparated.of_subsingleton

nonrec lemma IsSeparated.anti (hUV : U ⊆ V) (hs : IsSeparated V s) : IsSeparated U s :=
  hs.mono' fun _x _y hxy h ↦ hxy <| hUV h

lemma IsSeparated.subset (hst : s ⊆ t) (hs : IsSeparated U t) : IsSeparated U s := hs.mono hst

lemma isSeparated_insert (hU : IsSymmetricRel U) :
    IsSeparated U (insert x s) ↔ IsSeparated U s ∧ ∀ y ∈ s, x ≠ y → (x, y) ∉ U :=
  pairwise_insert_of_symmetric fun _ _ ↦ hU.mk_mem_comm.not.1

lemma isSeparated_insert_of_not_mem (hU : IsSymmetricRel U) (hx : x ∉ s) :
    IsSeparated U (insert x s) ↔ IsSeparated U s ∧ ∀ y ∈ s, (x, y) ∉ U :=
  pairwise_insert_of_symmetric_of_not_mem (fun _ _ ↦ hU.mk_mem_comm.not.1) hx

protected lemma IsSeparated.insert (hU : IsSymmetricRel U) (hs : IsSeparated U s)
    (h : ∀ y ∈ s, x ≠ y → (x, y) ∉ U) : IsSeparated U (insert x s) :=
  (isSeparated_insert hU).2 ⟨hs, h⟩

end UniformSpace
