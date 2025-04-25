/-
Copyright (c) 2024 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
import Mathlib.Order.CompleteLattice.SetLike

/-!
# Trees in the sense of descriptive set theory

This file defines trees of depth `ω` in the sense of descriptive set theory as sets of finite
sequences that are stable under taking prefixes.

## Main declarations

* `tree A`: a (possibly infinite) tree of depth at most `ω` with nodes in `A`
-/

namespace Descriptive

/-- A tree is a set of finite sequences, implemented as `List A`, that is stable under
  taking prefixes. For the definition we use the equivalent property `x ++ [a] ∈ T → x ∈ T`,
  which is more convenient to check. We define `tree A` as a complete sublattice of
  `Set (List A)`, which coerces to the type of trees on `A`. -/
def tree (A : Type*) : CompleteSublattice (Set (List A)) :=
  CompleteSublattice.mk' {T | ∀ ⦃x : List A⦄ ⦃a : A⦄, x ++ [a] ∈ T → x ∈ T}
    (by rintro S hS x a ⟨t, ht, hx⟩; use t, ht, hS ht hx)
    (by rintro S hS x a h T hT; exact hS hT <| h T hT)

instance (A : Type*) : SetLike (tree A) (List A) := SetLike.instSubtypeSet

variable {A : Type*} {T : tree A}

lemma mem_of_append {x y : List A} (h : x ++ y ∈ T) : x ∈ T := by
  induction' y with y ys ih generalizing x
  · simpa using h
  · exact T.prop (ih (by simpa))

lemma mem_of_prefix {x y : List A} (h' : x <+: y) (h : y ∈ T) : x ∈ T := by
  obtain ⟨_, rfl⟩ := h'; exact mem_of_append h

@[simp] lemma tree_eq_bot : T = ⊥ ↔ [] ∉ T where
  mp := by rintro rfl; simp
  mpr h := by ext x; simpa using fun h' ↦ h <| mem_of_prefix x.nil_prefix h'

end Descriptive
