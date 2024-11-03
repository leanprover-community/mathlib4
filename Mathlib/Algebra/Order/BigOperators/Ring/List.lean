/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Canonical

/-!
# Big operators on a list in ordered rings

This file contains the results concerning the interaction of list big operators with ordered rings.
-/

variable {R : Type*}

/-- A variant of `List.prod_pos` for `CanonicallyOrderedCommSemiring`. -/
@[simp] lemma CanonicallyOrderedCommSemiring.list_prod_pos
    {α : Type*} [CanonicallyOrderedCommSemiring α] [Nontrivial α] :
    ∀ {l : List α}, 0 < l.prod ↔ (∀ x ∈ l, (0 : α) < x)
  | [] => by simp
  | (x :: xs) => by simp_rw [List.prod_cons, List.forall_mem_cons,
      CanonicallyOrderedCommSemiring.mul_pos, list_prod_pos]
