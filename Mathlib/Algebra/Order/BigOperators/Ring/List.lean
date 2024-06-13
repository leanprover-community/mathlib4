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

namespace List

/-- The product of a list of positive natural numbers is positive,
and likewise for any nontrivial ordered semiring. -/
lemma prod_pos [StrictOrderedSemiring R] (l : List R) (h : ∀ a ∈ l, (0 : R) < a) :
    0 < l.prod := by
  induction' l with a l ih
  · simp
  · rw [prod_cons]
    exact mul_pos (h _ <| mem_cons_self _ _) (ih fun a ha => h a <| mem_cons_of_mem _ ha)
#align list.prod_pos List.prod_pos

/-- A variant of `List.prod_pos` for `CanonicallyOrderedCommSemiring`. -/
@[simp] lemma _root_.CanonicallyOrderedCommSemiring.list_prod_pos
    {α : Type*} [CanonicallyOrderedCommSemiring α] [Nontrivial α] :
    ∀ {l : List α}, 0 < l.prod ↔ (∀ x ∈ l, (0 : α) < x)
  | [] => by simp
  | (x :: xs) => by simp_rw [prod_cons, forall_mem_cons, CanonicallyOrderedCommSemiring.mul_pos,
    list_prod_pos]
#align canonically_ordered_comm_semiring.list_prod_pos CanonicallyOrderedCommSemiring.list_prod_pos

end List
