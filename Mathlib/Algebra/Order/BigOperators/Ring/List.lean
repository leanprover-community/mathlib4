import Batteries.Data.List.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Big operators on a list in ordered rings

This file contains the results concerning the interaction of list big operators with ordered rings.
-/

public section

variable {R : Type*}

/-- A variant of `List.prod_pos` for `CanonicallyOrderedAdd`. -/
@[simp] lemma CanonicallyOrderedAdd.list_prod_pos {α : Type*}
    [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α] [NoZeroDivisors α] [Nontrivial α] :
    ∀ {l : List α}, 0 < l.prod ↔ (∀ x ∈ l, (0 : α) < x)
  | [] => by simp
  | (x :: xs) => by simp_rw [List.prod_cons, List.forall_mem_cons, CanonicallyOrderedAdd.mul_pos,
    list_prod_pos]
