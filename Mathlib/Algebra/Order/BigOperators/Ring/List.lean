/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
module

public import Batteries.Data.List.Basic
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Ring.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

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
