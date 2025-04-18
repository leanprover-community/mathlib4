/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Algebra.Order.Group.Defs

/-!
# Least upper bound and the greatest lower bound in linear ordered additive commutative groups
-/

section LinearOrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {s : Set α} {a ε : α}

theorem IsGLB.exists_between_self_add (h : IsGLB s a) (hε : 0 < ε) : ∃ b ∈ s, a ≤ b ∧ b < a + ε :=
  h.exists_between <| lt_add_of_pos_right _ hε

theorem IsGLB.exists_between_self_add' (h : IsGLB s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    ∃ b ∈ s, a < b ∧ b < a + ε :=
  h.exists_between' h₂ <| lt_add_of_pos_right _ hε

theorem IsLUB.exists_between_sub_self (h : IsLUB s a) (hε : 0 < ε) : ∃ b ∈ s, a - ε < b ∧ b ≤ a :=
  h.exists_between <| sub_lt_self _ hε

theorem IsLUB.exists_between_sub_self' (h : IsLUB s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    ∃ b ∈ s, a - ε < b ∧ b < a :=
  h.exists_between' h₂ <| sub_lt_self _ hε

end LinearOrderedAddCommGroup
