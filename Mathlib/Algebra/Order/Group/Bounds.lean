/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Algebra.Order.Group.Defs

#align_import algebra.order.group.bounds from "leanprover-community/mathlib"@"d012cd09a9b256d870751284dd6a29882b0be105"

/-!
# Least upper bound and the greatest lower bound in linear ordered additive commutative groups
-/

section LinearOrderedAddCommGroup

variable {α : Type*} [LinearOrderedAddCommGroup α] {s : Set α} {a ε : α}

theorem IsGLB.exists_between_self_add (h : IsGLB s a) (hε : 0 < ε) : ∃ b ∈ s, a ≤ b ∧ b < a + ε :=
  h.exists_between <| lt_add_of_pos_right _ hε
#align is_glb.exists_between_self_add IsGLB.exists_between_self_add

theorem IsGLB.exists_between_self_add' (h : IsGLB s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    ∃ b ∈ s, a < b ∧ b < a + ε :=
  h.exists_between' h₂ <| lt_add_of_pos_right _ hε
#align is_glb.exists_between_self_add' IsGLB.exists_between_self_add'

theorem IsLUB.exists_between_sub_self (h : IsLUB s a) (hε : 0 < ε) : ∃ b ∈ s, a - ε < b ∧ b ≤ a :=
  h.exists_between <| sub_lt_self _ hε
#align is_lub.exists_between_sub_self IsLUB.exists_between_sub_self

theorem IsLUB.exists_between_sub_self' (h : IsLUB s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    ∃ b ∈ s, a - ε < b ∧ b < a :=
  h.exists_between' h₂ <| sub_lt_self _ hε
#align is_lub.exists_between_sub_self' IsLUB.exists_between_sub_self'

end LinearOrderedAddCommGroup
