/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn

! This file was ported from Lean 3 source module algebra.order.field.canonical.basic
! leanprover-community/mathlib commit ee0c179cd3c8a45aa5bffbf1b41d8dbede452865
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Order.Field.Canonical.Defs

/-!
# Lemmas about canonically ordered semifields.

-/


variable {α : Type _}

section CanonicallyLinearOrderedSemifield

variable [CanonicallyLinearOrderedSemifield α] [Sub α] [OrderedSub α]

theorem tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]
#align tsub_div tsub_div

end CanonicallyLinearOrderedSemifield
