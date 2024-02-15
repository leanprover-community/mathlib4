/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.OrderDual

#align_import order.conditionally_complete_lattice.group from "leanprover-community/mathlib"@"46a64b5b4268c594af770c44d9e502afc6a515cb"

/-!
# Conditionally complete lattices and groups.

-/


section Group

variable {α : Type*} {ι : Sort*} {ι' : Sort*} [Nonempty ι] [Nonempty ι']
  [ConditionallyCompleteLattice α] [Group α]

@[to_additive]
theorem le_mul_ciInf [CovariantClass α α (· * ·) (· ≤ ·)] {a : α} {g : α} {h : ι → α}
    (H : ∀ j, a ≤ g * h j) : a ≤ g * iInf h :=
  inv_mul_le_iff_le_mul.mp <| le_ciInf fun _ => inv_mul_le_iff_le_mul.mpr <| H _
#align le_mul_cinfi le_mul_ciInf
#align le_add_cinfi le_add_ciInf

@[to_additive]
theorem mul_ciSup_le [CovariantClass α α (· * ·) (· ≤ ·)] {a : α} {g : α} {h : ι → α}
    (H : ∀ j, g * h j ≤ a) : g * iSup h ≤ a :=
  le_mul_ciInf (α := αᵒᵈ) H
#align mul_csupr_le mul_ciSup_le
#align add_csupr_le add_ciSup_le

@[to_additive]
theorem le_ciInf_mul [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α}
    {h : α} (H : ∀ i, a ≤ g i * h) : a ≤ iInf g * h :=
  mul_inv_le_iff_le_mul.mp <| le_ciInf fun _ => mul_inv_le_iff_le_mul.mpr <| H _
#align le_cinfi_mul le_ciInf_mul
#align le_cinfi_add le_ciInf_add

@[to_additive]
theorem ciSup_mul_le [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α}
    {h : α} (H : ∀ i, g i * h ≤ a) : iSup g * h ≤ a :=
  le_ciInf_mul (α := αᵒᵈ) H
#align csupr_mul_le ciSup_mul_le
#align csupr_add_le ciSup_add_le

@[to_additive]
theorem le_ciInf_mul_ciInf [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α} {h : ι' → α}
    (H : ∀ i j, a ≤ g i * h j) : a ≤ iInf g * iInf h :=
  le_ciInf_mul fun _ => le_mul_ciInf <| H _
#align le_cinfi_mul_cinfi le_ciInf_mul_ciInf
#align le_cinfi_add_cinfi le_ciInf_add_ciInf

@[to_additive]
theorem ciSup_mul_ciSup_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α} {h : ι' → α}
    (H : ∀ i j, g i * h j ≤ a) : iSup g * iSup h ≤ a :=
  ciSup_mul_le fun _ => mul_ciSup_le <| H _
#align csupr_mul_csupr_le ciSup_mul_ciSup_le
#align csupr_add_csupr_le ciSup_add_ciSup_le

end Group
