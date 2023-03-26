/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
Ported by: Anatole Dedecker

! This file was ported from Lean 3 source module order.conditionally_complete_lattice.group
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Group.TypeTags

/-!
# Conditionally complete lattices and groups.

-/


section Group

variable {α : Type _} {ι : Sort _} {ι' : Sort _} [Nonempty ι] [Nonempty ι']
  [ConditionallyCompleteLattice α] [Group α]

@[to_additive]
theorem le_mul_cinfᵢ [CovariantClass α α (· * ·) (· ≤ ·)] {a : α} {g : α} {h : ι → α}
    (H : ∀ j, a ≤ g * h j) : a ≤ g * infᵢ h :=
  inv_mul_le_iff_le_mul.mp <| le_cinfᵢ fun _ => inv_mul_le_iff_le_mul.mpr <| H _
#align le_mul_cinfi le_mul_cinfᵢ
#align le_add_cinfi le_add_cinfᵢ

@[to_additive]
theorem mul_csupᵢ_le [CovariantClass α α (· * ·) (· ≤ ·)] {a : α} {g : α} {h : ι → α}
    (H : ∀ j, g * h j ≤ a) : g * supᵢ h ≤ a :=
  @le_mul_cinfᵢ αᵒᵈ _ _ _ _ _ _ _ _ H
#align mul_csupr_le mul_csupᵢ_le
#align add_csupr_le add_csupᵢ_le

@[to_additive]
theorem le_cinfᵢ_mul [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α}
    {h : α} (H : ∀ i, a ≤ g i * h) : a ≤ infᵢ g * h :=
  mul_inv_le_iff_le_mul.mp <| le_cinfᵢ fun _ => mul_inv_le_iff_le_mul.mpr <| H _
#align le_cinfi_mul le_cinfᵢ_mul
#align le_cinfi_add le_cinfᵢ_add

@[to_additive]
theorem csupᵢ_mul_le [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α}
    {h : α} (H : ∀ i, g i * h ≤ a) : supᵢ g * h ≤ a :=
  @le_cinfᵢ_mul αᵒᵈ _ _ _ _ _ _ _ _ H
#align csupr_mul_le csupᵢ_mul_le
#align csupr_add_le csupᵢ_add_le

@[to_additive]
theorem le_cinfᵢ_mul_cinfᵢ [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α} {h : ι' → α}
    (H : ∀ i j, a ≤ g i * h j) : a ≤ infᵢ g * infᵢ h :=
  le_cinfᵢ_mul fun _ => le_mul_cinfᵢ <| H _
#align le_cinfi_mul_cinfi le_cinfᵢ_mul_cinfᵢ
#align le_cinfi_add_cinfi le_cinfᵢ_add_cinfᵢ

@[to_additive]
theorem csupᵢ_mul_csupᵢ_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α} {h : ι' → α}
    (H : ∀ i j, g i * h j ≤ a) : supᵢ g * supᵢ h ≤ a :=
  csupᵢ_mul_le fun _ => mul_csupᵢ_le <| H _
#align csupr_mul_csupr_le csupᵢ_mul_csupᵢ_le
#align csupr_add_csupr_le csupᵢ_add_csupᵢ_le

end Group
