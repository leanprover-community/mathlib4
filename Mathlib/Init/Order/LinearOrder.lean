/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Batteries.Classes.Order
import Mathlib.Init.Algebra.Classes
import Mathlib.Init.Order.Defs
import Mathlib.Init.Data.Ordering.Basic

/-!
# Orders

Some slightly less basic lemmas about linear orders.
-/

universe u
variable {α : Type u}

variable [LinearOrder α]

instance : IsTotalPreorder α (· ≤ ·) where
  trans := @le_trans _ _
  total := le_total

-- TODO(Leo): decide whether we should keep this instance or not
instance isStrictWeakOrder_of_linearOrder : IsStrictWeakOrder α (· < ·) :=
  have : IsTotalPreorder α (· ≤ ·) := by infer_instance -- Porting note: added
  isStrictWeakOrder_of_isTotalPreorder lt_iff_not_ge
#align is_strict_weak_order_of_linear_order isStrictWeakOrder_of_linearOrder

-- TODO(Leo): decide whether we should keep this instance or not
instance isStrictTotalOrder_of_linearOrder : IsStrictTotalOrder α (· < ·) where
  trichotomous := lt_trichotomy
#align is_strict_total_order_of_linear_order isStrictTotalOrder_of_linearOrder

theorem compare_iff (a b : α) {o : Ordering} : compare a b = o ↔ o.toRel a b := by
  cases o <;> simp only [Ordering.toRel]
  · exact compare_lt_iff_lt
  · exact compare_eq_iff_eq
  · exact compare_gt_iff_gt

instance : Batteries.TransCmp (compare (α := α)) where
  symm a b := by
    cases h : compare a b <;>
    simp only [Ordering.swap] <;> apply Eq.symm
    · exact compare_gt_iff_gt.2 <| compare_lt_iff_lt.1 h
    · exact compare_eq_iff_eq.2 <| compare_eq_iff_eq.1 h |>.symm
    · exact compare_lt_iff_lt.2 <| compare_gt_iff_gt.1 h
  le_trans := fun h₁ h₂ ↦
    compare_le_iff_le.2 <| le_trans (compare_le_iff_le.1 h₁) (compare_le_iff_le.1 h₂)
