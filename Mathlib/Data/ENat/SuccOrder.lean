/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Group.Nat.Units
public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.WithTop
public import Mathlib.Data.ENat.Basic


instance : SuccAddOrder ℕ∞ where
  succ_eq_add_one x := by cases x <;> simp


@[simp] theorem succ_natCast (n : ℕ) : SuccOrder.succ (n : ℕ∞) = (n + 1 : ℕ) := WithTop.succ_coe

@[deprecated (since := "2026-07-17")] alias succ_coe := succ_natCast


@[simp] theorem succ_top : SuccOrder.succ (⊤ : ℕ∞) = ⊤ := rfl


@[deprecated Order.succ_eq_add_one (since := "2026-05-25")]
theorem succ_def (m : ℕ∞) : Order.succ m = m + 1 :=
  Order.succ_eq_add_one m

theorem add_one_le_iff (hm : m ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
  Order.add_one_le_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hm)

theorem add_one_le_iff' (hn : n ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
  Order.add_one_le_iff_of_not_isMax' (not_isMax_iff_ne_top.mpr hn)
