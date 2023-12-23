/-
Copyright (c) 2023 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr.Core

/-! # Setup for the `gcongr` tactic

The core implementation of the `gcongr` ("generalized congruence") tactic is in the file
`Tactic.GCongr.Core`.  In this file we set it up for use across the library by tagging a minimal
set of lemmas with the attribute `@[gcongr]` and by listing `positivity` as a first-pass
discharger for side goals (`gcongr_discharger`). -/

set_option autoImplicit true

macro_rules | `(tactic| gcongr_discharger) => `(tactic| positivity)

/-! # ≤, - -/

attribute [gcongr]
  neg_le_neg -- tt

/-! # <, - -/

attribute [gcongr]
  neg_lt_neg -- tt

/-! # ≤, + -/

attribute [gcongr]
  add_le_add -- tt + tt
  add_le_add_left -- ff + tt
  add_le_add_right -- tt + ff

/-! # <, + -/

attribute [gcongr]
  add_lt_add -- tt + tt
  add_lt_add_left -- ff + tt
  add_lt_add_right -- tt + ff

/-! # ≤, - -/

attribute [gcongr]
  sub_le_sub -- tt - tt
  sub_le_sub_left -- ff - tt
  sub_le_sub_right -- tt - ff

/-! # <, - -/

attribute [gcongr]
  sub_lt_sub -- tt - tt
  sub_lt_sub_left -- ff - tt
  sub_lt_sub_right -- tt - ff

/-! # ≤, * -/

attribute [gcongr]
  mul_le_mul' mul_le_mul -- tt * tt
  mul_le_mul_left' mul_le_mul_of_nonneg_left -- ff * tt
  mul_le_mul_right' mul_le_mul_of_nonneg_right -- tt * ff

/-! # <, * -/

attribute [gcongr]
  mul_lt_mul_of_lt_of_lt mul_lt_mul'' -- tt * tt
  mul_lt_mul_left' mul_lt_mul_of_pos_left -- ff * tt
  mul_lt_mul_right' mul_lt_mul_of_pos_right -- tt * ff

/-! # ≤, / -/

protected theorem Nat.div_le_div {a b c d : ℕ} (h1 : a ≤ b) (h2 : d ≤ c) (h3 : d ≠ 0) :
    a / c ≤ b / d :=
  calc a / c ≤ b / c := Nat.div_le_div_right h1
    _ ≤ b / d := Nat.div_le_div_left h2 (Nat.pos_of_ne_zero h3)

/-- See if the term is `a ⊂ b` and the goal is `a ⊆ b`. -/
@[gcongr_forward] def exactSubsetOfSSubset : Mathlib.Tactic.GCongr.ForwardExt where
  eval h goal := do goal.assignIfDefeq (← Lean.Meta.mkAppM ``subset_of_ssubset #[h])

attribute [gcongr]
  div_le_div'' div_le_div Nat.div_le_div -- tt / tt
  div_le_div_left' div_le_div_of_le_left Nat.div_le_div_left -- ff / tt
  div_le_div_right' div_le_div_of_le Nat.div_le_div_right -- tt / ff

/-! # <, / -/

attribute [gcongr]
  div_lt_div'' div_lt_div -- tt / tt
  div_lt_div_left' div_lt_div_of_lt_left -- ff / tt
  div_lt_div_right' div_lt_div_of_lt -- tt / ff

/-! # ≤, ⁻¹ -/

attribute [gcongr]
  inv_le_inv_of_le inv_le_inv' -- tt
  inv_lt_inv_of_lt inv_lt_inv' -- tt

/-! # ≤, ^ -/

attribute [gcongr]
  pow_le_pow_right pow_le_pow_right' zpow_le_zpow zpow_le_of_le -- ff ^ tt
  pow_le_pow_left pow_le_pow_left' zpow_le_zpow' -- tt ^ ff

/-! # <, ^ -/

theorem zpow_lt_of_lt [LinearOrderedSemifield α] {a : α} {m n : ℤ} (hx : 1 < a) (h : m < n) :
    a ^ m < a ^ n :=
  zpow_strictMono hx h

attribute [gcongr]
  pow_lt_pow_right pow_lt_pow_right' zpow_lt_zpow zpow_lt_of_lt -- ff ^ tt
  pow_lt_pow_left zpow_lt_zpow' -- tt ^ ff

/-! # coercions -/

@[gcongr]
theorem Nat.cast_le_cast [OrderedSemiring α] [CharZero α] {x y : ℕ} (h : x ≤ y) : (x:α) ≤ y :=
  Nat.cast_le.mpr h
