/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Algebra.GroupWithZero.Power
import Mathlib.Data.Int.Bitwise

#align_import algebra.group_with_zero.power from "leanprover-community/mathlib"@"46a64b5b4268c594af770c44d9e502afc6a515cb"

/-!
# Powers of elements of groups with an adjoined zero element

We exile two lemmas about `a ^ bit1` here to avoid importing unnecessary material into `ring`.

These lemmas can hopefully be removed entirely later.
-/

section GroupWithZero

variable {G₀ : Type*} [GroupWithZero G₀] {a : G₀} {m n : ℕ}

open Int

set_option linter.deprecated false in
theorem zpow_bit1₀ (a : G₀) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a := by
  rw [← zpow_bit0, bit1, zpow_add', zpow_one]
  right; left
  apply bit1_ne_zero
#align zpow_bit1₀ zpow_bit1₀

set_option linter.deprecated false in
theorem zpow_bit1' (a : G₀) (n : ℤ) : a ^ bit1 n = (a * a) ^ n * a := by
  rw [zpow_bit1₀, (Commute.refl a).mul_zpow]
#align zpow_bit1' zpow_bit1'
