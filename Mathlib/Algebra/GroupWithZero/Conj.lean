/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.GroupWithZero.Units.Basic

#align_import algebra.group.conj from "leanprover-community/mathlib"@"0743cc5d9d86bcd1bba10f480e948a257d65056f"

/-!
# Conjugacy in a group with zero
-/

assert_not_exists Multiset
-- TODO
-- assert_not_exists DenselyOrdered

variable {α : Type*} [GroupWithZero α] {a b : α}

@[simp] lemma isConj_iff₀ : IsConj a b ↔ ∃ c : α, c ≠ 0 ∧ c * a * c⁻¹ = b := by
  rw [IsConj, Units.exists_iff_ne_zero (p := (SemiconjBy · a b))]
  congr! 2 with c
  exact and_congr_right (mul_inv_eq_iff_eq_mul₀ · |>.symm)
#align is_conj_iff₀ isConj_iff₀
