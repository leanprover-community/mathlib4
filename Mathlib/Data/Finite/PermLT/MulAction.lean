/-
Copyright (c) 2024-2025 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Data.Finite.PermLT.Group

/-!
# Multiplicative action of `PermLT` on naturals.
-/
namespace PermLT

variable {n m i j : ℕ} {a b : PermLT n}

instance : FaithfulSMul (PermLT n) ℕ where
  eq_of_smul_eq_smul := by simp_rw [eq_iff_smul_eq_smul, imp_self, implies_true]

instance : MulAction (PermLT n) ℕ where
  one_smul k := by
    simp_rw [smul_eq_iff, getElem_one, implies_true, and_self]
  mul_smul a b k := by
    rcases lt_or_le k n with hkn | hkn
    · simp_rw [smul_of_lt hkn, smul_getElem, getElem_mul]
    · simp_rw [smul_of_ge hkn]

section MulAction

theorem smul_eq_iff_eq_one : (∀ {i : ℕ}, a • i = i) ↔ a = 1 := by
  simp_rw [eq_iff_smul_eq_smul, one_smul]

theorem smul_eq_id_iff_eq_one : ((a • ·) : ℕ → ℕ) = id ↔ a = 1 := by
  simp_rw [funext_iff, id_eq, smul_eq_iff_eq_one]

end MulAction

end PermLT
