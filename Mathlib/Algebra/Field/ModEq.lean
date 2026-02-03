/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.ModEq
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.MinImports

/-!
# Congruence modulo multiples of an element in a (semi)field

In this file we prove a few theorems about the congruence relation `_ ≡ _ [PMOD _]`
in a division semiring or a semifield.
-/

public section

namespace AddCommGroup

section DivisionSemiring
variable {K : Type*} [DivisionSemiring K] {a b c p : K}

@[simp] lemma div_modEq_div (hc : c ≠ 0) : a / c ≡ b / c [PMOD p] ↔ a ≡ b [PMOD (p * c)] := by
  simp [modEq_iff_nsmul, add_div' _ _ _ hc, div_left_inj' hc, mul_assoc]

@[simp] lemma mul_modEq_mul_right (hc : c ≠ 0) : a * c ≡ b * c [PMOD p] ↔ a ≡ b [PMOD (p / c)] := by
  rw [div_eq_mul_inv, ← div_modEq_div (inv_ne_zero hc), div_inv_eq_mul, div_inv_eq_mul]

end DivisionSemiring

section Semifield
variable {K : Type*} [Semifield K] {a b c p : K}

@[simp] lemma mul_modEq_mul_left (hc : c ≠ 0) : c * a ≡ c * b [PMOD p] ↔ a ≡ b [PMOD (p / c)] := by
  simp [mul_comm c, hc]

end Semifield
end AddCommGroup
