/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Semiconj.Basic

/-!
# Additional lemmas about commuting pairs of elements in monoids

-/

assert_not_exists MonoidWithZero DenselyOrdered

variable {G : Type*}

section Semigroup
variable [Semigroup G] {a b c : G}

open Function

@[to_additive]
lemma SemiconjBy.function_semiconj_mul_left (h : SemiconjBy a b c) :
    Semiconj (a * ·) (b * ·) (c * ·) := fun j ↦ by simp only [← mul_assoc, h.eq]

@[to_additive]
lemma Commute.function_commute_mul_left (h : Commute a b) : Function.Commute (a * ·) (b * ·) :=
  SemiconjBy.function_semiconj_mul_left h

@[to_additive]
lemma SemiconjBy.function_semiconj_mul_right_swap (h : SemiconjBy a b c) :
    Function.Semiconj (· * a) (· * c) (· * b) := fun j ↦ by simp only [mul_assoc, ← h.eq]

@[to_additive]
lemma Commute.function_commute_mul_right (h : Commute a b) : Function.Commute (· * a) (· * b) :=
  SemiconjBy.function_semiconj_mul_right_swap h

end Semigroup

namespace Commute

section DivisionMonoid

variable [DivisionMonoid G] {a b c d : G}

@[to_additive]
protected theorem inv_inv : Commute a b → Commute a⁻¹ b⁻¹ :=
  SemiconjBy.inv_inv_symm

@[to_additive (attr := simp)]
theorem inv_inv_iff : Commute a⁻¹ b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_inv_symm_iff

@[to_additive]
protected theorem div_mul_div_comm (hbd : Commute b d) (hbc : Commute b⁻¹ c) :
    a / b * (c / d) = a * c / (b * d) := by
  simp_rw [div_eq_mul_inv, mul_inv_rev, hbd.inv_inv.symm.eq, hbc.mul_mul_mul_comm]

@[to_additive]
protected theorem mul_div_mul_comm (hcd : Commute c d) (hbc : Commute b c⁻¹) :
    a * b / (c * d) = a / c * (b / d) :=
  (hcd.div_mul_div_comm hbc.symm).symm

@[to_additive]
protected theorem div_div_div_comm (hbc : Commute b c) (hbd : Commute b⁻¹ d) (hcd : Commute c⁻¹ d) :
    a / b / (c / d) = a / c / (b / d) := by
  simp_rw [div_eq_mul_inv, mul_inv_rev, inv_inv, hbd.symm.eq, hcd.symm.eq,
    hbc.inv_inv.mul_mul_mul_comm]

end DivisionMonoid

section Group
variable [Group G] {a b : G}

@[to_additive (attr := simp)]
lemma inv_left_iff : Commute a⁻¹ b ↔ Commute a b := SemiconjBy.inv_symm_left_iff

@[to_additive] alias ⟨_, inv_left⟩ := inv_left_iff

@[to_additive (attr := simp)]
lemma inv_right_iff : Commute a b⁻¹ ↔ Commute a b := SemiconjBy.inv_right_iff

@[to_additive] alias ⟨_, inv_right⟩ := inv_right_iff

@[to_additive]
protected lemma inv_mul_cancel (h : Commute a b) : a⁻¹ * b * a = b := by
  rw [h.inv_left.eq, inv_mul_cancel_right]

@[to_additive]
lemma inv_mul_cancel_assoc (h : Commute a b) : a⁻¹ * (b * a) = b := by
  rw [← mul_assoc, h.inv_mul_cancel]

@[to_additive (attr := simp)]
protected theorem conj_iff (h : G) : Commute (h * a * h⁻¹) (h * b * h⁻¹) ↔ Commute a b :=
  SemiconjBy.conj_iff

@[to_additive]
protected theorem conj (comm : Commute a b) (h : G) : Commute (h * a * h⁻¹) (h * b * h⁻¹) :=
  (Commute.conj_iff h).mpr comm

@[to_additive (attr := simp)]
lemma zpow_right (h : Commute a b) (m : ℤ) : Commute a (b ^ m) := SemiconjBy.zpow_right h m

@[to_additive (attr := simp)]
lemma zpow_left (h : Commute a b) (m : ℤ) : Commute (a ^ m) b := (h.symm.zpow_right m).symm

@[to_additive] lemma zpow_zpow (h : Commute a b) (m n : ℤ) : Commute (a ^ m) (b ^ n) :=
  (h.zpow_left m).zpow_right n

variable (a) (m n : ℤ)

@[to_additive] lemma self_zpow : Commute a (a ^ n) := (Commute.refl a).zpow_right n

@[to_additive] lemma zpow_self : Commute (a ^ n) a := (Commute.refl a).zpow_left n

@[to_additive] lemma zpow_zpow_self : Commute (a ^ m) (a ^ n) := (Commute.refl a).zpow_zpow m n

end Group
end Commute

section Group
variable [Group G]

@[to_additive] lemma pow_inv_comm (a : G) (m n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left.pow_pow _ _

end Group
