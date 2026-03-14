/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.Semiconj
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Tactic.Nontriviality

/-!
# Lemmas about commuting elements in a `MonoidWithZero` or a `GroupWithZero`.

-/

public section

assert_not_exists DenselyOrdered Ring

variable {M₀ G₀ : Type*}
variable [MonoidWithZero M₀]

namespace Ring

theorem mul_inverse_rev' {a b : M₀} (h : Commute a b) :
    inverse (a * b) = inverse b * inverse a := by
  by_cases hab : IsUnit (a * b)
  · obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.isUnit_mul_iff.mp hab
    rw [← Units.val_mul, inverse_unit, inverse_unit, inverse_unit, ← Units.val_mul, mul_inv_rev]
  obtain ha | hb := not_and_or.mp (mt h.isUnit_mul_iff.mpr hab)
  · rw [inverse_non_unit _ hab, inverse_non_unit _ ha, mul_zero]
  · rw [inverse_non_unit _ hab, inverse_non_unit _ hb, zero_mul]

theorem mul_inverse_rev {M₀} [CommMonoidWithZero M₀] (a b : M₀) :
    (a * b)⁻¹ʳ = b⁻¹ʳ * a⁻¹ʳ :=
  mul_inverse_rev' (Commute.all _ _)

lemma inverse_pow (r : M₀) : ∀ n : ℕ, r⁻¹ʳ ^ n= (r ^ n)⁻¹ʳ
  | 0 => by rw [pow_zero, pow_zero, Ring.inverse_one]
  | n + 1 => by
    rw [pow_succ', pow_succ, Ring.mul_inverse_rev' ((Commute.refl r).pow_left n),
      Ring.inverse_pow r n]

lemma inverse_pow_mul_eq_iff_eq_mul {a : M₀} (b c : M₀) (ha : IsUnit a) {k : ℕ} :
    a⁻¹ʳ ^ k * b = c ↔ b = a ^ k * c := by
  rw [Ring.inverse_pow, Ring.inverse_mul_eq_iff_eq_mul _ _ _ (IsUnit.pow _ ha)]

end Ring

@[grind ←]
theorem Commute.ringInverse_ringInverse {a b : M₀} (h : Commute a b) :
    Commute a⁻¹ʳ b⁻¹ʳ :=
  (Ring.mul_inverse_rev' h.symm).symm.trans <| (congr_arg _ h.symm.eq).trans <|
    Ring.mul_inverse_rev' h

namespace Commute

@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : Commute a 0 :=
  SemiconjBy.zero_right a

@[simp]
theorem zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a :=
  SemiconjBy.zero_left a a

variable [GroupWithZero G₀] {a b c : G₀}

@[simp]
theorem inv_left_iff₀ : Commute a⁻¹ b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff₀

theorem inv_left₀ (h : Commute a b) : Commute a⁻¹ b :=
  inv_left_iff₀.2 h

@[simp]
theorem inv_right_iff₀ : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff₀

theorem inv_right₀ (h : Commute a b) : Commute a b⁻¹ :=
  inv_right_iff₀.2 h

@[simp]
theorem div_right (hab : Commute a b) (hac : Commute a c) : Commute a (b / c) :=
  SemiconjBy.div_right hab hac

@[simp]
theorem div_left (hac : Commute a c) (hbc : Commute b c) : Commute (a / b) c := by
  rw [div_eq_mul_inv]
  exact hac.mul_left hbc.inv_left₀

end Commute

section GroupWithZero
variable [GroupWithZero G₀]

theorem pow_inv_comm₀ (a : G₀) (m n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left₀.pow_pow m n

end GroupWithZero
