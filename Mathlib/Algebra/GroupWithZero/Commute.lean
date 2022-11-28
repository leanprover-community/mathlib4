/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.GroupWithZero.Semiconj
import Mathbin.Algebra.Group.Commute
import Mathbin.Tactic.Nontriviality

/-!
# Lemmas about commuting elements in a `monoid_with_zero` or a `group_with_zero`.

-/


variable {α M₀ G₀ M₀' G₀' F F' : Type _}

variable [MonoidWithZero M₀]

namespace Ring

open Classical

theorem mul_inverse_rev' {a b : M₀} (h : Commute a b) : inverse (a * b) = inverse b * inverse a := by
  by_cases hab : IsUnit (a * b)
  · obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.is_unit_mul_iff.mp hab
    rw [← Units.coe_mul, inverse_unit, inverse_unit, inverse_unit, ← Units.coe_mul, mul_inv_rev]
    
  obtain ha | hb := not_and_distrib.mp (mt h.is_unit_mul_iff.mpr hab)
  · rw [inverse_non_unit _ hab, inverse_non_unit _ ha, mul_zero]
    
  · rw [inverse_non_unit _ hab, inverse_non_unit _ hb, zero_mul]
    
#align ring.mul_inverse_rev' Ring.mul_inverse_rev'

theorem mul_inverse_rev {M₀} [CommMonoidWithZero M₀] (a b : M₀) : Ring.inverse (a * b) = inverse b * inverse a :=
  mul_inverse_rev' (Commute.all _ _)
#align ring.mul_inverse_rev Ring.mul_inverse_rev

end Ring

theorem Commute.ring_inverse_ring_inverse {a b : M₀} (h : Commute a b) : Commute (Ring.inverse a) (Ring.inverse b) :=
  (Ring.mul_inverse_rev' h.symm).symm.trans <| (congr_arg _ h.symm.Eq).trans <| Ring.mul_inverse_rev' h
#align commute.ring_inverse_ring_inverse Commute.ring_inverse_ring_inverse

namespace Commute

/- warning: commute.zero_right -> Commute.zero_right is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_2 : MulZeroClass.{u_3} G₀] (a : G₀), Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ _inst_2) a (OfNat.ofNat.{u_3} G₀ 0 (OfNat.mk.{u_3} G₀ 0 (Zero.zero.{u_3} G₀ (MulZeroClass.toHasZero.{u_3} G₀ _inst_2))))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.Ring.Basic._hyg.11 : Semiring.{u_1} R] (a : R), Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.11))) a (OfNat.ofNat.{u_1} R 0 (Zero.toOfNat0.{u_1} R (MonoidWithZero.toZero.{u_1} R (Semiring.toMonoidWithZero.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.11))))
Case conversion may be inaccurate. Consider using '#align commute.zero_right Commute.zero_rightₓ'. -/
@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : Commute a 0 :=
  SemiconjBy.zero_right a
#align commute.zero_right Commute.zero_right

/- warning: commute.zero_left -> Commute.zero_left is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_2 : MulZeroClass.{u_3} G₀] (a : G₀), Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ _inst_2) (OfNat.ofNat.{u_3} G₀ 0 (OfNat.mk.{u_3} G₀ 0 (Zero.zero.{u_3} G₀ (MulZeroClass.toHasZero.{u_3} G₀ _inst_2)))) a
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.Ring.Basic._hyg.36 : Semiring.{u_1} R] (a : R), Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.36))) (OfNat.ofNat.{u_1} R 0 (Zero.toOfNat0.{u_1} R (MonoidWithZero.toZero.{u_1} R (Semiring.toMonoidWithZero.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.36)))) a
Case conversion may be inaccurate. Consider using '#align commute.zero_left Commute.zero_leftₓ'. -/
@[simp]
theorem zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a :=
  SemiconjBy.zero_left a a
#align commute.zero_left Commute.zero_left

variable [GroupWithZero G₀] {a b c : G₀}

@[simp]
theorem inv_left_iff₀ : Commute a⁻¹ b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff₀
#align commute.inv_left_iff₀ Commute.inv_left_iff₀

theorem inv_left₀ (h : Commute a b) : Commute a⁻¹ b :=
  inv_left_iff₀.2 h
#align commute.inv_left₀ Commute.inv_left₀

@[simp]
theorem inv_right_iff₀ : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff₀
#align commute.inv_right_iff₀ Commute.inv_right_iff₀

theorem inv_right₀ (h : Commute a b) : Commute a b⁻¹ :=
  inv_right_iff₀.2 h
#align commute.inv_right₀ Commute.inv_right₀

@[simp]
theorem div_right (hab : Commute a b) (hac : Commute a c) : Commute a (b / c) :=
  hab.div_right hac
#align commute.div_right Commute.div_right

@[simp]
theorem div_left (hac : Commute a c) (hbc : Commute b c) : Commute (a / b) c := by
  rw [div_eq_mul_inv]
  exact hac.mul_left hbc.inv_left₀
#align commute.div_left Commute.div_left

end Commute

