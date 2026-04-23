/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Init
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
import Mathlib.Tactic.SimpRw
import Mathlib.Util.CompileInductive

/-!
# Theorems about additively and multiplicatively invertible elements in rings

-/

@[expose] public section

open scoped Ring

variable {R : Type*}

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R] (x : AddUnits R) (y : R)

/-- Multiplying an additive unit from the left produces another additive unit. -/
@[simps] def AddUnits.mulLeft : AddUnits R where
  val := y * x.val
  neg := y * x.neg
  val_neg := by simp [← mul_add]
  neg_val := by simp [← mul_add]

/-- Multiplying an additive unit from the right produces another additive unit. -/
@[simps] def AddUnits.mulRight : AddUnits R where
  val := x.val * y
  neg := x.neg * y
  val_neg := by simp [← add_mul]
  neg_val := by simp [← add_mul]

variable {x y}

theorem AddUnits.neg_mulLeft : -(x.mulLeft y) = (-x).mulLeft y := rfl
theorem AddUnits.neg_mulRight : -(x.mulRight y) = (-x).mulRight y := rfl

theorem AddUnits.neg_mul_eq_mul_neg {x y : AddUnits R} : (↑(-x) * y : R) = x * ↑(-y) := by
  rw [← neg_eq_val_neg, ← val_neg_mulRight]
  apply AddUnits.neg_eq_of_add_eq_zero_left
  simp [← mul_add]

theorem AddUnits.neg_mul_neg {x y : AddUnits R} : ↑(-x) * ↑(-y) = (x * y : R) := by
  rw [← val_mulLeft, ← val_mulLeft, ← AddUnits.ext_iff, ← neg_inj, ← y.neg_mulLeft, neg_neg]
  apply AddUnits.ext
  simp [neg_mul_eq_mul_neg]

theorem IsAddUnit.mul_left {x : R} (h : IsAddUnit x) (y : R) : IsAddUnit (y * x) :=
  (h.addUnit.mulLeft y).isAddUnit

theorem IsAddUnit.mul_right {x : R} (h : IsAddUnit x) (y : R) : IsAddUnit (x * y) :=
  (h.addUnit.mulRight y).isAddUnit

end NonUnitalNonAssocSemiring

/-- `-⅟a` is the inverse of `-a` -/
@[implicit_reducible]
def invertibleNeg [Mul R] [One R] [HasDistribNeg R] (a : R) [Invertible a] : Invertible (-a) :=
  ⟨-⅟a, by simp, by simp⟩

@[simp]
theorem invOf_neg [Monoid R] [HasDistribNeg R] (a : R) [Invertible a] [Invertible (-a)] :
    ⅟(-a) = -⅟a :=
  invOf_eq_right_inv (by simp)

@[simp]
theorem one_sub_invOf_two [Ring R] [Invertible (2 : R)] : 1 - (⅟2 : R) = ⅟2 :=
  (isUnit_of_invertible (2 : R)).mul_right_inj.1 <| by
    rw [mul_sub, mul_invOf_self, mul_one, ← one_add_one_eq_two, add_sub_cancel_right]

@[simp]
theorem invOf_two_add_invOf_two [NonAssocSemiring R] [Invertible (2 : R)] :
    (⅟2 : R) + (⅟2 : R) = 1 := by rw [← two_mul, mul_invOf_self]

theorem pos_of_invertible_cast [NonAssocSemiring R] [Nontrivial R] (n : ℕ) [Invertible (n : R)] :
    0 < n :=
  Nat.zero_lt_of_ne_zero fun h => Invertible.ne_zero (n : R) (h ▸ Nat.cast_zero)

theorem invOf_add_invOf [Semiring R] (a b : R) [Invertible a] [Invertible b] :
    ⅟a + ⅟b = ⅟a * (a + b) * ⅟b := by
  rw [mul_add, invOf_mul_self, add_mul, one_mul, mul_assoc, mul_invOf_self, mul_one, add_comm]

/-- A version of `inv_sub_inv'` for `invOf`. -/
theorem invOf_sub_invOf [Ring R] (a b : R) [Invertible a] [Invertible b] :
    ⅟a - ⅟b = ⅟a * (b - a) * ⅟b := by
  rw [mul_sub, invOf_mul_self, sub_mul, one_mul, mul_assoc, mul_invOf_self, mul_one]

lemma neg_add_eq_mul_invOf_mul_same_iff [Ring R] {a b : R} [Invertible a] [Invertible b] :
    -(b + a) = a * ⅟b * a ↔ -1 = ⅟a * b + ⅟b * a :=
  calc -(b + a) = a * ⅟b * a
      ↔ -a = b + a * ⅟b * a := ⟨by grind, fun h ↦ by simp [h]⟩
    _ ↔ -a = a * ⅟a * b + a * ⅟b * a := by rw [mul_invOf_self, one_mul]
    _ ↔ -a = a * (⅟a * b + ⅟b * a) := by simp only [mul_add, mul_assoc]
    _ ↔ -1 = ⅟a * b + ⅟b * a := ⟨fun h ↦ by simpa using congr_arg (⅟a * ·) h, fun h ↦ by simp [← h]⟩

lemma neg_one_eq_invOf_mul_add_invOf_mul_iff [Ring R] {a b : R} [Invertible a]
    [Invertible b] [Invertible (a + b)] : ⅟(a + b) = ⅟a + ⅟b ↔ -1 = ⅟a * b + ⅟b * a := by
  calc ⅟(a + b) = ⅟a + ⅟b
      ↔ ⅟(a + b) * (a + b) = (⅟a + ⅟b) * (a + b) := by rw [mul_left_inj_of_invertible]
    _ ↔ 1 = ⅟a * a + ⅟b * a + (⅟a * b + ⅟b * b) := by rw [invOf_mul_self, mul_add, add_mul, add_mul]
    _ ↔ 1 = 1 + ⅟b * a + (1 + ⅟a * b) := by rw [invOf_mul_self, invOf_mul_self, add_comm _ 1]
    _ ↔ 1 = 1 + 1 + ⅟b * a + ⅟a * b := by rw [← add_assoc, add_comm _ 1, ← add_assoc]
    _ ↔ -2 + 1 = -2 + (2 + ⅟b * a + ⅟a * b) := by rw [one_add_one_eq_two, add_right_inj]
    _ ↔ -2 + 1 = ⅟b * a + ⅟a * b := by rw [← add_assoc, ← add_assoc, neg_add_cancel, zero_add]
    _ ↔ -1 + 0 = ⅟b * a + ⅟a * b := by rw [← one_add_one_eq_two, neg_add, add_assoc, neg_add_cancel]
    _ ↔ -1 = ⅟a * b + ⅟b * a := by rw [add_zero, add_comm]

theorem eq_of_invOf_add_eq_invOf_add_invOf [Ring R] {a b : R} [Invertible a] [Invertible b]
    [Invertible (a + b)] (h : ⅟(a + b) = ⅟a + ⅟b) :
    a * ⅟b * a = b * ⅟a * b := by
  have h' := neg_one_eq_invOf_mul_add_invOf_mul_iff.mp h
  have h_a_binv_a : -(b + a) = a * ⅟b * a := neg_add_eq_mul_invOf_mul_same_iff.mpr h'
  have h_b_ainv_b : -(a + b) = b * ⅟a * b := by
    rw [add_comm] at h'
    exact neg_add_eq_mul_invOf_mul_same_iff.mpr h'
  rw [← h_a_binv_a, ← h_b_ainv_b, add_comm]

/-- A version of `inv_add_inv'` for `Ring.inverse`. -/
theorem Ring.inverse_add_inverse [Semiring R] {a b : R} (h : IsUnit a ↔ IsUnit b) :
    a⁻¹ʳ + b⁻¹ʳ = a⁻¹ʳ * (a + b) * b⁻¹ʳ := by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_add_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]

/-- A version of `inv_sub_inv'` for `Ring.inverse`. -/
theorem Ring.inverse_sub_inverse [Ring R] {a b : R} (h : IsUnit a ↔ IsUnit b) :
    a⁻¹ʳ - b⁻¹ʳ = a⁻¹ʳ * (b - a) * b⁻¹ʳ := by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_sub_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]
