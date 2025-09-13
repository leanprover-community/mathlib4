/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.Ring.Defs
/-!
# Theorems about invertible elements in rings

-/

universe u

variable {R : Type u}

/-- `-⅟a` is the inverse of `-a` -/
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

theorem eq_of_invOf_add_eq_invOf_add_invOf [Ring R] {a b : R} [Invertible a] [Invertible b]
    [Invertible (a + b)] (h : ⅟(a + b) = ⅟a + ⅟b) :
    a * ⅟b * a = b * ⅟a * b := by
  have h_neg_identity : -1 = ⅟a * b + ⅟b * a := by
    have : 1 = 2 + ⅟a * b + ⅟b * a := by
      rw [← invOf_mul_self (a + b), h, add_mul, mul_add, mul_add, invOf_mul_self a,
          invOf_mul_self b, ← add_assoc, add_assoc 1 _, add_comm 1 _, add_assoc 2 _,
          add_comm 2 _, add_assoc, one_add_one_eq_two]
    apply (add_left_inj 2).mp
    conv => lhs; rw [← one_add_one_eq_two, ← add_assoc, neg_add_cancel, zero_add]
    rw [add_comm, ← add_assoc]
    exact this
  let helper {x y : R} [Invertible x] [Invertible y] (h' : -1 = ⅟x * y + ⅟y * x)
      : -(y + x) = x * ⅟y * x := by
    apply (add_left_inj y).mp
    rw [(by simp : -(y + x) + y = -x)]
    conv => rhs; rhs; rw [(by simp : y = x * ⅟x * y)]
    rw [mul_assoc, mul_assoc, ← mul_add x]
    rw [(by simp : -x = x * (-1))]
    apply (mul_right_inj_of_invertible x).mpr
    rw [add_comm]
    exact h'
  have h_a_binv_a : -(b + a) = a * ⅟b * a := by
    exact helper h_neg_identity
  have h_b_ainv_b : -(a + b) = b * ⅟a * b := by
    rw [add_comm] at h_neg_identity
    exact helper h_neg_identity
  rw [← h_a_binv_a, ← h_b_ainv_b, add_comm]

/-- A version of `inv_add_inv'` for `Ring.inverse`. -/
theorem Ring.inverse_add_inverse [Semiring R] {a b : R} (h : IsUnit a ↔ IsUnit b) :
    Ring.inverse a + Ring.inverse b = Ring.inverse a * (a + b) * Ring.inverse b := by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_add_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]

/-- A version of `inv_sub_inv'` for `Ring.inverse`. -/
theorem Ring.inverse_sub_inverse [Ring R] {a b : R} (h : IsUnit a ↔ IsUnit b) :
    Ring.inverse a - Ring.inverse b = Ring.inverse a * (b - a) * Ring.inverse b := by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_sub_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]
