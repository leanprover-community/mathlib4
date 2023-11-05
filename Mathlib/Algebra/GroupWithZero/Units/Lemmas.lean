/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.GroupTheory.GroupAction.Units

#align_import algebra.group_with_zero.units.lemmas from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Further lemmas about units in a `MonoidWithZero` or a `GroupWithZero`.

-/


variable {α M₀ G₀ M₀' G₀' F F' : Type*}

variable [MonoidWithZero M₀]

section GroupWithZero

variable [GroupWithZero G₀] {a b c : G₀}

@[simp]
theorem div_self (h : a ≠ 0) : a / a = 1 :=
  IsUnit.div_self h.isUnit

theorem eq_mul_inv_iff_mul_eq₀ (hc : c ≠ 0) : a = b * c⁻¹ ↔ a * c = b :=
  IsUnit.eq_mul_inv_iff_mul_eq hc.isUnit

theorem eq_inv_mul_iff_mul_eq₀ (hb : b ≠ 0) : a = b⁻¹ * c ↔ b * a = c :=
  IsUnit.eq_inv_mul_iff_mul_eq hb.isUnit

theorem inv_mul_eq_iff_eq_mul₀ (ha : a ≠ 0) : a⁻¹ * b = c ↔ b = a * c :=
  IsUnit.inv_mul_eq_iff_eq_mul ha.isUnit

theorem mul_inv_eq_iff_eq_mul₀ (hb : b ≠ 0) : a * b⁻¹ = c ↔ a = c * b :=
  IsUnit.mul_inv_eq_iff_eq_mul hb.isUnit

theorem mul_inv_eq_one₀ (hb : b ≠ 0) : a * b⁻¹ = 1 ↔ a = b :=
  IsUnit.mul_inv_eq_one hb.isUnit

theorem inv_mul_eq_one₀ (ha : a ≠ 0) : a⁻¹ * b = 1 ↔ a = b :=
  IsUnit.inv_mul_eq_one ha.isUnit

theorem mul_eq_one_iff_eq_inv₀ (hb : b ≠ 0) : a * b = 1 ↔ a = b⁻¹ :=
  IsUnit.mul_eq_one_iff_eq_inv hb.isUnit

theorem mul_eq_one_iff_inv_eq₀ (ha : a ≠ 0) : a * b = 1 ↔ a⁻¹ = b :=
  IsUnit.mul_eq_one_iff_inv_eq ha.isUnit

@[simp]
theorem div_mul_cancel (a : G₀) (h : b ≠ 0) : a / b * b = a :=
  IsUnit.div_mul_cancel h.isUnit _

@[simp]
theorem mul_div_cancel (a : G₀) (h : b ≠ 0) : a * b / b = a :=
  IsUnit.mul_div_cancel h.isUnit _

theorem mul_one_div_cancel (h : a ≠ 0) : a * (1 / a) = 1 :=
  IsUnit.mul_one_div_cancel h.isUnit

theorem one_div_mul_cancel (h : a ≠ 0) : 1 / a * a = 1 :=
  IsUnit.one_div_mul_cancel h.isUnit

theorem div_left_inj' (hc : c ≠ 0) : a / c = b / c ↔ a = b :=
  IsUnit.div_left_inj hc.isUnit

@[field_simps]
theorem div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b :=
  IsUnit.div_eq_iff hb.isUnit

@[field_simps]
theorem eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a :=
  IsUnit.eq_div_iff hb.isUnit

theorem div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a :=
  (IsUnit.div_eq_iff hb.isUnit).trans eq_comm

theorem eq_div_iff_mul_eq (hc : c ≠ 0) : a = b / c ↔ a * c = b :=
  IsUnit.eq_div_iff hc.isUnit

theorem div_eq_of_eq_mul (hb : b ≠ 0) : a = c * b → a / b = c :=
  IsUnit.div_eq_of_eq_mul hb.isUnit

theorem eq_div_of_mul_eq (hc : c ≠ 0) : a * c = b → a = b / c :=
  IsUnit.eq_div_of_mul_eq hc.isUnit

theorem div_eq_one_iff_eq (hb : b ≠ 0) : a / b = 1 ↔ a = b :=
  IsUnit.div_eq_one_iff_eq hb.isUnit

theorem div_mul_left (hb : b ≠ 0) : b / (a * b) = 1 / a :=
  IsUnit.div_mul_left hb.isUnit

theorem mul_div_mul_right (a b : G₀) (hc : c ≠ 0) : a * c / (b * c) = a / b :=
  IsUnit.mul_div_mul_right hc.isUnit _ _

theorem mul_mul_div (a : G₀) (hb : b ≠ 0) : a = a * b * (1 / b) :=
  (IsUnit.mul_mul_div _ hb.isUnit).symm

theorem div_div_div_cancel_right (a : G₀) (hc : c ≠ 0) : a / c / (b / c) = a / b := by
  rw [div_div_eq_mul_div, div_mul_cancel _ hc]

theorem div_mul_div_cancel (a : G₀) (hc : c ≠ 0) : a / c * (c / b) = a / b := by
  rw [← mul_div_assoc, div_mul_cancel _ hc]

theorem div_mul_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a / b * b = a :=
  Classical.by_cases (fun hb : b = 0 => by simp [*]) (div_mul_cancel a)

theorem mul_div_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a * b / b = a :=
  Classical.by_cases (fun hb : b = 0 => by simp [*]) (mul_div_cancel a)

@[simp]
theorem divp_mk0 (a : G₀) {b : G₀} (hb : b ≠ 0) : a /ₚ Units.mk0 b hb = a / b :=
  divp_eq_div _ _

end GroupWithZero

section CommGroupWithZero

-- comm
variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem div_mul_right (b : G₀) (ha : a ≠ 0) : a / (a * b) = 1 / b :=
  IsUnit.div_mul_right ha.isUnit _

theorem mul_div_cancel_left_of_imp {a b : G₀} (h : a = 0 → b = 0) : a * b / a = b := by
  rw [mul_comm, mul_div_cancel_of_imp h]

theorem mul_div_cancel_left (b : G₀) (ha : a ≠ 0) : a * b / a = b :=
  IsUnit.mul_div_cancel_left ha.isUnit _

theorem mul_div_cancel_of_imp' {a b : G₀} (h : b = 0 → a = 0) : b * (a / b) = a := by
  rw [mul_comm, div_mul_cancel_of_imp h]

theorem mul_div_cancel' (a : G₀) (hb : b ≠ 0) : b * (a / b) = a :=
  IsUnit.mul_div_cancel' hb.isUnit _

theorem mul_div_mul_left (a b : G₀) (hc : c ≠ 0) : c * a / (c * b) = a / b :=
  IsUnit.mul_div_mul_left hc.isUnit _ _

theorem mul_eq_mul_of_div_eq_div (a : G₀) {b : G₀} (c : G₀) {d : G₀} (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a / b = c / d) : a * d = c * b := by
  rw [← mul_one a, ← div_self hb, ← mul_comm_div, h, div_mul_eq_mul_div, div_mul_cancel _ hd]

@[field_simps]
theorem div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
  IsUnit.div_eq_div_iff hb.isUnit hd.isUnit

theorem div_div_cancel' (ha : a ≠ 0) : a / (a / b) = b :=
  IsUnit.div_div_cancel ha.isUnit

theorem div_div_cancel_left' (ha : a ≠ 0) : a / b / a = b⁻¹ :=
  ha.isUnit.div_div_cancel_left

theorem div_helper (b : G₀) (h : a ≠ 0) : 1 / (a * b) * a = 1 / b := by
  rw [div_mul_eq_mul_div, one_mul, div_mul_right _ h]

theorem div_div_div_cancel_left' (a b : G₀) (hc : c ≠ 0) : c / a / (c / b) = b / a := by
  rw [div_div_div_eq, mul_comm, mul_div_mul_right _ _ hc]

end CommGroupWithZero

section MonoidWithZero

variable [GroupWithZero G₀] [Nontrivial M₀] [MonoidWithZero M₀'] [MonoidWithZeroHomClass F G₀ M₀]
  [MonoidWithZeroHomClass F' G₀ M₀'] (f : F) {a : G₀}


theorem map_ne_zero : f a ≠ 0 ↔ a ≠ 0 :=
  ⟨fun hfa ha => hfa <| ha.symm ▸ map_zero f, fun ha => ((IsUnit.mk0 a ha).map f).ne_zero⟩

@[simp]
theorem map_eq_zero : f a = 0 ↔ a = 0 :=
  not_iff_not.1 (map_ne_zero f)


theorem eq_on_inv₀ (f g : F') (h : f a = g a) : f a⁻¹ = g a⁻¹ := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · rw [inv_zero, map_zero, map_zero]
  · exact (IsUnit.mk0 a ha).eq_on_inv f g h

end MonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] [GroupWithZero G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (a b : G₀)

/-- A monoid homomorphism between groups with zeros sending `0` to `0` sends `a⁻¹` to `(f a)⁻¹`. -/
@[simp]
theorem map_inv₀ : f a⁻¹ = (f a)⁻¹ := by
  by_cases h : a = 0
  · simp [h, map_zero f]
  · apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, inv_mul_cancel h, map_one]

@[simp]
theorem map_div₀ : f (a / b) = f a / f b :=
  map_div' f (map_inv₀ f) a b

end GroupWithZero

/-- We define the inverse as a `MonoidWithZeroHom` by extending the inverse map by zero
on non-units. -/
noncomputable def MonoidWithZero.inverse {M : Type*} [CommMonoidWithZero M] :
    M →*₀ M where
  toFun := Ring.inverse
  map_zero' := Ring.inverse_zero _
  map_one' := Ring.inverse_one _
  map_mul' x y := (Ring.mul_inverse_rev x y).trans (mul_comm _ _)

@[simp]
theorem MonoidWithZero.coe_inverse {M : Type*} [CommMonoidWithZero M] :
    (MonoidWithZero.inverse : M → M) = Ring.inverse :=
  rfl

@[simp]
theorem MonoidWithZero.inverse_apply {M : Type*} [CommMonoidWithZero M] (a : M) :
    MonoidWithZero.inverse a = Ring.inverse a :=
  rfl

/-- Inversion on a commutative group with zero, considered as a monoid with zero homomorphism. -/
def invMonoidWithZeroHom {G₀ : Type*} [CommGroupWithZero G₀] : G₀ →*₀ G₀ :=
  { invMonoidHom with map_zero' := inv_zero }

namespace Units

variable [GroupWithZero G₀]

variable {a b : G₀}

@[simp]
theorem smul_mk0 {α : Type*} [SMul G₀ α] {g : G₀} (hg : g ≠ 0) (a : α) : mk0 g hg • a = g • a :=
  rfl

end Units

/-- If a monoid homomorphism `f` between two `GroupWithZero`s maps `0` to `0`, then it maps `x^n`,
`n : ℤ`, to `(f x)^n`. -/
@[simp]
theorem map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZero G₀']
    [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n : ℤ) : f (x ^ n) = f x ^ n :=
  map_zpow' f (map_inv₀ f) x n
