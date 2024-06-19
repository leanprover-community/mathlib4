/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.GroupTheory.GroupAction.Units

#align_import algebra.group_with_zero.units.lemmas from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Further lemmas about units in a `MonoidWithZero` or a `GroupWithZero`.

-/

assert_not_exists DenselyOrdered

variable {α M₀ G₀ M₀' G₀' F F' : Type*}
variable [MonoidWithZero M₀]

namespace Commute
variable [GroupWithZero G₀] {a b c d : G₀}

/-- The `MonoidWithZero` version of `div_eq_div_iff_mul_eq_mul`. -/
protected lemma div_eq_div_iff (hbd : Commute b d) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b = c / d ↔ a * d = c * b := hbd.div_eq_div_iff_of_isUnit hb.isUnit hd.isUnit

end Commute

section MonoidWithZero

variable [GroupWithZero G₀] [Nontrivial M₀] [MonoidWithZero M₀'] [FunLike F G₀ M₀]
  [MonoidWithZeroHomClass F G₀ M₀] [FunLike F' G₀ M₀'] [MonoidWithZeroHomClass F' G₀ M₀']
  (f : F) {a : G₀}


theorem map_ne_zero : f a ≠ 0 ↔ a ≠ 0 :=
  ⟨fun hfa ha => hfa <| ha.symm ▸ map_zero f, fun ha => ((IsUnit.mk0 a ha).map f).ne_zero⟩
#align map_ne_zero map_ne_zero

@[simp]
theorem map_eq_zero : f a = 0 ↔ a = 0 :=
  not_iff_not.1 (map_ne_zero f)
#align map_eq_zero map_eq_zero


theorem eq_on_inv₀ (f g : F') (h : f a = g a) : f a⁻¹ = g a⁻¹ := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · rw [inv_zero, map_zero, map_zero]
  · exact (IsUnit.mk0 a ha).eq_on_inv f g h
#align eq_on_inv₀ eq_on_inv₀

end MonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] [GroupWithZero G₀'] [FunLike F G₀ G₀']
  [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (a b : G₀)

/-- A monoid homomorphism between groups with zeros sending `0` to `0` sends `a⁻¹` to `(f a)⁻¹`. -/
@[simp]
theorem map_inv₀ : f a⁻¹ = (f a)⁻¹ := by
  by_cases h : a = 0
  · simp [h, map_zero f]
  · apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, inv_mul_cancel h, map_one]
#align map_inv₀ map_inv₀

@[simp]
theorem map_div₀ : f (a / b) = f a / f b :=
  map_div' f (map_inv₀ f) a b
#align map_div₀ map_div₀

end GroupWithZero

/-- We define the inverse as a `MonoidWithZeroHom` by extending the inverse map by zero
on non-units. -/
noncomputable def MonoidWithZero.inverse {M : Type*} [CommMonoidWithZero M] :
    M →*₀ M where
  toFun := Ring.inverse
  map_zero' := Ring.inverse_zero _
  map_one' := Ring.inverse_one _
  map_mul' x y := (Ring.mul_inverse_rev x y).trans (mul_comm _ _)
#align monoid_with_zero.inverse MonoidWithZero.inverse

@[simp]
theorem MonoidWithZero.coe_inverse {M : Type*} [CommMonoidWithZero M] :
    (MonoidWithZero.inverse : M → M) = Ring.inverse :=
  rfl
#align monoid_with_zero.coe_inverse MonoidWithZero.coe_inverse

@[simp]
theorem MonoidWithZero.inverse_apply {M : Type*} [CommMonoidWithZero M] (a : M) :
    MonoidWithZero.inverse a = Ring.inverse a :=
  rfl
#align monoid_with_zero.inverse_apply MonoidWithZero.inverse_apply

/-- Inversion on a commutative group with zero, considered as a monoid with zero homomorphism. -/
def invMonoidWithZeroHom {G₀ : Type*} [CommGroupWithZero G₀] : G₀ →*₀ G₀ :=
  { invMonoidHom with map_zero' := inv_zero }
#align inv_monoid_with_zero_hom invMonoidWithZeroHom

namespace Units

variable [GroupWithZero G₀]
variable {a b : G₀}

@[simp]
theorem smul_mk0 {α : Type*} [SMul G₀ α] {g : G₀} (hg : g ≠ 0) (a : α) : mk0 g hg • a = g • a :=
  rfl
#align units.smul_mk0 Units.smul_mk0

end Units

/-- If a monoid homomorphism `f` between two `GroupWithZero`s maps `0` to `0`, then it maps `x^n`,
`n : ℤ`, to `(f x)^n`. -/
@[simp]
theorem map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZero G₀'] [FunLike F G₀ G₀']
    [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n : ℤ) : f (x ^ n) = f x ^ n :=
  map_zpow' f (map_inv₀ f) x n
#align map_zpow₀ map_zpow₀
