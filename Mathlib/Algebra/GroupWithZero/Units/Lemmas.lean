/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.GroupWithZero.Hom

/-!
# Further lemmas about units in a `MonoidWithZero` or a `GroupWithZero`.

-/

assert_not_exists DenselyOrdered MulAction Ring

variable {M M₀ G₀ M₀' G₀' F F' : Type*}
variable [MonoidWithZero M₀]

section Monoid

variable [Monoid M] [GroupWithZero G₀]

lemma isLocalHom_of_exists_map_ne_one [FunLike F G₀ M] [MonoidHomClass F G₀ M] {f : F}
    (hf : ∃ x : G₀, f x ≠ 1) : IsLocalHom f where
  map_nonunit a h := by
    rcases eq_or_ne a 0 with (rfl | h)
    · obtain ⟨t, ht⟩ := hf
      refine (ht ?_).elim
      have := map_mul f t 0
      rw [← one_mul (f (t * 0)), mul_zero] at this
      exact (h.mul_right_cancel this).symm
    · exact ⟨⟨a, a⁻¹, mul_inv_cancel₀ h, inv_mul_cancel₀ h⟩, rfl⟩

instance [GroupWithZero G₀] [FunLike F G₀ M₀] [MonoidWithZeroHomClass F G₀ M₀] [Nontrivial M₀]
    (f : F) : IsLocalHom f :=
  isLocalHom_of_exists_map_ne_one ⟨0, by simp⟩

end Monoid

section GroupWithZero

namespace Commute

variable [GroupWithZero G₀] {a b c d : G₀}

/-- The `MonoidWithZero` version of `div_eq_div_iff_mul_eq_mul`. -/
protected lemma div_eq_div_iff (hbd : Commute b d) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b = c / d ↔ a * d = c * b :=
  hbd.div_eq_div_iff_of_isUnit hb.isUnit hd.isUnit

/-- The `MonoidWithZero` version of `mul_inv_eq_mul_inv_iff_mul_eq_mul`. -/
protected lemma mul_inv_eq_mul_inv_iff (hbd : Commute b d) (hb : b ≠ 0) (hd : d ≠ 0) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b :=
  hbd.mul_inv_eq_mul_inv_iff_of_isUnit hb.isUnit hd.isUnit

/-- The `MonoidWithZero` version of `inv_mul_eq_inv_mul_iff_mul_eq_mul`. -/
protected lemma inv_mul_eq_inv_mul_iff (hbd : Commute b d) (hb : b ≠ 0) (hd : d ≠ 0) :
    b⁻¹ * a = d⁻¹ * c ↔ d * a = b * c :=
  hbd.inv_mul_eq_inv_mul_iff_of_isUnit hb.isUnit hd.isUnit

end Commute

section MulZeroOneClass

variable [GroupWithZero G₀] [MulZeroOneClass M₀'] [Nontrivial M₀'] [FunLike F G₀ M₀']
  [MonoidWithZeroHomClass F G₀ M₀']
  (f : F) {a : G₀}

theorem map_ne_zero : f a ≠ 0 ↔ a ≠ 0 := by
  refine ⟨fun hfa ha => hfa <| ha.symm ▸ map_zero f, ?_⟩
  intro hx H
  lift a to G₀ˣ using isUnit_iff_ne_zero.mpr hx
  apply one_ne_zero (α := M₀')
  rw [← map_one f, ← Units.mul_inv a, map_mul, H, zero_mul]

@[simp]
theorem map_eq_zero : f a = 0 ↔ a = 0 :=
  not_iff_not.1 (map_ne_zero f)

end MulZeroOneClass

section MonoidWithZero

variable [GroupWithZero G₀] [Nontrivial M₀] [MonoidWithZero M₀'] [FunLike F G₀ M₀]
  [MonoidWithZeroHomClass F G₀ M₀] [FunLike F' G₀ M₀']
  (f : F) {a : G₀}

theorem eq_on_inv₀ [MonoidWithZeroHomClass F' G₀ M₀'] (f g : F') (h : f a = g a) :
    f a⁻¹ = g a⁻¹ := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · rw [inv_zero, map_zero, map_zero]
  · exact (IsUnit.mk0 a ha).eq_on_inv f g h

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
    rw [← map_mul, inv_mul_cancel₀ h, map_one]

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

/-- If a monoid homomorphism `f` between two `GroupWithZero`s maps `0` to `0`, then it maps `x^n`,
`n : ℤ`, to `(f x)^n`. -/
@[simp]
theorem map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZero G₀'] [FunLike F G₀ G₀']
    [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n : ℤ) : f (x ^ n) = f x ^ n :=
  map_zpow' f (map_inv₀ f) x n

end GroupWithZero
