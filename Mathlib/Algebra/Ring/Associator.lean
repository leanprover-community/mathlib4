/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernhard Reinke
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Tactic.Abel

/-!
## Associator in a ring
If `R` is a non-associative ring, then  `(x * y) * z - x * (y * z)` is called the `associator` of
ring elements `x y z : R`. We realize the associator as a map that is an `AddMonoidHom` in each
argument. The associator vanishes exactly when `R` is associative. We prove a similar statement for
semirings by directly comparing the maps `mulLeft₃` and `mulRight₃`, the `AddMonoidHom` versions of
the multiplications `(x * y) * z` and `x * (y * z)`.
-/

universe u

namespace AddMonoidHom

section NonUnitalNonAssocSemiring
variable {R : Type u} [NonUnitalNonAssocSemiring R]

/-- The multiplication `(x * y) * z` of three elements of a (non-associative)
(semi)-ring is an `AddMonoidHom` in each argument. -/
def mulLeft₃ : R →+ R →+ R →+ R where
  toFun x := comp mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' := fun x y => by ext; simp [add_mul]

@[simp]
theorem mulLeft₃_apply (x y z : R) : mulLeft₃ x y z = (x * y) * z := rfl

/-- The multiplication `x * (y * z)` of three elements of a (non-associative)
(semi)-ring is an `AddMonoidHom` in each argument. -/
def mulRight₃ : R →+ R →+ R →+ R where
  toFun x := compr₂ mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' := fun x y => by ext; simp [add_mul]

@[simp]
theorem mulRight₃_apply (x y z : R) : mulRight₃ x y z = x * (y * z) := rfl

/-- An a priori non-associative semiring is associative if the `AddMonoidHom` versions of
the multiplications `(x * y) * z` and `x * (y * z)` agree. -/
theorem associative_iff_mulLeft₃_eq_mulRight₃ : Std.Associative (fun (x y : R) ↦ x * y) ↔
  mulLeft₃ (R := R) = mulRight₃ := by
  constructor
  · rintro ⟨h⟩
    ext x y z
    simp [h x y z]
  · intro h
    apply Std.Associative.mk
    intro x y z
    rw [← mulLeft₃_apply, ← mulRight₃_apply, h]

end NonUnitalNonAssocSemiring

section NonUnitalSemiring
variable {R : Type u} [NonUnitalSemiring R]

theorem mulLeft₃_eq_mulRight₃ : mulLeft₃ (R := R) = mulRight₃ := by
  ext x y z
  simp [mul_assoc]

end NonUnitalSemiring

section NonUnitalNonAssocRing
variable {R : Type u} [NonUnitalNonAssocRing R] (a b c d : R)

/-- The associator for a non-associative ring is `(x * y) * z - x * (y * z)`. It is an
`AddMonoidHom` in each argument. -/
def associator : R →+ R →+ R →+ R := mulLeft₃ - mulRight₃

theorem associator_apply : associator a b c = (a * b) * c - a * (b * c) := rfl

theorem associator_cocycle : a * associator b c d - associator (a * b) c d + associator a (b * c) d
    - associator a b (c * d) + (associator a b c) * d = 0 := by
    simp only [associator, sub_apply, mulLeft₃_apply, mulRight₃_apply, mul_sub, sub_mul]
    abel1

/-- An a priori non-associative ring is associative iff the associator vanishes. -/
theorem associative_iff_associator_eq_zero : Std.Associative (fun (x y : R) ↦ x * y) ↔
  associator (R := R) = 0 := by
  simp [associative_iff_mulLeft₃_eq_mulRight₃, associator, sub_eq_zero]

end NonUnitalNonAssocRing
end AddMonoidHom
