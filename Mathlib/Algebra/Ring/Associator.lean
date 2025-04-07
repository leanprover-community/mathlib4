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
ring elements `x y z : R`.

The associator vanishes exactly when `R` is associative. We prove a similar statement for the
`AddMonoidHom` bundled version of the associator, as well as for semirings by directly comparing the
maps `mulLeft₃` and `mulRight₃`, the multiplications `(x * y) * z` and `x * (y * z)`, and for their
`AddMonoidHom` versions.
-/

universe u

namespace Mul
variable {R : Type u} [Mul R]

/-- The multiplication `(x * y) * z` -/
def mulLeft₃ (x y z : R) := (x * y) * z

/-- The multiplication `x * (y * z)` -/
def mulRight₃ (x y z : R) := x * (y * z)

@[simp]
theorem mulLeft₃_apply (x y z : R) : mulLeft₃ x y z = (x * y) * z := rfl

@[simp]
theorem mulRight₃_apply (x y z : R) : mulRight₃ x y z = x * (y * z) := rfl

/-- The multiplications `(x * y) * z` and `x * (y * z)` agree iff multiplication is associative. -/
theorem mulLeft₃_eq_mulRight₃_iff_associative :
    mulLeft₃ (R := R) = mulRight₃ ↔ Std.Associative (fun (x y : R) ↦ x * y) where
  mp h := ⟨fun x y z ↦ by rw [← mulLeft₃_apply, ← mulRight₃_apply, h]⟩
  mpr h := by ext x y z; simp [Std.Associative.assoc]
end Mul

namespace NonUnitalNonAssocRing
variable {R : Type u} [NonUnitalNonAssocRing R]
/-- The associator `(x * y) * z - x * (y * z)` -/
def associator (x y z : R) := (x * y) * z - x * (y * z)

theorem associator_eq_mulLeft₃_sub_mulRight₃ :
    associator = Mul.mulLeft₃ (R := R) - Mul.mulRight₃ := by
  funext x y z
  simp [associator]

theorem associative_iff_associator_eq_zero : Std.Associative (fun (x y : R) ↦ x * y) ↔
    associator (R := R) = 0 := by
  simp [Mul.mulLeft₃_eq_mulRight₃_iff_associative, associator_eq_mulLeft₃_sub_mulRight₃,
  sub_eq_zero]

theorem associator_cocycle (a b c d : R):
    a * associator b c d - associator (a * b) c d + associator a (b * c) d - associator a b (c * d)
    + (associator a b c) * d = 0 := by
  simp only [associator, mul_sub, sub_mul]
  abel1

end NonUnitalNonAssocRing

namespace AddMonoidHom

section NonUnitalNonAssocSemiring
variable {R : Type u} [NonUnitalNonAssocSemiring R]

/-- The multiplication `(x * y) * z` of three elements of a (non-associative)
(semi)-ring is an `AddMonoidHom` in each argument. -/
def mulLeft₃ : R →+ R →+ R →+ R where
  toFun x := comp mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_mul]

@[simp]
theorem mulLeft₃_apply (x y z : R) : mulLeft₃ x y z = (x * y) * z := rfl

/-- The multiplication `x * (y * z)` of three elements of a (non-associative)
(semi)-ring is an `AddMonoidHom` in each argument. -/
def mulRight₃ : R →+ R →+ R →+ R where
  toFun x := compr₂ mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_mul]

@[simp]
theorem mulRight₃_apply (x y z : R) : mulRight₃ x y z = x * (y * z) := rfl

/-- An a priori non-associative semiring is associative if the `AddMonoidHom` versions of
the multiplications `(x * y) * z` and `x * (y * z)` agree. -/
theorem mulLeft₃_eq_mulRight₃_iff_associative :
    mulLeft₃ (R := R) = mulRight₃ ↔ Std.Associative (fun (x y : R) ↦ x * y) where
  mp h := ⟨fun x y z ↦ by rw [← mulLeft₃_apply, ← mulRight₃_apply, h]⟩
  mpr h := by ext x y z; simp [Std.Associative.assoc]

end NonUnitalNonAssocSemiring

section NonUnitalSemiring
variable {R : Type u} [NonUnitalSemiring R]

theorem mulLeft₃_eq_mulRight₃ : mulLeft₃ (R := R) = mulRight₃ :=
  mulLeft₃_eq_mulRight₃_iff_associative.2 inferInstance

end NonUnitalSemiring

section NonUnitalNonAssocRing
variable {R : Type u} [NonUnitalNonAssocRing R] (a b c : R)

/-- The associator for a non-associative ring is `(x * y) * z - x * (y * z)`. It is an
`AddMonoidHom` in each argument. -/
def associator : R →+ R →+ R →+ R := mulLeft₃ - mulRight₃

@[simp]
theorem associator_apply : associator a b c = NonUnitalNonAssocRing.associator a b c := rfl

/-- An a priori non-associative ring is associative iff the `AddMonoidHom` version of the
associator vanishes. -/
theorem associative_iff_associator_eq_zero : Std.Associative (fun (x y : R) ↦ x * y) ↔
    associator (R := R) = 0 := by
  simp [mulLeft₃_eq_mulRight₃_iff_associative, associator, sub_eq_zero]

end NonUnitalNonAssocRing
end AddMonoidHom
