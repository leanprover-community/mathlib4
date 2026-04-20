/-
Copyright (c) 2026 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.NonAssoc.PreLie.Basic
/-!
# Dendriform (Semi)Rings and Algebras

## Main definitions
A nonunital dendriform semiring `M` is a `Semiring` where the associative product can be split into
two operations `left : M → M → M` and `right : M → M → M` satisfying
* `left (left a b) c = left a (right b c + left b c)`
* `right a (left b c) = left (right a b) c`
* `right a (right b c) = right (right a b + left a b) c`

These identities ensure that `* := left + right` is indeed associative.
In the literature it is common to denote `left` and `right` as ≺ and ≻, respectively.

Their unital version requires the existence of a unit `1` such that `1 ≻ a = a ≺ 1 = a` and
`1 ≺ a = a ≻ 1 = 0` for all `a ≠ 1`. Note that `1 ≺ 1` and `1 ≻ 1` are left undefined.
This is enough to ensure that `1 * a = a * 1 = 1`. The product `1 * 1` is defined to be `1`.

Dendriform algebras are unital dendriform semirings with an extra module structure over a
commutative semiring `R` such that both `≺` and `≻` are bilinear.

## Main results
Any dendriform ring (algebra) becomes a left or right `PreLieRing` (`PreLieAlgebra`) by
antisymmetrization of operations: either `a ≻ b - b ≺ a` or `a ≺ b - b ≻ a` gives such a structure.

## References
[J.-L. Loday, B. Vallette, *Algebraic Operads*][LV2012]
-/

@[expose] public section

/-- A nonunital nonassociative dendriform semiring is an `AddCommMonoid` with two operations
satisfying certain axioms, such that `a * b = left a b + right a b` is associative. -/
class NonUnitalDendriformSemiring (M) extends AddCommMonoid M where
  /-- The left operation splitting the associative product -/
  left : M → M → M
  /-- The right operation splitting the associative product -/
  right : M → M → M
  left_add_id a b c : left (a + b) c = left a c + left b c
  left_id_add a b c : left a (b + c) = left a b + left a c
  right_add_id a b c : right (a + b) c = right a c + right b c
  right_id_add a b c : right a (b + c) = right a b + right a c
  left_id_zero a : left a 0 = 0
  left_zero_id a : left 0 a = 0
  right_id_zero a : right a 0 = 0
  right_zero_id a : right 0 a = 0
  right_right_eq_mul_right' a b c : right a (right b c) = right (right a b + left a b) c
  right_left_assoc' a b c : right a (left b c) = left (right a b) c
  left_mul_eq_left_left' a b c : left a (right b c + left b c) = left (left a b) c

/-- Notation for the right operation. The symbol points right. -/
infixr:75 " ≻ " => NonUnitalDendriformSemiring.right
/-- Notation for the left operation. The symbol point left. -/
infixr:75 " ≺ " => NonUnitalDendriformSemiring.left

/-- A dendriform semiring is a `NonUnitalDendriformSemiring` where the unit satisfies certain axioms
ensuring that `1 * a = a * 1` for all `a : M`.
-/
class DendriformSemiring (M) extends NonUnitalDendriformSemiring M, One M where
  left_id_one a : a ≠ 1 → left a 1 = a
  left_one_id a : a ≠ 1 →  left 1 a = 0
  right_one_id a : a ≠ 1 → right 1 a = a
  right_id_one a : a ≠ 1 → right a 1 = 0
  one_mul_one_eq_one' : right 1 1 + left 1 1 = 1

namespace NonUnitalDendriformSemiring

variable {M} [NonUnitalDendriformSemiring M]
variable (a b c : M)

instance : Mul M where
  mul a b := a ≻ b + a ≺ b

@[simp]
lemma mul_def : a * b = a ≻ b + a ≺ b := rfl
@[simp]
lemma right_zero : a ≻ 0 = (0 : M) := right_id_zero a

@[simp]
lemma zero_right : 0 ≻ a = (0 : M) := right_zero_id a

@[simp]
lemma left_zero : a ≺ 0 = (0 : M) := left_id_zero a

@[simp]
lemma zero_left : 0 ≺ a = (0 : M) := left_zero_id a

@[simp]
lemma add_right : (a + b) ≻ c = a ≻ c + b ≻ c := right_add_id a b c

@[simp]
lemma right_add : a ≻ (b + c) = a ≻ b + a ≻ c := right_id_add a b c

@[simp]
lemma add_left : (a + b) ≺ c = a ≺ c + b ≺ c := left_add_id a b c

@[simp]
lemma left_add : a ≺ (b + c) = a ≺ b + a ≺ c := left_id_add a b c

@[simp]
lemma right_left_assoc : a ≻ b ≺ c = (a ≻ b) ≺ c := right_left_assoc' a b c

@[simp]
lemma right_right_eq_mul_right : (a ≺ b) ≺ c = a ≺ (b * c) := by simp [← left_mul_eq_left_left']

@[simp]
lemma left_mul_eq_left_left : a ≻ (b ≻ c) = (a * b) ≻ c := by simp [right_right_eq_mul_right']

instance : NonUnitalSemiring M where
  left_distrib a b c := by simpa using by abel_nf
  right_distrib a b c := by simpa using by abel_nf
  zero_mul a := by simp
  mul_zero a := by simp
  mul_assoc a b c := by simpa using by abel_nf

end NonUnitalDendriformSemiring

namespace DendriformSemiring

variable {M} [DendriformSemiring M]

@[simp]
lemma left_one {a : M} (ha : a ≠ 1) : a ≺ 1 = a := left_id_one a ha

@[simp]
lemma one_left {a : M} (ha : a ≠ 1) : 1 ≺ a = 0 := left_one_id a ha

@[simp]
lemma one_right {a : M} (ha : a ≠ 1) : 1 ≻ a = a := right_one_id a ha

@[simp]
lemma right_one {a : M} (ha : a ≠ 1) : a ≻ 1 = 0 := right_id_one a ha

@[simp]
lemma one_mul_one_eq_one : (1 : M) ≻ 1 + 1 ≺ 1 = 1 := one_mul_one_eq_one'


instance : Semiring M where
  one_mul a := by
    rcases eq_or_ne a 1 with (rfl | ha)
    · exact one_mul_one_eq_one
    · simp [one_right ha, one_left ha]
  mul_one a := by 
    rcases eq_or_ne a 1 with (rfl | ha)
    · exact one_mul_one_eq_one
    · simp [right_one ha, left_one ha]

end DendriformSemiring

