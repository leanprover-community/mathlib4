/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/

import Mathlib.Algebra.Ring.Defs
import Std.Data.Rat.Basic
import Mathlib.Data.Rat.Init

#align_import algebra.field.defs from "leanprover-community/mathlib"@"2651125b48fc5c170ab1111afd0817c903b1fc6c"

/-!
# Division (semi)rings and (semi)fields

This file introduces fields and division rings (also known as skewfields) and proves some basic
statements about them. For a more extensive theory of fields, see the `FieldTheory` folder.

## Main definitions

* `DivisionSemiring`: Nontrivial semiring with multiplicative inverses for nonzero elements.
* `DivisionRing`: : Nontrivial ring with multiplicative inverses for nonzero elements.
* `Semifield`: Commutative division semiring.
* `Field`: Commutative division ring.
* `IsField`: Predicate on a (semi)ring that it is a (semi)field, i.e. that the multiplication is
  commutative, that it has more than one element and that all non-zero elements have a
  multiplicative inverse. In contrast to `Field`, which contains the data of a function associating
  to an element of the field its multiplicative inverse, this predicate only assumes the existence
  and can therefore more easily be used to e.g. transfer along ring isomorphisms.

## Implementation details

By convention `0⁻¹ = 0` in a field or division ring. This is due to the fact that working with total
functions has the advantage of not constantly having to check that `x ≠ 0` when writing `x⁻¹`. With
this convention in place, some statements like `(a + b) * c⁻¹ = a * c⁻¹ + b * c⁻¹` still remain
true, while others like the defining property `a * a⁻¹ = 1` need the assumption `a ≠ 0`. If you are
a beginner in using Lean and are confused by that, you can read more about why this convention is
taken in Kevin Buzzard's
[blogpost](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)

A division ring or field is an example of a `GroupWithZero`. If you cannot find
a division ring / field lemma that does not involve `+`, you can try looking for
a `GroupWithZero` lemma instead.

## Tags

field, division ring, skew field, skew-field, skewfield
-/


open Function Set

universe u

variable {α β K : Type*}

/-- The default definition of the coercion `(↑(a : ℚ) : K)` for a division ring `K`
is defined as `(a / b : K) = (a : K) * (b : K)⁻¹`.
Use `coe` instead of `Rat.castRec` for better definitional behaviour.
-/
def Rat.castRec [NatCast K] [IntCast K] [Mul K] [Inv K] : ℚ → K
  | ⟨a, b, _, _⟩ => ↑a * (↑b)⁻¹
#align rat.cast_rec Rat.castRec

/-- The default definition of the scalar multiplication `(a : ℚ) • (x : K)` for a division ring `K`
is given by `a • x = (↑ a) * x`.
Use `(a : ℚ) • (x : K)` instead of `qsmulRec` for better definitional behaviour.
-/
def qsmulRec (coe : ℚ → K) [Mul K] (a : ℚ) (x : K) : K :=
  coe a * x
#align qsmul_rec qsmulRec

/-- A `DivisionSemiring` is a `Semiring` with multiplicative inverses for nonzero elements. -/
class DivisionSemiring (α : Type*) extends Semiring α, GroupWithZero α
#align division_semiring DivisionSemiring

/-- A `DivisionRing` is a `Ring` with multiplicative inverses for nonzero elements.

An instance of `DivisionRing K` includes maps `ratCast : ℚ → K` and `qsmul : ℚ → K → K`.
If the division ring has positive characteristic p, we define `ratCast (1 / p) = 1 / 0 = 0`
for consistency with our division by zero convention.
The fields `ratCast` and `qsmul` are needed to implement the
`algebraRat [DivisionRing K] : Algebra ℚ K` instance, since we need to control the specific
definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also Note [forgetful inheritance].
-/
class DivisionRing (K : Type u) extends Ring K, DivInvMonoid K, Nontrivial K, RatCast K where
  /-- For a nonzero `a`, `a⁻¹` is a right multiplicative inverse. -/
  protected mul_inv_cancel : ∀ (a : K), a ≠ 0 → a * a⁻¹ = 1
  /-- We define the inverse of `0` to be `0`. -/
  protected inv_zero : (0 : K)⁻¹ = 0
  protected ratCast := Rat.castRec
  /-- However `ratCast` is defined, propositionally it must be equal to `a * b⁻¹`. -/
  protected ratCast_mk : ∀ (a : ℤ) (b : ℕ) (h1 h2), Rat.cast ⟨a, b, h1, h2⟩ = a * (b : K)⁻¹ := by
    intros
    rfl
  /-- Multiplication by a rational number. -/
  protected qsmul : ℚ → K → K := qsmulRec Rat.cast
  /-- However `qsmul` is defined,
  propositionally it must be equal to multiplication by `ratCast`. -/
  protected qsmul_eq_mul' : ∀ (a : ℚ) (x : K), qsmul a x = Rat.cast a * x := by
    intros
    rfl
#align division_ring DivisionRing
#align division_ring.rat_cast_mk DivisionRing.ratCast_mk

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.toDivisionSemiring [DivisionRing α] : DivisionSemiring α :=
  { ‹DivisionRing α› with }
#align division_ring.to_division_semiring DivisionRing.toDivisionSemiring

/-- A `Semifield` is a `CommSemiring` with multiplicative inverses for nonzero elements. -/
class Semifield (α : Type*) extends CommSemiring α, DivisionSemiring α, CommGroupWithZero α
#align semifield Semifield

/-- A `Field` is a `CommRing` with multiplicative inverses for nonzero elements.

An instance of `Field K` includes maps `ratCast : ℚ → K` and `qsmul : ℚ → K → K`.
If the field has positive characteristic p, we define `ratCast (1 / p) = 1 / 0 = 0`
for consistency with our division by zero convention.
The fields `ratCast` and `qsmul` are needed to implement the
`algebraRat [DivisionRing K] : Algebra ℚ K` instance, since we need to control the specific
definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also Note [forgetful inheritance].
-/
class Field (K : Type u) extends CommRing K, DivisionRing K
#align field Field

section DivisionRing

variable [DivisionRing K] {a b : K}

namespace Rat

theorem cast_mk' (a b h1 h2) : ((⟨a, b, h1, h2⟩ : ℚ) : K) = a * (b : K)⁻¹ :=
  DivisionRing.ratCast_mk _ _ _ _
#align rat.cast_mk' Rat.cast_mk'

theorem cast_def : ∀ r : ℚ, (r : K) = r.num / r.den
  | ⟨_, _, _, _⟩ => (cast_mk' _ _ _ _).trans (div_eq_mul_inv _ _).symm
#align rat.cast_def Rat.cast_def

instance (priority := 100) smulDivisionRing : SMul ℚ K :=
  ⟨DivisionRing.qsmul⟩
#align rat.smul_division_ring Rat.smulDivisionRing

theorem smul_def (a : ℚ) (x : K) : a • x = ↑a * x :=
  DivisionRing.qsmul_eq_mul' a x
#align rat.smul_def Rat.smul_def

@[simp]
theorem smul_one_eq_coe (A : Type*) [DivisionRing A] (m : ℚ) : m • (1 : A) = ↑m := by
  rw [Rat.smul_def, mul_one]
#align rat.smul_one_eq_coe Rat.smul_one_eq_coe

end Rat

end DivisionRing

section OfScientific

instance DivisionRing.toOfScientific [DivisionRing K] : OfScientific K where
  ofScientific (m : ℕ) (b : Bool) (d : ℕ) := Rat.ofScientific m b d

end OfScientific

section Field

variable [Field K]

-- see Note [lower instance priority]
instance (priority := 100) Field.toSemifield : Semifield K :=
  { ‹Field K› with }
#align field.to_semifield Field.toSemifield

end Field

/-
`NeZero` should not be needed in the basic algebraic hierarchy.
-/
assert_not_exists NeZero

/-
Check that we have not imported `Mathlib.Tactic.Common` yet.
-/
assert_not_exists Mathlib.Tactic.LibrarySearch.librarySearch
