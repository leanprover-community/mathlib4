/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro, Yaël Dillies
-/
import Mathlib.Algebra.Ring.Defs
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

-- `NeZero` should not be needed in the basic algebraic hierarchy.
assert_not_exists NeZero

-- Check that we have not imported `Mathlib.Tactic.Common` yet.
assert_not_exists Mathlib.Tactic.LibrarySearch.librarySearch

assert_not_exists MonoidHom

open Function Set

universe u

variable {α β K : Type*}

/-- The default definition of the coercion `ℚ≥0 → K` for a division semiring `K`.

`↑q : K` is defined as `(q.num : K) / (q.den : K)`.

Do not use this directly (instances of `DivisionSemiring` are allowed to override that default for
better definitional properties). Instead, use the coercion. -/
def NNRat.castRec [NatCast K] [Div K] (q : ℚ≥0) : K := q.num / q.den

/-- The default definition of the coercion `ℚ → K` for a division ring `K`.

`↑q : K` is defined as `(q.num : K) / (q.den : K)`.

Do not use this directly (instances of `DivisionRing` are allowed to override that default for
better definitional properties). Instead, use the coercion. -/
def Rat.castRec [NatCast K] [IntCast K] [Div K] (q : ℚ) : K := q.num / q.den
#align rat.cast_rec Rat.castRec

#noalign qsmul_rec

/-- A `DivisionSemiring` is a `Semiring` with multiplicative inverses for nonzero elements.

An instance of `DivisionSemiring K` includes maps `nnratCast : ℚ≥0 → K` and `nnqsmul : ℚ≥0 → K → K`.
Those two fields are needed to implement the `DivisionSemiring K → Algebra ℚ≥0 K` instance since we
need to control the specific definitions for some special cases of `K` (in particular `K = ℚ≥0`
itself). See also note [forgetful inheritance].

If the division semiring has positive characteristic `p`, our division by zero convention forces
`nnratCast (1 / p) = 1 / 0 = 0`. -/
class DivisionSemiring (α : Type*) extends Semiring α, GroupWithZero α, NNRatCast α where
  protected nnratCast := NNRat.castRec
  /-- However `NNRat.cast` is defined, it must be propositionally equal to `a / b`.

  Do not use this lemma directly. Use `NNRat.cast_def` instead. -/
  protected nnratCast_def (q : ℚ≥0) : (NNRat.cast q : α) = q.num / q.den := by intros; rfl
  /-- Scalar multiplication by a nonnegative rational number.

  Unless there is a risk of a `Module ℚ≥0 _` instance diamond, write `nnqsmul := _`. This will set
  `nnqsmul` to `(NNRat.cast · * ·)` thanks to unification in the default proof of `nnqsmul_def`.

  Do not use directly. Instead use the `•` notation. -/
  protected nnqsmul : ℚ≥0 → α → α
  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.

  Do not use this lemma directly. Use `NNRat.smul_def` instead. -/
  protected nnqsmul_def (q : ℚ≥0) (a : α) : nnqsmul q a = NNRat.cast q * a := by intros; rfl
#align division_semiring DivisionSemiring

/-- A `DivisionRing` is a `Ring` with multiplicative inverses for nonzero elements.

An instance of `DivisionRing K` includes maps `ratCast : ℚ → K` and `qsmul : ℚ → K → K`.
Those two fields are needed to implement the `DivisionRing K → Algebra ℚ K` instance since we need
to control the specific definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also note [forgetful inheritance]. Similarly, there are maps `nnratCast ℚ≥0 → K` and
`nnqsmul : ℚ≥0 → K → K` to implement the `DivisionSemiring K → Algebra ℚ≥0 K` instance.

If the division ring has positive characteristic `p`, our division by zero convention forces
`ratCast (1 / p) = 1 / 0 = 0`. -/
class DivisionRing (α : Type*)
  extends Ring α, DivInvMonoid α, Nontrivial α, NNRatCast α, RatCast α where
  /-- For a nonzero `a`, `a⁻¹` is a right multiplicative inverse. -/
  protected mul_inv_cancel : ∀ (a : α), a ≠ 0 → a * a⁻¹ = 1
  /-- The inverse of `0` is `0` by convention. -/
  protected inv_zero : (0 : α)⁻¹ = 0
  protected nnratCast := NNRat.castRec
  /-- However `NNRat.cast` is defined, it must be equal to `a / b`.

  Do not use this lemma directly. Use `NNRat.cast_def` instead. -/
  protected nnratCast_def (q : ℚ≥0) : (NNRat.cast q : α) = q.num / q.den := by intros; rfl
  /-- Scalar multiplication by a nonnegative rational number.

  Unless there is a risk of a `Module ℚ≥0 _` instance diamond, write `nnqsmul := _`. This will set
  `nnqsmul` to `(NNRat.cast · * ·)` thanks to unification in the default proof of `nnqsmul_def`.

  Do not use directly. Instead use the `•` notation. -/
  protected nnqsmul : ℚ≥0 → α → α
  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.

  Do not use this lemma directly. Use `NNRat.smul_def` instead. -/
  protected nnqsmul_def (q : ℚ≥0) (a : α) : nnqsmul q a = NNRat.cast q * a := by intros; rfl
  protected ratCast := Rat.castRec
  /-- However `Rat.cast q` is defined, it must be propositionally equal to `q.num / q.den`.

  Do not use this lemma directly. Use `Rat.cast_def` instead. -/
  protected ratCast_def (q : ℚ) : (Rat.cast q : α) = q.num / q.den := by intros; rfl
  /-- Scalar multiplication by a rational number.

  Unless there is a risk of a `Module ℚ _` instance diamond, write `qsmul := _`. This will set
  `qsmul` to `(Rat.cast · * ·)` thanks to unification in the default proof of `qsmul_def`.

  Do not use directly. Instead use the `•` notation. -/
  protected qsmul : ℚ → α → α
  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.

  Do not use this lemma directly. Use `Rat.cast_def` instead. -/
  protected qsmul_def (a : ℚ) (x : α) : qsmul a x = Rat.cast a * x := by intros; rfl
#align division_ring DivisionRing
#align division_ring.rat_cast_mk DivisionRing.ratCast_def

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.toDivisionSemiring [DivisionRing α] : DivisionSemiring α :=
  { ‹DivisionRing α› with }
#align division_ring.to_division_semiring DivisionRing.toDivisionSemiring

/-- A `Semifield` is a `CommSemiring` with multiplicative inverses for nonzero elements.

An instance of `Semifield K` includes maps `nnratCast : ℚ≥0 → K` and `nnqsmul : ℚ≥0 → K → K`.
Those two fields are needed to implement the `DivisionSemiring K → Algebra ℚ≥0 K` instance since we
need to control the specific definitions for some special cases of `K` (in particular `K = ℚ≥0`
itself). See also note [forgetful inheritance].

If the semifield has positive characteristic `p`, our division by zero convention forces
`nnratCast (1 / p) = 1 / 0 = 0`. -/
class Semifield (α : Type*) extends CommSemiring α, DivisionSemiring α, CommGroupWithZero α
#align semifield Semifield

/-- A `Field` is a `CommRing` with multiplicative inverses for nonzero elements.

An instance of `Field K` includes maps `ratCast : ℚ → K` and `qsmul : ℚ → K → K`.
Those two fields are needed to implement the `DivisionRing K → Algebra ℚ K` instance since we need
to control the specific definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also note [forgetful inheritance].

If the field has positive characteristic `p`, our division by zero convention forces
`ratCast (1 / p) = 1 / 0 = 0`. -/
class Field (K : Type u) extends CommRing K, DivisionRing K
#align field Field

-- see Note [lower instance priority]
instance (priority := 100) Field.toSemifield [Field α] : Semifield α := { ‹Field α› with }
#align field.to_semifield Field.toSemifield

namespace NNRat
variable [DivisionSemiring α]

instance (priority := 100) smulDivisionSemiring : SMul ℚ≥0 α := ⟨DivisionSemiring.nnqsmul⟩

lemma cast_def (q : ℚ≥0) : (q : α) = q.num / q.den := DivisionSemiring.nnratCast_def _
lemma smul_def (q : ℚ≥0) (a : α) : q • a = q * a := DivisionSemiring.nnqsmul_def q a

variable (α)

@[simp] lemma smul_one_eq_cast (q : ℚ≥0) : q • (1 : α) = q := by rw [NNRat.smul_def, mul_one]

@[deprecated (since := "2024-05-03")] alias smul_one_eq_coe := smul_one_eq_cast

end NNRat

namespace Rat
variable [DivisionRing K] {a b : K}

lemma cast_def (q : ℚ) : (q : K) = q.num / q.den := DivisionRing.ratCast_def _
#align rat.cast_def Rat.cast_def

lemma cast_mk' (a b h1 h2) : ((⟨a, b, h1, h2⟩ : ℚ) : K) = a / b := cast_def _
#align rat.cast_mk' Rat.cast_mk'

instance (priority := 100) smulDivisionRing : SMul ℚ K :=
  ⟨DivisionRing.qsmul⟩
#align rat.smul_division_ring Rat.smulDivisionRing

theorem smul_def (a : ℚ) (x : K) : a • x = ↑a * x := DivisionRing.qsmul_def a x
#align rat.smul_def Rat.smul_def

@[simp]
theorem smul_one_eq_cast (A : Type*) [DivisionRing A] (m : ℚ) : m • (1 : A) = ↑m := by
  rw [Rat.smul_def, mul_one]
#align rat.smul_one_eq_coe Rat.smul_one_eq_cast

@[deprecated (since := "2024-05-03")] alias smul_one_eq_coe := smul_one_eq_cast

end Rat

/-- `OfScientific.ofScientific` is the simp-normal form. -/
@[simp]
theorem Rat.ofScientific_eq_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    Rat.ofScientific (OfNat.ofNat m) s (OfNat.ofNat e) = OfScientific.ofScientific m s e := rfl
