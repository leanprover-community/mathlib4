/-
Copyright (c) 2024 Pieter Cuijpers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pieter Cuijpers
-/
import Mathlib.Order.CompleteLattice
import Mathlib.Algebra.Group.Defs

/-!
# Theory of quantales

Quantales are the non-commutative generalization of locales/frames and as such are linked
to point-free topology and order theory. Applications are found throughout logic,
quantum mechanics, and computer science.

The most general definition of quantale occurring in literature, is that a quantale is a semigroup
distributing over a complete sup-semilattice. In our definition below, we use the fact that
every complete sup-semlattice is in fact a complete lattice, and make construct defined for
those immediately available. Another view could be to define a quantale as a complete idempotent
semiring, i.e. a complete semiring in which + and sup coincide. However, we will often encounter
additive quantales, i.e. quantales in which the semigroup operator is thought of as addition, in
which case the link with semirings will lead to confusion notationally.

In this file, we follow the basic definitions set out on the wikipedia page on quantales,
which also distinguish unital, commutative, idempotent, integral and involutive quantales.
A unital quantale is simply a quantale over a monoid, a commutative quantale is a quantale
over a commutative semigroup, and an idempotent quantale is a quantale over an idempotent
semigroup. As we define quantales relative to their semigroup, these do not need to be defined
explicitly here. An integral (or strictly two-sided) quantale is a unital quantale in which
the top element of the lattice and the unit of the semigroup coincide. We give a mix-in class
definition for this.

The involutive quantale (which is necessary to discuss regularity properties) we do not cover
in this file. Also the proof that every frame is a commutative quantale, and that a quantale is
a frame if and only if it is integral and idempotent are developed separately in order to reduce
overhead if a user does not need them.

## Main definitions

* class `Quantale`: a semigroup distributing over a complete lattice, i.e satisfying
  `x * (sSup s) = ⨆ y ∈ s, x * y` and `(sSup s) * y = ⨆ x ∈ s, x * y`;

* mix-in class `IsIntegral`: a unital quantale (i.e. a quantale in which the semigroup is
  a monoid) is called integral, or strictly two-sided, when `⊤ = 1`;

* next to these classes, we define the additive versions `AddQuantale`, `IsAddIntegral` in
  which the semigroup is denoted `+` i.s.o. `*`;

## Naming conventions

## Notation

* `x ⇨ₗ y` : `sSup { z | z * x ≤ y }`, the left-residuation of `y` over `x`;

* `x ⇨ᵣ y` : `sSup { z | x * z ≤ y }`, the right-residuation of `y` over `x`;

## References

<https://en.wikipedia.org/wiki/Quantale>
<https://encyclopediaofmath.org/wiki/Quantale>
<https://ncatlab.org/nlab/show/quantale>

## TODO

-/

/-- An additive quantale is an additive semigroup distributing over a complete lattice. -/
class AddQuantale (α : Type*) [AddSemigroup α] extends CompleteLattice α where
  /-- Addition is distributive over join in a quantale -/
  protected add_sSup_eq_iSup_add (x : α) (s : Set α) : x + sSup s = ⨆ y ∈ s, x + y
  /-- Addition is distributive over join in a quantale -/
  protected sSup_add_eq_iSup_add (s : Set α) (y : α) : sSup s + y = ⨆ x ∈ s, x + y

/-- A quantale is a semigroup distributing over a complete lattice. -/
@[to_additive]
class Quantale (α : Type*) [Semigroup α] extends CompleteLattice α where
  /-- Multiplication is distributive over join in a quantale -/
  protected mul_sSup_eq_iSup_mul (x : α) (s : Set α) : x * sSup s = ⨆ y ∈ s, x * y
  /-- Multiplication is distributive over join in a quantale -/
  protected sSup_mul_eq_iSup_mul (s : Set α) (y : α) : sSup s * y = ⨆ x ∈ s, x * y

/-- An integral (or strictly two-sided) additive quantale is a quantale over an additive monoid
    where top and unit coincide. -/
class IsAddIntegral (α : Type*) [AddMonoid α] [AddQuantale α] : Prop where
  /-- Top and unit coincide in an integral (or strictly two-sided) quantale -/
  protected top_eq_zero : (⊤ : α) = 0

/-- An integral (or strictly two-sided) quantale is a quantale over a monoid where
    top and unit coincide. -/
@[to_additive]
class IsIntegral (α : Type*) [Monoid α] [Quantale α] : Prop where
  /-- Top and unit coincide in an integral (or strictly two-sided) quantale -/
  protected top_eq_one : (⊤ : α) = 1

section Quantale

variable (α : Type _)
variable [Semigroup α] [Quantale α]

@[to_additive]
theorem mul_sSup_eq_iSup_mul : ∀ x : α, ∀ s : Set α, x * sSup s = ⨆ y ∈ s, x * y :=
  Quantale.mul_sSup_eq_iSup_mul

@[to_additive]
theorem sSup_mul_eq_iSup_mul : ∀ s : Set α, ∀ y : α, sSup s * y = ⨆ x ∈ s, x * y :=
  Quantale.sSup_mul_eq_iSup_mul

end Quantale

section IsIntegral

variable (α : Type _)
variable [Monoid α] [Quantale α] [IsIntegral α]

@[to_additive]
theorem top_eq_one : (⊤ : α) = 1 := IsIntegral.top_eq_one

end IsIntegral

namespace Quantale

variable {α : Type _}
variable [Semigroup α] [Quantale α]

/-- Left- and right- residuation operators on an additive quantale are similar to the Heyting
operator on complete lattices, but for a non-commutative logic.
I.e. `x ⇨ₗ y = sSup { z | z * x ≤ y }`.
-/
@[to_additive "Left- and right- residuation operators on an additive quantale are similar to
the Heyting operator on complete lattices, but for a non-commutative logic.
I.e. `x ⇨ₗ y = sSup { z | z + x ≤ y }`.
"]
def left_residuation (x y : α) := sSup { z | z * x ≤ y }

/-- Left- and right- residuation operators on an additive quantale are similar to the Heyting
operator on complete lattices, but for a non-commutative logic.
I.e. `x ⇨ᵣ y = sSup { z | x * z ≤ y }`.
-/
@[to_additive "Left- and right- residuation operators on an additive quantale are similar to
the Heyting operator on complete lattices, but for a non-commutative logic.
I.e. `x ⇨ᵣ y = sSup { z | x + z ≤ y }`.
"]
def right_residuation (x y : α) := sSup { z | x * z ≤ y }

/-- Notation for left-residuation in quantales.
    I.e. `x ⇨ₗ y = sSup { z | z * x ≤ y }`.
-/
@[to_additive "Notation for left-residuation in quantales.
    I.e. `x ⇨ₗ y = sSup { z | z + x ≤ y }`. "]
scoped infixr:60 " ⇨ₗ " => left_residuation

/-- Notation for right-residuation in quantales.
    I.e. `x ⇨ᵣ y = sSup { z | x * z ≤ y }`.
-/
@[to_additive "Notation for right-residuation in quantales.
    I.e. `x ⇨ᵣ y = sSup { z | x * z ≤ y }`."]
scoped infixr:60 " ⇨ᵣ " => right_residuation

end Quantale
