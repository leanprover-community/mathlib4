/-
Copyright (c) 2024 Pieter Cuijpers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pieter Cuijpers
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.CompleteLattice
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Theory of quantales

Quantales are the non-commutative generalization of locales/frames and as such are linked
to point-free topology and order theory. Applications are found throughout logic,
quantum mechanics, and computer science (see e.g. [Vickers1989] and [Mulvey1986]).

The most general definition of quantale occurring in literature, is that a quantale is a semigroup
distributing over a complete sup-semilattice. In our definition below, we use the fact that
every complete sup-semilattice is in fact a complete lattice, and make constructs defined for
those immediately available. Another view could be to define a quantale as a complete idempotent
semiring, i.e. a complete semiring in which + and sup coincide. However, we will often encounter
additive quantales, i.e. quantales in which the semigroup operator is thought of as addition, in
which case the link with semirings will lead to confusion notationally.

In this file, we follow the basic definitions set out on the wikipedia page on quantales,
which also distinguish unital, commutative, idempotent, integral and involutive quantales.
A unital quantale is simply a quantale over a monoid, a commutative quantale is a quantale
over a commutative semigroup, and an idempotent quantale is a quantale over an idempotent
semigroup. As we define quantales relative to their semigroup, these do not need to be defined
explicitly here, one can simply use a `Monoid`, `CommMonoid`, or `IdemMonoid` while constructing
the quantale. An integral (or strictly two-sided) quantale is a unital quantale in which
the top element of the lattice and the unit of the semigroup coincide. We give a mix-in class
definition `IntegralQuantale` for this.

The involutive quantale (which is necessary to discuss regularity properties) we do not cover
in this file. Also the proof that every frame is a commutative quantale, and that a quantale is
a frame if and only if it is integral and idempotent are developed separately in order to reduce
overhead if a user does not need them.

## Main definitions

* class `Quantale`: a semigroup distributing over a complete lattice, i.e satisfying
  `x * (sSup s) = ⨆ y ∈ s, x * y` and `(sSup s) * y = ⨆ x ∈ s, x * y`;

* `IsIntegralQuantale`: Typeclass mixin for a unital quantale (i.e. a quantale in which the
  semigroup is a monoid) respecting `⊤ = 1` (also called a two-sided quantale);

* next to these classes, we define the additive versions `AddQuantale`, `IsAddIntegral` in
  which the semigroup operation is denoted by addition instead of multiplication;

* furthermore, we provide basic lemmas rewriting distributivity laws for sSup into iSup and sup,
  monotonicity of the multiplication, and basic equivalence theorems for left- and right-
  residuation.

## Naming conventions

## Notation

* `x ⇨ₗ y` : `sSup {z | z * x ≤ y}`, the `leftResiduation` of `y` over `x`;

* `x ⇨ᵣ y` : `sSup {z | x * z ≤ y}`, the `rightResiduation` of `y` over `x`;

## References

<https://en.wikipedia.org/wiki/Quantale>
<https://encyclopediaofmath.org/wiki/Quantale>
<https://ncatlab.org/nlab/show/quantale>

-/

open Function

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
`⊤` and `0` coincide. -/
class IsIntegralAddQuantale (α : Type*) [AddMonoid α] [AddQuantale α] : Prop where
  /-- `⊤` and `1` coincide in an integral (or strictly two-sided) quantale -/
  protected top_eq_zero : (⊤ : α) = 0

/-- An integral (or strictly two-sided) quantale is a quantale over a monoid where
`⊤` and `1` coincide. -/
@[to_additive]
class IsIntegralQuantale (α : Type*) [Monoid α] [Quantale α] : Prop where
  /-- `⊤` and `1` coincide in an integral (or strictly two-sided) quantale -/
  protected top_eq_one : (⊤ : α) = 1

section Quantale

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}
variable [Semigroup α] [Quantale α]

@[to_additive]
theorem mul_sSup_eq_iSup_mul : x * sSup s = ⨆ y ∈ s, x * y := Quantale.mul_sSup_eq_iSup_mul _ _

@[to_additive]
theorem sSup_mul_eq_iSup_mul : sSup s * x = ⨆ y ∈ s, y * x := Quantale.sSup_mul_eq_iSup_mul _ _

@[to_additive]
theorem mul_iSup_eq_iSup_mul : x * ⨆ i, f i = ⨆ i, x * f i := by
  rw [iSup, mul_sSup_eq_iSup_mul, iSup_range]

@[to_additive]
theorem iSup_mul_eq_iSup_mul : (⨆ i, f i) * x = ⨆ i, f i * x := by
  rw [iSup, sSup_mul_eq_iSup_mul, iSup_range]

@[to_additive]
theorem mul_sup_eq_sup_mul : x * (y ⊔ z) = (x * y) ⊔ (x * z) := by
  rw [← iSup_pair, ← sSup_pair, mul_sSup_eq_iSup_mul]

@[to_additive]
theorem sup_mul_eq_sup_mul : (x ⊔ y) * z = (x * z) ⊔ (y * z) := by
  rw [← (@iSup_pair _ _ _ (fun _? => _? * z) _ _), ← sSup_pair, sSup_mul_eq_iSup_mul]

/- There is not general class definition for OrderedMonoid, so we use the more granular
MulLeftMono and MulRightMono class definitions instead to obtain monotonicity theorems. -/

@[to_additive]
instance : MulLeftMono α where
  elim := by
    intro _ _ _; simp only; intro
    rw [← left_eq_sup, ← mul_sup_eq_sup_mul, sup_of_le_left]
    trivial

@[to_additive]
instance : MulRightMono α where
  elim := by
    intro _ _ _; simp only; intro
    rw [← left_eq_sup, ← sup_mul_eq_sup_mul, sup_of_le_left]
    trivial

end Quantale

section IsIntegral
open Quantale

variable {α : Type*}
variable [Monoid α] [Quantale α] [IsIntegralQuantale α]

@[to_additive]
theorem top_eq_one : (⊤ : α) = 1 := IsIntegralQuantale.top_eq_one

end IsIntegral

namespace Quantale

variable {α : Type*}
variable [Semigroup α] [Quantale α]

/-- Left- and right-residuation operators on an additive quantale are similar to the Heyting
operator on complete lattices, but for a non-commutative logic.
I.e. `x ≤ y ⇨ₗ z ↔ x * y ≤ z` or alternatively `x ⇨ₗ y = sSup { z | z * x ≤ y }`.
-/
@[to_additive "Left- and right- residuation operators on an additive quantale are similar to
the Heyting operator on complete lattices, but for a non-commutative logic.
I.e. `x ≤ y ⇨ₗ z ↔ x + y ≤ z` or alternatively `x ⇨ₗ y = sSup { z | z + x ≤ y }`.
"]
def leftResiduation (x y : α) := sSup {z | z * x ≤ y}

/-- Left- and right- residuation operators on an additive quantale are similar to the Heyting
operator on complete lattices, but for a non-commutative logic.
I.e. `x ≤ y ⇨ᵣ z ↔ y * x ≤ z` or alternatively `x ⇨ₗ y = sSup { z | x * z ≤ y }`.
-/
@[to_additive "Left- and right- residuation operators on an additive quantale are similar to
the Heyting operator on complete lattices, but for a non-commutative logic.
I.e. `x ≤ y ⇨ᵣ z ↔ y + x ≤ z` or alternatively `x ⇨ₗ y = sSup { z | x + z ≤ y }`.
"]
def rightResiduation (x y : α) := sSup {z | x * z ≤ y}

@[inherit_doc]
scoped infixr:60 " ⇨ₗ " => leftResiduation

@[inherit_doc]
scoped infixr:60 " ⇨ᵣ " => rightResiduation

end Quantale

namespace AddQuantale

@[inherit_doc]
scoped infixr:60 " ⇨ₗ " => leftResiduation

@[inherit_doc]
scoped infixr:60 " ⇨ᵣ " => rightResiduation

end AddQuantale

namespace Quantale

variable {α : Type*} {x y z : α}
variable [Semigroup α] [Quantale α]

@[to_additive]
theorem leftResiduation_le_iff_mul_le : x ≤ y ⇨ₗ z ↔ x * y ≤ z := by
  rw [leftResiduation];
  constructor
  · intro h1
    apply le_trans (mul_le_mul_right' h1 _)
    apply le_trans (mul_le_mul_right' h1 _)
    simp_all only [sSup_mul_eq_iSup_mul, Set.mem_setOf_eq, iSup_le_iff, implies_true]
  · intro h1
    apply le_sSup
    exact h1

@[to_additive]
theorem rightResiduation_le_iff_mul_le : x ≤ y ⇨ᵣ z ↔ y * x ≤ z := by
  rw [rightResiduation];
  constructor
  · intro h1
    apply le_trans (mul_le_mul_left' h1 _)
    apply le_trans (mul_le_mul_left' h1 _)
    simp_all only [mul_sSup_eq_iSup_mul, Set.mem_setOf_eq, iSup_le_iff, implies_true]
  · intro h1
    apply le_sSup
    exact h1

end Quantale
