/-
Copyright (c) 2024 Pieter Cuijpers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pieter Cuijpers
-/
import Mathlib.Order.CompleteLattice
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Idem

/-!
# Theory of quantales

Quantales are the non-commutative generalization of locales/frames and as such are linked
to point-free topology and order theory. Applications are found throughout logic,
quantum mechanics, and computer science.

Intuitively, as described by [vickers1989], open sets of a topology form a frame, and can be
considered as modeling what is `observable` in a system. In behavioral systems theory, quantales
come into play when making an observation may change the system itself. Traditionally, one would
write `x ⊓ y` to describe making observations `x` and `y` at the same time, but when the order of
observation becomes important due to changes in the system caused by the observation, it makes
more sense to write `x * y` or `x + y` and consider `*` or `+` as a possibly non-commutative
(additive) monoid.

In literature, there are slight variations regarding the basic definition of quantale.
The most general definition, is that a quantale is a semigroup distributing over a complete
sup-semilattice. In some works (like in the Wikipedia definition), it is taken to be a semigroup
distributing over a complete lattice. This is an equivalent definition in the sense that every
complete sup-semilattice is a complete lattice, but in further elaborations it allows the user
to also consider the meet `⊓` and infinite meet `⨅` as available operations - while these are
usually not preserved by quantale morphisms. Finally, in many works only unital quantales are
considered, i.e. quantales for which the semigroup operation has a unit element. In those works
a quantale is defined as a monoid distributing over a complete (sup-semi)lattice.

Our definitions below take a quantale to be a semigroup distributing over a complete lattice,
in order to be maximally generic but at the same time efficient in providing all theorems and
definitions one might at some point want to have available on quantales. Furthermore, we
follow the wikipedia page on quantales and give the definitions for integral, commutative,
and idempotent quantale.

## Main definitions

* class `Quantale`: a semigroup distributing over a complete lattice, i.e satisfying
  `x * (sSup s) = ⨆ y ∈ s, x * y` and `(sSup s) * y = ⨆ x ∈ s, x * y`;

* class `OneQuantale`: is a unital quantale, i.e. a monoid distributing over a complete lattice;

* class `IntegralQuantale`: a unital quantale where `⊤ = 1`, also called a strictly
  two-sided quantale;

* class `CommQuantale`: a quantale with a commutative semigroup, iu.e. `x * y = y * x`;

* class `IdemQuantale`: a quantale with an idempotent semigroup, i.e. `x * x = x`;

* class `IdemIntegralQuantale`: a idempotent integral quantale. A quantale is a frame if
  and only if it is idempotent and integral. In that case, it is also commutative
  and ⊓ and * coincide;

* next to these classes, we define the additive versions `AddQuantale`, `UnitalAddQuantale`,
  `AddCommQuantale`, `IdemAddQuantale`, `IntegralAddQuantale`, `IdemIntegralAddQuantale`,
  in which the semigroup operation is written as `+` i.s.o. `*`. In the definitions below
  these additive versions are defined first in order to support the `to_additive` attribute;

## Naming conventions

## Notation

* `x ⇨ₗ y` : `sSup { z | z * x ≤ y }`, the left-residuation of `y` over `x`;

* `x ⇨ᵣ y` : `sSup { z | x * z ≤ y }`, the right-residuation of `y` over `x`;

## References

[Topology via Logic][vickers1989]
<https://en.wikipedia.org/wiki/Quantale>
<https://encyclopediaofmath.org/wiki/Quantale>
<https://ncatlab.org/nlab/show/quantale> (Categorical definition - not followed here)

## TODO

+ A proof that `IdemIntegralQuantale` and `Order.Frame` coincide (probably in a different file);

+ Definition of residuation also for AddQuantale;

+ Definition of involutive quantale;

-/

/-- An additive quantale is an additive semigroup distributing over a complete lattice. -/
class AddQuantale (α : Type*) extends AddSemigroup α, CompleteLattice α where
  /-- Addition is distributive over join in a quantale -/
  protected add_sSup_eq_iSup_add (x : α) (s : Set α) : x + sSup s = ⨆ y ∈ s, x + y
  /-- Addition is distributive over join in a quantale -/
  protected sSup_add_eq_iSup_add (s : Set α) (y : α) : sSup s + y = ⨆ x ∈ s, x + y

/-- A quantale is a semigroup distributing over a complete lattice. -/
@[to_additive]
class Quantale (α : Type*) extends Semigroup α, CompleteLattice α where
  /-- Multiplication is distributive over join in a quantale -/
  protected mul_sSup_eq_iSup_mul (x : α) (s : Set α) : x * sSup s = ⨆ y ∈ s, x * y
  /-- Multiplication is distributive over join in a quantale -/
  protected sSup_mul_eq_iSup_mul (s : Set α) (y : α) : sSup s * y = ⨆ x ∈ s, x * y

/-- A unital additive quantale is a quantale with a unit element, i.e. a monoid -/
class ZeroAddQuantale (α : Type*) extends AddQuantale α, AddMonoid α

/-- A unital quantale is a quantale with a unit element, i.e. a monoid -/
@[to_additive]
class OneQuantale (α : Type*) extends Quantale α, Monoid α

/-- An integral (or strictly two-sided) additive quantale is an additive quantale with `⊤ = 0` -/
class AddIntegralQuantale (α : Type*) extends ZeroAddQuantale α where
  /-- Top and unit coincide in an integral (or strictly two-sided) quantale -/
  protected top_eq_zero : (⊤ : α) = 0

/-- An integral (or strictly two-sided) quantale is a quantale with `⊤ = 1` -/
@[to_additive]
class IntegralQuantale (α : Type*) extends OneQuantale α where
  /-- Top and unit coincide in an integral (or strictly two-sided) quantale -/
  protected top_eq_one : (⊤ : α) = 1

/-- A additive commutative quantale is an additive quantale such that `x + y = y + x` -/
class AddCommQuantale (α : Type*) extends AddQuantale α, CommSemigroup α

/-- A commutative quantale is a quantale such that `x * y = y * x` -/
@[to_additive]
class CommQuantale (α : Type*) extends Quantale α, CommSemigroup α

/-- An idempotent additive quantale is a quantale such that `x + x = x` -/
class AddIdemQuantale (α : Type*) extends AddQuantale α, AddIdemSemigroup α

/-- An idempotent quantale is a quantale such that `x * x = x` -/
@[to_additive]
class IdemQuantale (α : Type*) extends Quantale α, IdemSemigroup α

/-- An idempotent integral additive quantale is an idempotent additive quantale as well as
    an integral quantale. A basic result from quantale theory is that such a quantale is
    also commutative and, in fact, is a frame. I.e. the addition and infimum coinicide.
-/
class AddIdemIntegralQuantale (α : Type*) extends AddIdemQuantale α, AddIntegralQuantale α

/-- An idempotent integral quantale is an idempotent quantale as well as an integral
    quantale. A basic result from quantale theory is that such a quantale is also
    commutative and, in fact, is a frame. I.e. the multiplication and infimum coinicide.
-/
@[to_additive]
class IdemIntegralQuantale (α : Type*) extends IdemQuantale α, IntegralQuantale α

section Quantale

variable (α : Type _)
variable [Quantale α]

@[to_additive]
theorem mul_sSup_eq_iSup_mul : ∀ x : α, ∀ s : Set α, x * sSup s = ⨆ y ∈ s, x * y :=
  Quantale.mul_sSup_eq_iSup_mul

@[to_additive]
theorem sSup_mul_eq_iSup_mul : ∀ s : Set α, ∀ y : α, sSup s * y = ⨆ x ∈ s, x * y :=
  Quantale.sSup_mul_eq_iSup_mul

end Quantale

section IntegralQuantale

variable (α : Type _)
variable [IntegralQuantale α]

@[to_additive]
theorem top_eq_one : (⊤ : α) = 1 := IntegralQuantale.top_eq_one

end IntegralQuantale

namespace Quantale

variable {α : Type _}
variable [Quantale α]

/-- Left- and right- residuation operators on a quantale are similar to the Heyting operator
on complete lattices, but for a non-commutative logic.
I.e. `x ⇨ₗ y = sSup { z | z * x ≤ y }`.
-/
@[to_additive]
def left_residuation (x y : α) := sSup { z | z * x ≤ y }

/-- Notation for left-residuation in quantales.
    I.e. `x ⇨ₗ y = sSup { z | z * x ≤ y }`.
-/
@[to_additive]
scoped infixr:60 " ⇨ₗ " => left_residuation

/-- Left- and right- residuation operators on a quantale are similar to the Heyting operator
    on complete lattices, but for a non-commutative logic.
    I.e. `x ⇨ᵣ y = sSup { z | x * z ≤ y }`.
-/
@[to_additive]
def right_residuation (x y : α) := sSup { z | x * z ≤ y }

/-- Notation for right-residuation in quantales.
    I.e. `x ⇨ᵣ y = sSup { z | x * z ≤ y }`.
-/
@[to_additive]
scoped infixr:60 " ⇨ᵣ " => right_residuation

end Quantale
