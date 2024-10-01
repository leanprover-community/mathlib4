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
quantum mechanics, and computer science. Intuitively, as described by [vickers1989],
open sets of a topology form a frame, and can be considered as modeling what is `observable`
in a system. Quantales come into play when making an observation may change the system itself.
Traditionally, one would write `x ⊓ y` to describe making observations `x` and `y` at the same
time, but when the order of observation becomes important due to changes in the system caused
by the observation, it makes more sense to write `x * y` or `x + y` and consider `*` or `+` as
a possibly non-commutative monoid.

## Main definitions

* class `Quantale`: a monoid distributing over a complete sup-semilattice,
  i.e satisfying `x * (sSup s) = ⨆ y ∈ s, x * y` and `(sSup s) * y = ⨆ x ∈ s, x * y`

* `IsIntegral`: a quantale for which `1 = ⊤`
* `IsComm`: a commutative quantale, satisfying `x * y = y * x`
* `IsIdem`: an idempotent quantale, satisfying `x * x = x`

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

Additive quantales and multiplicative quantales both occur in literature.
For sequences of actions, usually a multiplicative quantale is used, but for
describing timing of actions (for example) the additive quantale of max-plus algebra
a.k.a. tropical algebra, can be used. Therefore, extending the definitions with
addition is - I think - relevant future work.

-/

/-- A quantale generally is defined as a monoid distributing over a complete sup-semilattice.
    However, as it is common to also consider constructs like ⊤ and ⊥ on quantales,
    we use the (equivalent) definition of a monoid distributing over a complete lattice.
    Since every sup-semilattice is a complete lattice, we get the ensuing lemmas for free this way.

    Morphisms over quantales will usually focus on preserving the supremum and the monoid.
-/
class Quantale (α : Type*) extends Monoid α, CompleteLattice α where
  /-- Multiplication is distributive over join in a quantale -/
  protected mul_sSup_eq_iSup_mul (x : α) (s : Set α) : x * sSup s = ⨆ y ∈ s, x * y
  /-- Multiplication is distributive over join in a quantale -/
  protected sSup_mul_eq_iSup_mul (s : Set α) (y : α) : sSup s * y = ⨆ x ∈ s, x * y

section

variable (α : Type _)
variable [Quantale α]

theorem mul_sSup_eq_iSup_mul : ∀ x : α, ∀ s : Set α, x * sSup s = ⨆ y ∈ s, x * y :=
  Quantale.mul_sSup_eq_iSup_mul
theorem sSup_mul_eq_iSup_mul : ∀ s : Set α, ∀ y : α, sSup s * y = ⨆ x ∈ s, x * y :=
  Quantale.sSup_mul_eq_iSup_mul

namespace Quantale

/- Basic definitions on quantales -/

/-- A quantale is integral if its unit and top element coincide -/
def IsIntegral [Quantale α] := (⊤ : α) = 1

/-- A quantale is commutative if its monoid satisfies `x * y = y * x` -/
def IsComm [Quantale α] := ∀ x y : α , x * y = y * x

/-- A quantale is idempotent if its monoid satisfies `x * x = x` -/
def IsIdem [Quantale α] := ∀ x : α, x * x = x

variable {α : Type _}
variable [Quantale α]

/-- Left- and right- residuation operators on a quantale are similar to the Heyting operator
on complete lattices, but for a non-commutative logic.
I.e. `x ⇨ₗ y = sSup { z | z * x ≤ y }`.
-/
def left_residuation (x y : α) := sSup { z | z * x ≤ y }

/-- Notation for left-residuation in quantales.
    I.e. `x ⇨ₗ y = sSup { z | z * x ≤ y }`.
-/
scoped infixr:60 " ⇨ₗ " => left_residuation

/-- Left- and right- residuation operators on a quantale are similar to the Heyting operator
    on complete lattices, but for a non-commutative logic.
    I.e. `x ⇨ᵣ y = sSup { z | x * z ≤ y }`.
-/
def right_residuation (x y : α) := sSup { z | x * z ≤ y }
/-- Notation for right-residuation in quantales.
    I.e. `x ⇨ᵣ y = sSup { z | x * z ≤ y }`.
-/
scoped infixr:60 " ⇨ᵣ " => right_residuation

end Quantale

end
