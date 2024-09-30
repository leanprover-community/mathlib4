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

* class `Quantale`: a monoid distributing over a complete sup-semilattice.
  I.e satisfying `x * (sSup s) = ⨆ y ∈ s, x * y` and `(sSup s) * y = ⨆ x ∈ s, x * y`

Conceptually, every complete sup-semilattice is of course a complete lattice.
However, when considering morphisms between quantales, usually only the supremum
is required to be preserved. Hence, it is conseptually cleaner to define it as a
complete sup-semilattice. (In literature, both variants occur.)

* `is_integral`: a quantale for which `1 = ⊤`
* `is_comm`: a commutative quantale, satisfying `x * y = y * x`
* `is_idem`: an idempotent quantale, satisfying `x * x = x`

## Naming conventions

## Notation

* `x ⇨ₗ y` : `sSup { z | z * x ≤ y }`, the left-residuation of `y` over `x`  ;
* `x ⇨ᵣ y` : `sSup { z | x * z ≤ y }`, the right-residuation of `y` over `x` ;

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

/-- A quantale is a monoid distributing over a complete sup-semilattice.

    Technically, I would prefer to define it as
    `class Quantale (α : Type*) extends Monoid α, CompleteSemilatticeSup α where ...`
    however, if I do that currently, the elements ⊤ and ⊥ are not automatically defined.
    I could do that separately, but it seems more sensible to push the definition
    of those to CompleteSemmilatticeSup in the library, as they are already making
    sense there and having them should not break anything (in theory).

    The reason not to consider a quantale as a complete lattice, is because the
    morphisms between quantales usually only preserve the join and not the inf.
    In fact, when seen as a generalization of locales, the monoid multiplication
    usually takes the place of the inf.
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
def is_integral [Quantale α] := (⊤ : α) = 1

/-- A quantale is commutative if its monoid satisfies `x * y = y * x` -/
def is_comm [Quantale α] := ∀ x y : α , x * y = y * x

/-- A quantale is idempotent if its monoid satisfies `x * x = x` -/
def is_idem [Quantale α] := ∀ x : α, x * x = x

variable {α : Type _}
variable [Quantale α]

/-- Left- and right- residuation operators on a quantale are similar to the Heyting operator
    on complete lattices, but for a non-commutative logic.
    I.e. `x ⇨ₗ y = sSup { z | z * x ≤ y }`.
-/
def l_residuation (x y : α) := sSup { z | z * x ≤ y }
infixr:60 " ⇨ₗ " => l_residuation

/-- Left- and right- residuation operators on a quantale are similar to the Heyting operator
    on complete lattices, but for a non-commutative logic.
    I.e. `x ⇨ᵣ y = sSup { z | x * z ≤ y }`.
-/
def r_residuation (x y : α) := sSup { z | x * z ≤ y }
infixr:60 " ⇨ᵣ " => r_residuation

end Quantale

end
