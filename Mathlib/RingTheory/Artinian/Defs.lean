/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Module.Submodule.Defs

/-!
# Artinian rings and modules

A module satisfying these equivalent conditions is said to be an *Artinian* R-module
if every decreasing chain of submodules is eventually constant, or equivalently,
if the relation `<` on submodules is well founded.

A ring is said to be left (or right) Artinian if it is Artinian as a left (or right) module over
itself, or simply Artinian if it is both left and right Artinian.

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `IsArtinian R M` is the proposition that `M` is an Artinian `R`-module. It is a class,
  implemented as the predicate that the `<` relation on submodules is well founded.
* `IsArtinianRing R` is the proposition that `R` is a left Artinian ring.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Artinian, artinian, Artinian ring, Artinian module, artinian ring, artinian module

-/

public section

/-- `IsArtinian R M` is the proposition that `M` is an Artinian `R`-module,
implemented as the well-foundedness of submodule inclusion. -/
abbrev IsArtinian (R M) [Semiring R] [AddCommMonoid M] [Module R M] : Prop :=
  WellFoundedLT (Submodule R M)

theorem isArtinian_iff (R M) [Semiring R] [AddCommMonoid M] [Module R M] : IsArtinian R M ↔
    WellFounded (· < · : Submodule R M → Submodule R M → Prop) :=
  isWellFounded_iff _ _

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
theorem IsArtinian.induction {R M} [Semiring R] [AddCommMonoid M] [Module R M] [IsArtinian R M]
    {P : Submodule R M → Prop} (hgt : ∀ I, (∀ J < I, P J) → P I) (I : Submodule R M) : P I :=
  WellFoundedLT.induction I hgt

-- See `Mathlib/RingTheory/Artinian/Ring.lean`
assert_not_exists IsLocalization IsLocalRing

/-- A ring is Artinian if it is Artinian as a module over itself.

Strictly speaking, this should be called `IsLeftArtinianRing` but we omit the `Left` for
convenience in the commutative case. For a right Artinian ring, use `IsArtinian Rᵐᵒᵖ R`.

For equivalent definitions, see `Mathlib/RingTheory/Artinian/Ring.lean`.
-/
@[stacks 00J5]
abbrev IsArtinianRing (R) [Semiring R] :=
  IsArtinian R R

theorem isArtinianRing_iff {R} [Semiring R] : IsArtinianRing R ↔ IsArtinian R R := Iff.rfl
