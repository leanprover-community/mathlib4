/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.LocallyFinsupp.Pushforward
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Algebraic Cycles

In this file we define algebraic cycles on a scheme `X` with coefficients in a type `R` and provide
some basic API for working with them. We define an algebraic cycle on a scheme `X` with
coefficients in a type `R` to be functions `c : X → R` whose support is locally finite.

## Implementation notes

Here we're making use of the equivalence between irreducible closed subsets of a scheme and their
generic points in order to reuse the API in `Function.locallyFinsupp`, hence the slightly
nonstandard definition.
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u v
variable {X Y : Scheme.{u}} {R : Type*}

/--
Algebraic cycle on a scheme `X` with coefficients in a type `Z` is just a function from `X` to `Z`
with locally finite support (see the module docstring for more details).

Note: currently this is an abbrev to save some effort in duplicating API. This seems fine for now,
but be aware of this if there is ever an instance clash involving algebraic cycles.
-/
@[stacks 02QR]
abbrev AlgebraicCycle (X : Scheme.{u}) (R : Type*) [Zero R] :=
  Function.locallyFinsupp X R

variable (f : X ⟶ Y) [Semiring R] (c : AlgebraicCycle X R) (x : X) (z : Y)
namespace AlgebraicCycle

/--
Implementation detail for `AlgebraicCycle.map`: function used to define the coefficient of the
pushforward of a cycle `c` at a point `z = f x`.
-/
@[stacks 02R3]
noncomputable def mapCoeff {N : Type*} [DecidableEq N] {Y : Scheme} (f : X ⟶ Y) (wx : X → N)
    (wy : Y → N) (x : X) : ℕ := if wx x = wy (f.base x) then f.residueDegree x else 0

/--
The pushforward of algebraic cycles with respect to a quasicompact morphism of schemes. The
arguments `wx` and `wy` are certain weight functions used to calculate how the weights of the
algebraic cycle should be adjusted to make the pushforward operation functorial. Typically in
applications these will be some notions of dimension or codimension. The most common notion of
dimension is `Order.height`, and the most common notion of codimension is `Order.coheight`, though
more sophisticated notions exist in the literature which are useful when sufficient
equidimensionality hypotheses cannot be assumed.
-/
@[stacks 02R3]
noncomputable
def map [QuasiCompact f] {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)
    (c : AlgebraicCycle X R) : AlgebraicCycle Y R :=
  Function.locallyFinsupp.map f (Nat.cast (R := R) <| mapCoeff f wx wy ·) f.isSpectralMap c

@[simp]
lemma map_id {N : Type*} [DecidableEq N] (wx : X → N) (c : AlgebraicCycle X R) :
    map (𝟙 _) wx wx c = c := by
  apply Function.locallyFinsupp.map_id
  simp [mapCoeff]

section WeilDivisor

variable {R : Type*}

/--
A Weil divisor is an algebraic cycle supported purely in codimension one
-/
def IsWeilDivisor [Zero R] (D : AlgebraicCycle X R) : Prop :=
  D.support ⊆ {x | Order.coheight x = 1}

lemma isWeilDivisor_iff [Zero R] {D : AlgebraicCycle X R} :
    IsWeilDivisor D ↔ D.support ⊆ {x | Order.coheight x = 1} := Iff.rfl

lemma IsWeilDivisor.coheight_eq_one [Zero R] {D : AlgebraicCycle X R} (hD : IsWeilDivisor D)
    {x : X} (hx : D x ≠ 0) : Order.coheight x = 1 := hD hx

lemma isWeilDivisor_zero [Zero R] : IsWeilDivisor (0 : AlgebraicCycle X R) :=
  fun _ hx => absurd rfl hx

lemma IsWeilDivisor.add [AddMonoid R] {D E : AlgebraicCycle X R} (hD : IsWeilDivisor D)
    (hE : IsWeilDivisor E) : IsWeilDivisor (D + E) :=
  (Function.support_add _ _).trans (Set.union_subset hD hE)

open Function.locallyFinsuppWithin in
@[simp]
lemma isWeilDivisor_neg [AddGroup R] {D : AlgebraicCycle X R} :
    IsWeilDivisor (-D) ↔ IsWeilDivisor D := by
  simp only [IsWeilDivisor, support_neg]

lemma IsWeilDivisor.neg [AddGroup R] {D : AlgebraicCycle X R} (hD : IsWeilDivisor D) :
    IsWeilDivisor (-D) := by simp [hD]

lemma IsWeilDivisor.sub [AddGroup R] {D E : AlgebraicCycle X R} (hD : IsWeilDivisor D)
    (hE : IsWeilDivisor E) : IsWeilDivisor (D - E) := by
  rw [sub_eq_add_neg]
  exact hD.add hE.neg

open Function.locallyFinsuppWithin in
lemma isWeilDivisor_single [DecidableEq X] [Zero R] {x : X} (hx : Order.coheight x = 1) (r : R) :
    IsWeilDivisor (single x r) := fun _ _ ↦ by simp_all

end WeilDivisor

end AlgebraicGeometry.AlgebraicCycle
