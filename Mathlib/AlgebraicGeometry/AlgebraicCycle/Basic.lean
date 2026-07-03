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
public import Mathlib.RingTheory.Flat.Rank

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
namespace AlgebraicCycle
section map

variable (f : X ⟶ Y) [Semiring R] (c : AlgebraicCycle X R) (x : X) (z : Y)
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

end map
section degree

variable {Y : Scheme.{u}} (f : X ⟶ Y)

/--
The degree of a zero-cycle `D` with respect to a morphism `f : X ⟶ Y`.
Note that this definition is closely related to the pushforward of `D` along `f` (see stacks 0AZ1).
In applications, typically `f` is proper (so the pushforward respects rational equivalence) and `Y`
is `Spec k` for some field `k`.
-/
@[stacks 0AZ2]
noncomputable def degree {R : Type*} [AddCommMonoid R] (D : AlgebraicCycle X R) : R :=
    ∑ᶠ (x : X), (f.residueDegree x) • (D x)

section AddCommMonoid

variable [AddCommMonoid R]

@[simp]
lemma degree_sum (D D' : AlgebraicCycle X R) [CompactSpace X] :
    degree f (D + D') = degree f D + degree f D' := by
  simp only [degree, Function.locallyFinsuppWithin.coe_add, Pi.add_apply, smul_add]
  rw [finsum_add_distrib]
  · apply D.finite_support.subset
    aesop
  · apply D'.finite_support.subset
    aesop

open Function.locallyFinsuppWithin in
@[simp]
lemma degree_single [DecidableEq X] (p : X) {r : R} : degree f (single p r) =
    (f.residueDegree p) • r := by
  simp [degree, finsum_eq_finsetSum_of_support_subset (s := {p})]

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup R]

@[simp]
lemma degree_neg (D : AlgebraicCycle X R) : degree f (-D) = - degree f D :=
    by simp [degree, finsum_neg_distrib]

@[simp]
lemma degree_sub (D D' : AlgebraicCycle X R) [CompactSpace X] :
    degree f (D - D') = degree f D - degree f D' := by
  simp [sub_eq_add_neg]

end AddCommGroup

end degree

end AlgebraicGeometry.AlgebraicCycle
