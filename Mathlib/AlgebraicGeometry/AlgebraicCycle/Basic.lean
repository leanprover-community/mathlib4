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

variable (f : X ⟶ Y) [CompactSpace X]

section AddCommMonoid

variable [AddCommMonoid R]

/--
The degree of a zero-cycle `D` with respect to a morphism `f : X ⟶ Y`.
Note that this definition is closely related to the pushforward of `D` along `f` (see stacks 0AZ1).
In applications, typically `f` is proper (so the pushforward respects rational equivalence) and `Y`
is `Spec k` for some field `k`.
-/
@[stacks 0AZ2]
noncomputable def degree : AlgebraicCycle X R →+ R where
  toFun D := ∑ᶠ x, f.residueDegree x • D x
  map_zero' := by simp
  map_add' D D' := by
    simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, smul_add]
    exact finsum_add_distrib (D.finite_support.subset fun x hx h ↦ hx (by simp [h]))
      (D'.finite_support.subset fun x hx h ↦ hx (by simp [h]))

lemma degree_apply (D : AlgebraicCycle X R) :
    degree f D = ∑ᶠ x, f.residueDegree x • D x :=
  rfl

open Function.locallyFinsuppWithin in
@[simp]
lemma degree_single [DecidableEq X] (p : X) (r : R) :
    degree f (single p r) = f.residueDegree p • r := by
  simp [degree_apply, finsum_eq_finsetSum_of_support_subset (s := {p})]

end AddCommMonoid

section pushforward

variable [QuasiCompact f] [Semiring R] {N : Type*} [DecidableEq N] (wx : X → N) (wy : Y → N)

lemma degree_eq_map_of_unique [Unique Y] (D : AlgebraicCycle X R)
    (hw : ∀ x, D x ≠ 0 → f.residueDegree x ≠ 0 → wx x = wy (f.base x)) :
    degree f D = map f wx wy D default := by
  have : f.base ⁻¹' {default} = Set.univ := Set.eq_univ_of_forall fun _ ↦ Unique.eq_default _
  simp only [degree_apply, map, Function.locallyFinsupp.map_apply, this, finsum_mem_univ]
  refine finsum_congr fun x ↦ ?_
  by_cases hD : D x = 0
  · simp [hD]
  by_cases hr : f.residueDegree x = 0
  · simp [hr, mapCoeff]
  simp [mapCoeff, hw x hD hr, nsmul_eq_mul, (Nat.cast_commute _ (D x)).eq]

end pushforward

end degree

section WeilDivisor

variable {R : Type*}

/--
A Weil divisor is an algebraic cycle supported purely in codimension one
-/
@[stacks 0BE2]
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

variable (X R) in
/--
The Weil divisors on `X`, as a subgroup of the algebraic cycles
-/
@[stacks 0BE2]
def weilDivisors [AddGroup R] : AddSubgroup (AlgebraicCycle X R) :=
  Function.locallyFinsuppWithin.supported R Set.univ {x : X | Order.coheight x = 1}

@[simp]
lemma mem_weilDivisors [AddGroup R] {D : AlgebraicCycle X R} :
    D ∈ weilDivisors X R ↔ IsWeilDivisor D := Iff.rfl

@[simp]
lemma isWeilDivisor_neg [AddGroup R] {D : AlgebraicCycle X R} :
    IsWeilDivisor (-D) ↔ IsWeilDivisor D := (weilDivisors X R).neg_mem_iff

lemma IsWeilDivisor.neg [AddGroup R] {D : AlgebraicCycle X R} (hD : IsWeilDivisor D) :
    IsWeilDivisor (-D) := (weilDivisors X R).neg_mem hD

lemma IsWeilDivisor.sub [AddGroup R] {D E : AlgebraicCycle X R} (hD : IsWeilDivisor D)
    (hE : IsWeilDivisor E) : IsWeilDivisor (D - E) := (weilDivisors X R).sub_mem hD hE

open Function.locallyFinsuppWithin in
lemma isWeilDivisor_single [DecidableEq X] [Zero R] {x : X} (hx : Order.coheight x = 1) (r : R) :
    IsWeilDivisor (single x r) := fun _ _ ↦ by simp_all

end WeilDivisor

end AlgebraicGeometry.AlgebraicCycle
