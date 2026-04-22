/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.LocallyFinsupp.Pushforward
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Algebraic Cycles

In this file we define algebraic cycles on a scheme `X` with coefficients in a type `R` and provide
some basic API for working with them. We define an algebraic cycle on a scheme `X` with
coefficients in a type `R` to be functions `c : X → R` whose support is locally finite.

Here we're making use of the equivalence between irreducible closed subsets of a scheme and their
generic points in order to reuse the API in Function.locallyFinsupp, hence the slightly
nonstandard definition.
-/

@[expose] public section

open AlgebraicGeometry Set Order LocallyRingedSpace Topology TopologicalSpace
  CategoryTheory

universe u v
variable {X Y : Scheme.{u}} {R : Type*}
#check Finsupp.supported
/--
Algebraic cycle on a scheme `X` with coefficients in a type `Z` is just a function from `X` to `Z`
with locally finite support.

Here we're making use of the equivalence between irreducible closed subsets of a scheme and their
generic points in order to reuse the API in Function.locallyFinsupp, hence the slightly
nonstandard definition.
-/
abbrev AlgebraicCycle (X : Scheme.{u}) (R : Type*) [Zero R] :=
    Function.locallyFinsupp X R

variable (f : X ⟶ Y) [Semiring R] (c : AlgebraicCycle X R) (x : X) (z : Y)

noncomputable
instance moduleResidueFieldExtension (x : X) :
    Module (IsLocalRing.ResidueField ↑(Y.presheaf.stalk (f x)))
    (IsLocalRing.ResidueField ↑(X.presheaf.stalk x)) :=
  letI := RingHom.toAlgebra (IsLocalRing.ResidueField.map (f.stalkMap x).hom)
  Algebra.toModule

/--
Degree of `f` at a point `x` is defined to be the degree of the associated field extension
from `κ(f x)` to `κ(x)`. We return a default value of zero when this degree is either infinite
or undefined.
-/
noncomputable
def _root_.AlgebraicGeometry.Scheme.Hom.degree : ℕ := @Module.finrank
    (IsLocalRing.ResidueField (Y.presheaf.stalk (f.base x)))
    (IsLocalRing.ResidueField (X.presheaf.stalk x)) _ _ _

namespace AlgebraicCycle

/--
Implementation detail for pushforward: function used to define the coefficient of the pushforward
of a cycle `c` at a point `z = f x`, as in stacks `02R3`.
-/
noncomputable
def mapAux {N : Type*} [DecidableEq N] {Y : Scheme} (f : X ⟶ Y) (wx : X → N) (wy : Y → N) (x : X) :
    ℕ := if wx x = wy (f.base x) then f.degree x else 0

open Function locallyFinsupp
lemma _root_.AlgebraicGeometry.Scheme.Hom.preimageSupportFinite [QuasiCompact f] :
    PreimageSupportFinite c f :=
  fun z ↦ LocallyFiniteSupport.finite_inter_support_of_isCompact c.Function.locallyFinsuppWithin.locallyFiniteSupportWithin <|
    AlgebraicGeometry.Scheme.Hom.isCompact_preimage_singleton f z

/--
The pushforward of algebraic cycles with respect to a quasicompact morphism of schemes. The
arguments `wx` and `wy` are certain weight functions used to calculate how the weights of the
algebraic cycle should be adjusted to make the pushforward operation functorial. Typically in
applications these will be some notions of dimension or codimension. The most common notion of
dimension is `Order.height`, and the most common notion of codimension is `Order.coheight`, though
more sophisticated notions exist in the literature which are useful when sufficient
equidimensionality hypotheses cannot be assumed.
-/
noncomputable
def pushforward [QuasiCompact f] {N : Type*} [DecidableEq N] (c : AlgebraicCycle X R)
    (wx : X → N) (wy : Y → N) : AlgebraicCycle Y R :=
  Function.locallyFinsupp.map f (Nat.cast (R := R) <| mapAux f wx wy ·) c
  f.isSpectralMap (f.preimageSupportFinite c)

end AlgebraicCycle
