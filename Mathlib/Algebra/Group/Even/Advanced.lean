/-
Copyright (c) 2024 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Algebra.Group.Even.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic

/-!
# Squares and even elements

This file defines operations involving squares and even elements requiring more complex objects
such as substructures and orderings.
-/

namespace Subsemigroup
variable {S : Type*} [CommSemigroup S] {a : S}

variable (S) in
/--
In a commutative semigroup `S`, `Subsemigroup.sqIn S` is the subsemigroup of squares in `S`.
-/
@[to_additive evenIn
"In a commutative additive semigroup `S`, the type `AddSubsemigroup.evenIn S`
is the subsemigroup of even elements of `S`."]
def squareIn : Subsemigroup S where
  carrier := {s : S | IsSquare s}
  mul_mem' := IsSquare.mul

@[to_additive (attr := simp)]
theorem mem_squareIn : a ∈ squareIn S ↔ IsSquare a := Iff.rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_squareIn : squareIn S = {s : S | IsSquare s} := rfl

end Subsemigroup

namespace Submonoid
variable {M : Type*} [CommMonoid M] {a : M}

variable (M) in
/--
In a commutative monoid `M`, `Submonoid.sqIn M` is the submonoid of squares in `M`.
-/
@[to_additive evenIn
"In a commutative additive monoid `M`, the type `AddSubmonoid.evenIn M`
is the submonoid of even elements of `M`."]
def squareIn : Submonoid M where
  __ := Subsemigroup.squareIn M
  one_mem' := IsSquare.one

@[to_additive (attr := simp)]
theorem squareIn_toSubsemigroup : (squareIn M).toSubsemigroup = .squareIn M := rfl

@[to_additive (attr := simp)]
theorem mem_squareIn : a ∈ squareIn M ↔ IsSquare a := Iff.rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_squareIn : squareIn M = {s : M | IsSquare s} := rfl

end Submonoid

namespace Subgroup
variable {G : Type*} [CommGroup G] {a : G}

variable (G) in
/--
In an abelian group `G`, `Submonoid.sqIn G` is the subgroup of squares in `G`.
-/
@[to_additive evenIn
"In an abelian additive group `G`, the type `Submonoid.sqIn G` is
the subgroup of even elements in `G`."]
def squareIn : Subgroup G where
  __ := Submonoid.squareIn G
  inv_mem' := IsSquare.inv

@[to_additive (attr := simp)]
theorem squareIn_toSubmonoid : (squareIn G).toSubmonoid = .squareIn G := rfl

@[to_additive (attr := simp)]
theorem mem_squareIn : a ∈ squareIn G ↔ IsSquare a := Iff.rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_squareIn : squareIn G = {s : G | IsSquare s} := rfl

end Subgroup

theorem IsSquare.nonneg {R : Type*} [Semiring R] [LinearOrder R] [IsRightCancelAdd R]
    [ZeroLEOneClass R] [ExistsAddOfLE R] [PosMulMono R] [AddLeftStrictMono R]
    {x : R} (h : IsSquare x) : 0 ≤ x := by
  rcases h with ⟨y, rfl⟩
  exact mul_self_nonneg y
