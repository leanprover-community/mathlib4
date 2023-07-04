/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer

! This file was ported from Lean 3 source module algebra.category.Mon.adjunctions
! leanprover-community/mathlib commit 4bcba0da3d97399ce99260794213e69ccdf886ee
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Category.SemigroupCat.Basic
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Adjunctions regarding the category of monoids

This file proves the adjunction between adjoining a unit to a semigroup and the forgetful functor
from monoids to semigroups.

## TODO

* free-forgetful adjunction for monoids
* adjunctions related to commutative monoids
-/


universe u

open CategoryTheory

/-- The functor of adjoining a neutral element `one` to a semigroup.
 -/
@[to_additive (attr := simps) "The functor of adjoining a neutral element `zero` to a semigroup"]
def adjoinOne : SemigroupCat.{u} ⥤ MonCat.{u} where
  obj S := MonCat.of (WithOne S)
  map := WithOne.map
  map_id _ := WithOne.map_id
  map_comp := WithOne.map_comp
#align adjoin_one adjoinOne
#align adjoin_zero adjoinZero

@[to_additive]
instance hasForgetToSemigroup : HasForget₂ MonCat SemigroupCat where
  forget₂ :=
    { obj := fun M => SemigroupCat.of M
      map := MonoidHom.toMulHom }
set_option linter.uppercaseLean3 false in
#align has_forget_to_Semigroup hasForgetToSemigroup
set_option linter.uppercaseLean3 false in
#align has_forget_to_AddSemigroup hasForgetToAddSemigroup

/-- The adjoin_one-forgetful adjunction from `SemigroupCat` to `MonCat`.-/
@[to_additive "The adjoin_one-forgetful adjunction from `AddSemigroupCat` to `AddMonCat`"]
def adjoinOneAdj : adjoinOne ⊣ forget₂ MonCat.{u} SemigroupCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun S M => WithOne.lift.symm
      homEquiv_naturality_left_symm := by
        intro S T M f g
        ext x
        simp only [Equiv.symm_symm, adjoinOne_map, coe_comp]
        simp_rw [WithOne.map]
        cases x
        · rfl
        · simp
          rfl }
#align adjoin_one_adj adjoinOneAdj
#align adjoin_zero_adj adjoinZeroAdj

/-- The free functor `Type u ⥤ MonCat` sending a type `X` to the free monoid on `X`. -/
def free : Type u ⥤ MonCat.{u} where
  obj α := MonCat.of (FreeMonoid α)
  map := FreeMonoid.map
  map_id _ := FreeMonoid.hom_eq (fun _ => rfl)
  map_comp _ _ := FreeMonoid.hom_eq (fun _ => rfl)
#align free free

/-- The free-forgetful adjunction for monoids. -/
def adj : free ⊣ forget MonCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X G => FreeMonoid.lift.symm
      homEquiv_naturality_left_symm := fun _ _ => FreeMonoid.hom_eq (fun _ => rfl) }
#align adj adj

instance : IsRightAdjoint (forget MonCat.{u}) :=
  ⟨_, adj⟩
