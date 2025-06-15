/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Category.Semigrp.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.CategoryTheory.Adjunction.Basic

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

namespace MonCat

/-- The functor of adjoining a neutral element `one` to a semigroup. -/
@[to_additive (attr := simps) "The functor of adjoining a neutral element `zero` to a semigroup"]
def adjoinOne : Semigrp.{u} ⥤ MonCat.{u} where
  obj S := MonCat.of (WithOne S)
  map f := ofHom (WithOne.map f.hom)
  map_id _ := MonCat.hom_ext WithOne.map_id
  map_comp _ _ := MonCat.hom_ext (WithOne.map_comp _ _)

@[to_additive]
instance hasForgetToSemigroup : HasForget₂ MonCat Semigrp where
  forget₂ :=
    { obj := fun M => Semigrp.of M
      map f := Semigrp.ofHom f.hom.toMulHom }

/-- The `adjoinOne`-forgetful adjunction from `Semigrp` to `MonCat`. -/
@[to_additive "The `adjoinZero`-forgetful adjunction from `AddSemigrp` to `AddMonCat`"]
def adjoinOneAdj : adjoinOne ⊣ forget₂ MonCat.{u} Semigrp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        ConcreteCategory.homEquiv.trans (WithOne.lift.symm.trans
          (ConcreteCategory.homEquiv (X := X) (Y := (forget₂ _ _).obj Y)).symm)
      homEquiv_naturality_left_symm := by
        intros
        ext ⟨_|_⟩ <;> simp <;> rfl }

/-- The free functor `Type u ⥤ MonCat` sending a type `X` to the free monoid on `X`. -/
@[to_additive "The free functor `Type u ⥤ AddMonCat` sending a type `X` to the free monoid on `X`."]
def free : Type u ⥤ MonCat.{u} where
  obj α := MonCat.of (FreeMonoid α)
  map f := ofHom (FreeMonoid.map f)
  map_id _ := MonCat.hom_ext (FreeMonoid.hom_eq fun _ => rfl)
  map_comp _ _ := MonCat.hom_ext (FreeMonoid.hom_eq fun _ => rfl)

/-- The free-forgetful adjunction for monoids. -/
@[to_additive "The free-forgetful adjunction for additive monoids."]
def adj : free ⊣ forget MonCat.{u} :=
  Adjunction.mkOfHomEquiv
    -- The hint `(C := MonCat)` below speeds up the declaration by 10 times.
    { homEquiv X Y := (ConcreteCategory.homEquiv (C := MonCat)).trans FreeMonoid.lift.symm
      homEquiv_naturality_left_symm _ _ := MonCat.hom_ext (FreeMonoid.hom_eq fun _ => rfl) }

instance : (forget MonCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

end MonCat

namespace AddCommMonCat

/-- The free functor `Type u ⥤ AddCommMonCat`
sending a type `X` to the free commutative monoid on `X`. -/
@[simps]
noncomputable
def free : Type u ⥤ AddCommMonCat.{u} where
  obj α := .of (α →₀ ℕ)
  map f := ofHom (Finsupp.mapDomain.addMonoidHom f)

/-- The free-forgetful adjunction for commutative monoids. -/
noncomputable
def adj : free ⊣ forget AddCommMonCat.{u} where
  unit := { app X i := Finsupp.single i 1 }
  counit :=
  { app M := ofHom (Finsupp.liftAddHom (multiplesHom M))
    naturality {M N} f := by dsimp; ext1; apply Finsupp.liftAddHom.symm.injective; ext; simp }

instance : free.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩

instance : (forget AddCommMonCat.{u}).IsRightAdjoint := ⟨_, ⟨adj⟩⟩

end AddCommMonCat

namespace CommMonCat

instance : (forget CommMonCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨AddCommMonCat.adj.comp AddCommMonCat.equivalence.toAdjunction⟩⟩

end CommMonCat
