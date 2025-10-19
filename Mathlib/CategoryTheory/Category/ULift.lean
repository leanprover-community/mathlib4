/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Data.ULift

/-!
# Basic API for ULift

This file contains a very basic API for working with the categorical
instance on `ULift C` where `C` is a type with a category instance.

1. `CategoryTheory.ULift.upFunctor` is the functorial version of the usual `ULift.up`.
2. `CategoryTheory.ULift.downFunctor` is the functorial version of the usual `ULift.down`.
3. `CategoryTheory.ULift.equivalence` is the categorical equivalence between
  `C` and `ULift C`.

# ULiftHom

Given a type `C : Type u`, `ULiftHom.{w} C` is just an alias for `C`.
If we have `category.{v} C`, then `ULiftHom.{w} C` is endowed with a category instance
whose morphisms are obtained by applying `ULift.{w}` to the morphisms from `C`.

This is a category equivalent to `C`. The forward direction of the equivalence is `ULiftHom.up`,
the backward direction is `ULiftHom.down` and the equivalence is `ULiftHom.equiv`.

# AsSmall

This file also contains a construction which takes a type `C : Type u` with a
category instance `Category.{v} C` and makes a small category
`AsSmall.{w} C : Type (max w v u)` equivalent to `C`.

The forward direction of the equivalence, `C ⥤ AsSmall C`, is denoted `AsSmall.up`
and the backward direction is `AsSmall.down`. The equivalence itself is `AsSmall.equiv`.
-/

universe w₁ v₁ v₂ u₁ u₂

namespace CategoryTheory

attribute [local instance] uliftCategory

variable {C : Type u₁} [Category.{v₁} C]

/-- The functorial version of `ULift.up`. -/
@[simps]
def ULift.upFunctor : C ⥤ ULift.{u₂} C where
  obj := ULift.up
  map f := f

/-- The functorial version of `ULift.down`. -/
@[simps]
def ULift.downFunctor : ULift.{u₂} C ⥤ C where
  obj := ULift.down
  map f := f

/-- The categorical equivalence between `C` and `ULift C`. -/
@[simps]
def ULift.equivalence : C ≌ ULift.{u₂} C where
  functor := ULift.upFunctor
  inverse := ULift.downFunctor
  unitIso :=
    { hom := 𝟙 _
      inv := 𝟙 _ }
  counitIso :=
    { hom := { app := fun _ => 𝟙 _ }
      inv := { app := fun _ => 𝟙 _ } }

section ULiftHom

/-- `ULiftHom.{w} C` is an alias for `C`, which is endowed with a category instance
  whose morphisms are obtained by applying `ULift.{w}` to the morphisms from `C`.
-/
def ULiftHom.{w, u} (C : Type u) : Type u :=
  let _ := ULift.{w} C
  C

instance {C} [Inhabited C] : Inhabited (ULiftHom C) :=
  ⟨(default : C)⟩

/-- The obvious function `ULiftHom C → C`. -/
def ULiftHom.objDown {C} (A : ULiftHom C) : C :=
  A

/-- The obvious function `C → ULiftHom C`. -/
def ULiftHom.objUp {C} (A : C) : ULiftHom C :=
  A

@[simp]
theorem objDown_objUp {C} (A : C) : (ULiftHom.objUp A).objDown = A :=
  rfl

@[simp]
theorem objUp_objDown {C} (A : ULiftHom C) : ULiftHom.objUp A.objDown = A :=
  rfl

instance ULiftHom.category : Category.{max v₂ v₁} (ULiftHom.{v₂} C) where
  Hom A B := ULift.{v₂} <| A.objDown ⟶ B.objDown
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.down ≫ g.down⟩

/-- One half of the equivalence between `C` and `ULiftHom C`. -/
@[simps]
def ULiftHom.up : C ⥤ ULiftHom C where
  obj := ULiftHom.objUp
  map f := ⟨f⟩

/-- One half of the equivalence between `C` and `ULiftHom C`. -/
@[simps]
def ULiftHom.down : ULiftHom C ⥤ C where
  obj := ULiftHom.objDown
  map f := f.down

/-- The equivalence between `C` and `ULiftHom C`. -/
def ULiftHom.equiv : C ≌ ULiftHom C where
  functor := ULiftHom.up
  inverse := ULiftHom.down
  unitIso := NatIso.ofComponents fun _ => eqToIso rfl
  counitIso := NatIso.ofComponents fun _ => eqToIso rfl

end ULiftHom

/-- `AsSmall C` is a small category equivalent to `C`.
  More specifically, if `C : Type u` is endowed with `Category.{v} C`, then
  `AsSmall.{w} C : Type (max w v u)` is endowed with an instance of a small category.

  The objects and morphisms of `AsSmall C` are defined by applying `ULift` to the
  objects and morphisms of `C`.

  Note: We require a category instance for this definition in order to have direct
  access to the universe level `v`.
-/
@[nolint unusedArguments]
def AsSmall.{w, v, u} (D : Type u) [Category.{v} D] := ULift.{max w v} D

instance : SmallCategory (AsSmall.{w₁} C) where
  Hom X Y := ULift.{max w₁ u₁} <| X.down ⟶ Y.down
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.down ≫ g.down⟩

/-- One half of the equivalence between `C` and `AsSmall C`. -/
@[simps]
def AsSmall.up : C ⥤ AsSmall C where
  obj X := ⟨X⟩
  map f := ⟨f⟩

/-- One half of the equivalence between `C` and `AsSmall C`. -/
@[simps]
def AsSmall.down : AsSmall C ⥤ C where
  obj X := ULift.down X
  map f := f.down

@[reassoc]
theorem down_comp {X Y Z : AsSmall C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).down = f.down ≫ g.down :=
  rfl

@[simp]
theorem eqToHom_down {X Y : AsSmall C} (h : X = Y) :
    (eqToHom h).down = eqToHom (congrArg ULift.down h) := by
  subst h
  rfl

/-- The equivalence between `C` and `AsSmall C`. -/
@[simps]
def AsSmall.equiv : C ≌ AsSmall C where
  functor := AsSmall.up
  inverse := AsSmall.down
  unitIso := NatIso.ofComponents fun _ => eqToIso rfl
  counitIso := NatIso.ofComponents fun _ => eqToIso <| ULift.ext _ _ rfl

instance [Inhabited C] : Inhabited (AsSmall C) :=
  ⟨⟨default⟩⟩

/-- The equivalence between `C` and `ULiftHom (ULift C)`. -/
def ULiftHomULiftCategory.equiv.{v', u', v, u} (C : Type u) [Category.{v} C] :
    C ≌ ULiftHom.{v'} (ULift.{u'} C) :=
  ULift.equivalence.trans ULiftHom.equiv

end CategoryTheory
