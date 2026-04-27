/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

import Mathlib.Tactic.CategoryTheory.MkConcreteCategory

open CategoryTheory

universe u

/-- A tiny test category whose morphisms are wrappers around functions. -/
structure TestCat where
  /-- The underlying type. -/
  α : Type u

namespace TestCat

@[ext]
structure Fun (X Y : TestCat.{u}) where
  toFun : X.α → Y.α

instance (X Y : TestCat.{u}) : FunLike (Fun X Y) X.α Y.α where
  coe := Fun.toFun
  coe_injective' _ _ _ := by aesop

protected def Fun.id (X : TestCat.{u}) : Fun X X where
  toFun := id

protected def Fun.comp {X Y Z : TestCat.{u}} (f : Fun X Y) (g : Fun Y Z) : Fun X Z where
  toFun := g.toFun ∘ f.toFun

mk_concrete_category TestCat Fun (Fun.id) (Fun.comp)

/-- info: TestCat.Hom.{u_1} (X Y : TestCat) : Type u_1 -/
#guard_msgs in
#check Hom

/-- info: TestCat.Hom.mk.{u_1} {X Y : TestCat} (hom' : X.Fun Y) : X.Hom Y -/
#guard_msgs in
#check Hom.mk

/-- info: TestCat.Hom.hom'.{u_1} {X Y : TestCat} (self : X.Hom Y) : X.Fun Y -/
#guard_msgs in
#check Hom.hom'

/-- info: TestCat.Hom.ext.{u_1} {X Y : TestCat} {x y : X.Hom Y} (hom' : x.hom' = y.hom') : x = y -/
#guard_msgs in
#check Hom.ext

/-- info: inferInstance : Category.{u_1, u_1 + 1} TestCat -/
#guard_msgs in
#check (inferInstance : Category TestCat)

/-- info: inferInstance : ConcreteCategory TestCat Fun -/
#guard_msgs in
#check (inferInstance : ConcreteCategory TestCat Fun)

/-- info: TestCat.Hom.hom.{u_1} {X Y : TestCat} (f : X.Hom Y) : X.Fun Y -/
#guard_msgs in
#check Hom.hom

/-- info: TestCat.ofHom.{u_1} {X Y : TestCat} (f : ToHom X Y) : X ⟶ Y -/
#guard_msgs in
#check ofHom

/-- info: TestCat.Hom.Simps.hom.{u_1} (X Y : TestCat) (f : X.Hom Y) : X.Fun Y -/
#guard_msgs in
#check Hom.Simps.hom

/-- info: TestCat.hom_id.{u_1} {X : TestCat} : Hom.hom (𝟙 X) = Fun.id X -/
#guard_msgs in
#check hom_id

/-- info: TestCat.hom_comp.{u_1} {X Y Z : TestCat} (f : X ⟶ Y) (g : Y ⟶ Z) : Hom.hom (f ≫ g) = (Hom.hom f).comp (Hom.hom g) -/
#guard_msgs in
#check hom_comp

/-- info: TestCat.hom_ofHom.{u_1} {X Y : TestCat} (f : ToHom X Y) : Hom.hom (ofHom f) = f -/
#guard_msgs in
#check hom_ofHom

/-- info: TestCat.ofHom_hom.{u_1} {X Y : TestCat} (f : X ⟶ Y) : ofHom (Hom.hom f) = f -/
#guard_msgs in
#check ofHom_hom

example : Category TestCat := inferInstance

example : ConcreteCategory TestCat Fun := inferInstance

example {X Y : TestCat} (f : X ⟶ Y) : f.hom = ConcreteCategory.hom f := rfl

example {X Y : TestCat} (f : Fun X Y) : (ofHom f).hom = f := by
  dsimp

example {X Y : TestCat} (f : X ⟶ Y) : ofHom f.hom = f := by
  dsimp

example {X : TestCat} : (𝟙 X : X ⟶ X).hom = Fun.id X := by
  dsimp

example {X Y Z : TestCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = Fun.comp f.hom g.hom := by
  dsimp

example {X Y : TestCat} (f g : X ⟶ Y) (h : f.hom = g.hom) : f = g :=
  Hom.ext h

example {X Y : TestCat} (f g : X ⟶ Y) (h : ∀ x, f x = g x) : f = g := by
  cat_disch

example {X Y : TestCat} (f : Fun X Y) (x : X.α) : ofHom f x = f x := by
  dsimp

end TestCat
--
