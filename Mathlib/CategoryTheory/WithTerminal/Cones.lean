/-
Copyright (c) 2025 Moisés Herradón Cueto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moisés Herradón Cueto
-/
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.WithTerminal.Basic

/-!
# Relations between `Cone`, `WithTerminal` and `Over`

Given categories `C` and `J`, an object `X : C` and a functor `K : J ⥤ Over X`,
it has an obvious lift `liftFromOver K : WithTerminal J ⥤ C`, namely, send the terminal
object to `X`. These two functors have equivalent categories of cones (`coneEquiv`).
As a corollary, the limit of `K` is the limit of `liftFromOver K`, and viceversa.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.WithTerminal

universe w w' v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

namespace CategoryTheory.Limits.WithTerminal

/-- The category of functors `J ⥤ Over X` can be seen as part of a comma category,
namely the comma category constructed from the identity of the category of functors
`J ⥤ C` and the functor that maps `X : C` to the constant functor `J ⥤ C`.

Given a functor `K : J ⥤ Over X`, it is mapped to a natural transformation from the
obvious functor `J ⥤ C` to the constant functor `X`. -/
@[simps]
def commaFromFunctorToOver {X : C} : (J ⥤ Over X) ⥤ Comma (𝟭 (J ⥤ C)) (Functor.const J) where
  obj K := {
    left := K ⋙ Over.forget X
    right := X
    hom.app a := (K.obj a).hom
  }
  map f := {
    left := whiskerRight f (Over.forget X)
    right := 𝟙 X
  }

/-- For any functor `K : J ⥤ Over X`, there is a canonical extension
`WithTerminal J ⥤ C`, that sends `star` to `X`. -/
@[simps!]
def liftFromOver {X : C} : (J ⥤ Over X) ⥤ WithTerminal J ⥤ C :=
  commaFromFunctorToOver ⋙ equivComma.inverse

/-- The extension of a functor to over categories behaves well with compositions. -/
@[simps]
def extendCompose {X : C} (K : J ⥤ Over X) (F : C ⥤ D) :
    (liftFromOver.obj K ⋙ F) ≅ liftFromOver.obj (K ⋙ (Over.post F)) where
  hom.app
  | star => 𝟙 _
  | of a => 𝟙 _
  inv.app
  | star => 𝟙 _
  | of a => 𝟙 _

/-- A cone of a functor `K : J ⥤ Over X` consists of an object of `Over X`, together
with morphisms. This same object is a cone of the extended functor
`liftFromOver.obj K : WithTerminal J ⥤ C`. -/
@[simps]
private def coneLift {X : C} {K : J ⥤ Over X} : Cone K ⥤ Cone (liftFromOver.obj K) where
  obj t := {
    pt := t.pt.left
    π.app
    | of a => (t.π.app a).left
    | star => t.pt.hom
    π.naturality
    | star, star, _
    | of a, star, _ => by aesop
    | star, of _, _ => by contradiction
    | of a, of b, f => by simp [← Comma.comp_left
    ]
  }
  map {t₁ t₂} f := {
    hom := f.hom.left
    w
    | star => by aesop_cat
    | of a => by simp [← Comma.comp_left]
  }

/-- This is the inverse of the previous construction: a cone of an extended functor
`liftFromOver.obj K : WithTerminal J ⥤ C` consists of an object of `C`, together
with morphisms. This same object is a cone of the original functor `K : J ⥤ Over X`. -/
@[simps]
private def coneBack {X : C} {K : J ⥤ Over X} : Cone (liftFromOver.obj K) ⥤ Cone K where
  obj t := {
    pt := .mk (t.π.app star)
    π.app a := {
      left := t.π.app (of a)
      right := 𝟙 _
      w := by simpa using t.w (homFrom a)
    }
    π.naturality a b f := by
      ext; simpa using t.π.naturality (incl.map f)
  }
  map {t₁ t₂ f} := {
    hom := Over.homMk f.hom
  }

-- @[simp]
-- theorem coneBack_obj_pt {X : C} {K : J ⥤ Over X} (t : Cone (liftFromOver.obj K)) :
--     (coneBack.obj t).pt  = Over.mk (t.π.app star) := rfl

/-- The isomorphism between `coneLift ⋙ coneBack` and the identity, at the level of objects. -/
@[simps]
private def coneLiftBack {X : C} {K : J ⥤ Over X} (t : Cone K) :
   coneBack.obj (coneLift.obj t) ≅ t where
  hom.hom := 𝟙 t.pt
  inv.hom := 𝟙 t.pt

/-- The isomorphism between `coneBack ⋙ coneLift` and the identity, at the level of objects. -/
@[simps]
private def coneBackLift {X : C} {K : J ⥤ Over X} (t : Cone (liftFromOver.obj K)) :
    coneLift.obj (coneBack.obj t) ≅ t where
  hom.hom := 𝟙 t.pt
  inv.hom := 𝟙 t.pt

/-- Given a functor `K : J ⥤ Over X` and its extension `liftFromOver K : WithTerminal J ⥤ C`,
there is an obvious equivalence between cones of these two functors.
A cone of `K` is an object of `Over X`, so it has the form `t ⟶ X`.
Equivalently, a cone of `WithTerminal K` is an object `t : C`,
and we can recover the structure morphism as `π.app X : t ⟶ X`. -/
@[simps]
def coneEquiv {X : C} (K : J ⥤ Over X) : Cone K ≌ Cone (liftFromOver.obj K) where
  functor := coneLift
  inverse := coneBack
  unitIso := NatIso.ofComponents coneLiftBack
  counitIso := NatIso.ofComponents coneBackLift

end CategoryTheory.Limits.WithTerminal
