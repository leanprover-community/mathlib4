/-
Copyright (c) 2025 Moisés Herradón Cueto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moisés Herradón Cueto
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.WithTerminal.Basic

/-!
# Relations between `Cone`, `WithTerminal` and `Over`

Given categories `C` and `J`, an object `X : C` and a functor `K : J ⥤ Over X`,
it has an obvious lift `liftFromOver K : WithTerminal J ⥤ C`, namely, send the terminal
object to `X`. These two functors have equivalent categories of cones (`coneEquiv`).
As a corollary, the limit of `K` is the limit of `liftFromOver K`, and vice-versa.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

open CategoryTheory Limits

universe w w' v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

namespace CategoryTheory.WithTerminal
variable {X : C} {K : J ⥤ Over X} {F : C ⥤ D} {t : Cone K}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The category of functors `J ⥤ Over X` can be seen as part of a comma category,
namely the comma category constructed from the identity of the category of functors
`J ⥤ C` and the functor that maps `X : C` to the constant functor `J ⥤ C`.

Given a functor `K : J ⥤ Over X`, it is mapped to a natural transformation from the
obvious functor `J ⥤ C` to the constant functor `X`. -/
@[simps]
def commaFromOver : (J ⥤ Over X) ⥤ Comma (𝟭 (J ⥤ C)) (Functor.const J) where
  obj K := {
    left := K ⋙ Over.forget X
    right := X
    hom.app a := (K.obj a).hom
  }
  map f := {
    left := Functor.whiskerRight f (Over.forget X)
    right := 𝟙 X
  }

/-- For any functor `K : J ⥤ Over X`, there is a canonical extension
`WithTerminal J ⥤ C`, that sends `star` to `X`. -/
@[simps!]
def liftFromOver : (J ⥤ Over X) ⥤ WithTerminal J ⥤ C := commaFromOver ⋙ equivComma.inverse

/-- The extension of a functor to over categories behaves well with compositions. -/
@[simps]
def liftFromOverComp : liftFromOver.obj (K ⋙ Over.post F) ≅ liftFromOver.obj K ⋙ F where
  hom.app | star | of a => 𝟙 _
  inv.app | star | of a => 𝟙 _

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A cone of a functor `K : J ⥤ Over X` consists of an object of `Over X`, together
with morphisms. This same object is a cone of the extended functor
`liftFromOver.obj K : WithTerminal J ⥤ C`. -/
@[simps]
private def coneLift : Cone K ⥤ Cone (liftFromOver.obj K) where
  obj t := {
    pt := t.pt.left
    π.app
    | of a => (t.π.app a).left
    | star => t.pt.hom
    π.naturality
    | star, star, _
    | of a, star, _ => by aesop
    | of a, of b, f => by simp [← Comma.comp_left]
  }
  map {t₁ t₂} f := {
    hom := f.hom.left
    w
    | star => by cat_disch
    | of a => by simp [← Comma.comp_left]
  }

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- This is the inverse of the previous construction: a cone of an extended functor
`liftFromOver.obj K : WithTerminal J ⥤ C` consists of an object of `C`, together
with morphisms. This same object is a cone of the original functor `K : J ⥤ Over X`. -/
@[simps]
private def coneBack : Cone (liftFromOver.obj K) ⥤ Cone K where
  obj t := {
    pt := .mk (t.π.app star)
    π.app a := Over.homMk (t.π.app (of a)) (t.w (homFrom a))
    π.naturality _ _ f := by ext; simpa using (t.w (incl.map f)).symm }
  map {t₁ t₂ f} :=
    { hom := Over.homMk f.hom (by simp [dsimp% f.w star] )
      w j := by ext; simp [dsimp% f.w (of j)] }

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given a functor `K : J ⥤ Over X` and its extension `liftFromOver K : WithTerminal J ⥤ C`,
there is an obvious equivalence between cones of these two functors.
A cone of `K` is an object of `Over X`, so it has the form `t ⟶ X`.
Equivalently, a cone of `WithTerminal K` is an object `t : C`,
and we can recover the structure morphism as `π.app X : t ⟶ X`. -/
@[simps! functor_obj_pt functor_map_hom inverse_obj_pt_left inverse_obj_pt_right_as
  inverse_obj_pt_hom inverse_obj_π_app_left inverse_map_hom_left unitIso_hom_app_hom_left
  unitIso_inv_app_hom_left counitIso_hom_app_hom counitIso_inv_app_hom]
def coneEquiv : Cone K ≌ Cone (liftFromOver.obj K) where
  functor := coneLift
  inverse := coneBack
  unitIso := .refl _
  counitIso := NatIso.ofComponents fun t ↦ Cone.ext <| .refl _

@[simp]
lemma coneEquiv_functor_obj_π_app_star : (coneEquiv.functor.obj t).π.app star = t.pt.hom := rfl

@[simp]
lemma coneEquiv_functor_obj_π_app_of (Y : J) :
    (coneEquiv.functor.obj t).π.app (of Y) = (t.π.app Y).left := rfl

/-- A cone `t` of `K : J ⥤ Over X` is a limit if and only if the corresponding cone
`coneLift t` of `liftFromOver.obj K : WithTerminal K ⥤ C` is a limit. -/
@[simps!]
def isLimitEquiv : IsLimit (coneEquiv.functor.obj t) ≃ IsLimit t := IsLimit.ofConeEquiv coneEquiv

end WithTerminal

open WithTerminal in
lemma Over.hasLimit_of_hasLimit_liftFromOver {X : C} (F : J ⥤ Over X)
    [HasLimit (liftFromOver.obj F)] : HasLimit F :=
  ⟨_, isLimitEquiv <| .ofIsoLimit
    (limit.isLimit (liftFromOver.obj F)) (coneEquiv.counitIso.app _).symm⟩

instance (X : C) [HasLimitsOfShape (WithTerminal J) C] :
    HasLimitsOfShape J (Over X) where
  has_limit _ := Over.hasLimit_of_hasLimit_liftFromOver ..

instance (X : C) [HasLimitsOfSize.{w, w'} C] : HasLimitsOfSize.{w, w'} (Over X) where

namespace WithInitial
variable {X : C} {K : J ⥤ Under X} {F : C ⥤ D} {t : Cocone K}

/-- The category of functors `J ⥤ Under X` can be seen as part of a comma category,
namely the comma category constructed from the identity of the category of functors
`J ⥤ C` and the functor that maps `X : C` to the constant functor `J ⥤ C`.

Given a functor `K : J ⥤ Under X`, it is mapped to a natural transformation to the
obvious functor `J ⥤ C` from the constant functor `X`. -/
@[simps]
def commaFromUnder : (J ⥤ Under X) ⥤ Comma (Functor.const J) (𝟭 (J ⥤ C)) where
  obj K := {
    left := X
    right := K ⋙ Under.forget X
    hom.app a := (K.obj a).hom
  }
  map f := {
    left := 𝟙 X
    right := Functor.whiskerRight f (Under.forget X)
  }

/-- For any functor `K : J ⥤ Under X`, there is a canonical extension
`WithInitial J ⥤ C`, that sends `star` to `X`. -/
@[simps!]
def liftFromUnder : (J ⥤ Under X) ⥤ WithInitial J ⥤ C := commaFromUnder ⋙ equivComma.inverse

/-- The extension of a functor to under categories behaves well with compositions. -/
@[simps]
def liftFromUnderComp : liftFromUnder.obj (K ⋙ Under.post F) ≅ liftFromUnder.obj K ⋙ F where
  hom.app | star | of a => 𝟙 _
  inv.app | star | of a => 𝟙 _

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A cocone of a functor `K : J ⥤ Under X` consists of an object of `Under X`, together
with morphisms. This same object is a cocone of the extended functor
`liftFromUnder.obj K : WithInitial J ⥤ C`. -/
@[simps]
private def coconeLift : Cocone K ⥤ Cocone (liftFromUnder.obj K) where
  obj t := {
    pt := t.pt.right
    ι.app
    | of a => (t.ι.app a).right
    | star => t.pt.hom
    ι.naturality
    | star, star, _
    | star, of b, _ => by aesop
    | of a, of b, f => by simp [← Comma.comp_right]
  }
  map {t₁ t₂} f := {
    hom := f.hom.right
    w
    | star => by cat_disch
    | of a => by simp [← Comma.comp_right]
  }

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- This is the inverse of the previous construction: a cocone of an extended functor
`liftFromUnder.obj K : WithInitial J ⥤ C` consists of an object of `C`, together
with morphisms. This same object is a cocone of the original functor `K : J ⥤ Under X`. -/
@[simps]
private def coconeBack : Cocone (liftFromUnder.obj K) ⥤ Cocone K where
  obj t := {
    pt := .mk (t.ι.app star)
    ι.app a := Under.homMk (t.ι.app (of a)) (t.w (homTo a))
    ι.naturality _ _ f := by ext; simpa using t.ι.naturality (incl.map f) }
  map {t₁ t₂ f} :=
    { hom := Under.homMk f.hom (f.w .star)
      w j := by ext; simp [dsimp% f.w (of j)] }

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given a functor `K : J ⥤ Under X` and its extension `liftFromUnder K : WithInitial J ⥤ C`,
there is an obvious equivalence between cocones of these two functors.
A cocone of `K` is an object of `Under X`, so it has the form `X ⟶ t`.
Equivalently, a cocone of `WithInitial K` is an object `t : C`,
and we can recover the structure morphism as `ι.app X : X ⟶ t`. -/
@[simps! functor_obj_pt functor_map_hom inverse_obj_pt_right inverse_obj_pt_left_as
  inverse_obj_pt_hom inverse_obj_ι_app_right inverse_map_hom_right unitIso_hom_app_hom_right
  unitIso_inv_app_hom_right counitIso_hom_app_hom counitIso_inv_app_hom]
def coconeEquiv : Cocone K ≌ Cocone (liftFromUnder.obj K) where
  functor := coconeLift
  inverse := coconeBack
  unitIso := .refl _
  counitIso := NatIso.ofComponents fun t ↦ Cocone.ext <| .refl _

@[simp]
lemma coconeEquiv_functor_obj_ι_app_star : (coconeEquiv.functor.obj t).ι.app star = t.pt.hom := rfl

@[simp]
lemma coconeEquiv_functor_obj_ι_app_of (Y : J) :
    (coconeEquiv.functor.obj t).ι.app (of Y) = (t.ι.app Y).right := rfl

/-- A cocone `t` of `K : J ⥤ Under X` is a colimit if and only if the corresponding cocone
`coconeLift t` of `liftFromUnder.obj K : WithInitial K ⥤ C` is a colimit. -/
@[simps!]
def isColimitEquiv : IsColimit (coconeEquiv.functor.obj t) ≃ IsColimit t :=
  IsColimit.ofCoconeEquiv coconeEquiv

end CategoryTheory.WithInitial

open WithInitial in
lemma Under.hasColimit_of_hasColimit_liftFromUnder {X : C} (F : J ⥤ Under X)
    [HasColimit (liftFromUnder.obj F)] : HasColimit F :=
  ⟨_, isColimitEquiv <| .ofIsoColimit
    (colimit.isColimit (liftFromUnder.obj F)) (coconeEquiv.counitIso.app _).symm⟩

instance (X : C) [HasColimitsOfShape (WithInitial J) C] :
    HasColimitsOfShape J (Under X) where
  has_colimit _ := Under.hasColimit_of_hasColimit_liftFromUnder ..

instance (X : C) [HasColimitsOfSize.{w, w'} C] : HasColimitsOfSize.{w, w'} (Under X) where
