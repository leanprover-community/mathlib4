/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Join.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# Pseudofunctoriality of categorical joins

In this file, we promote the join construction to two pseudofunctors
`Join.pseudofunctorLeft` and `Join.pseudofunctorRight`, expressing its pseudofunctoriality in
each variable.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Join

open Bicategory Functor

-- The proof gets too slow if we put it in a single `pseudofunctor` constructor,
-- so we break down the component proofs for the pseudofunctors over several lemmas.

section
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]


variable (A) in
/-- The structural isomorphism for composition of `pseudofunctorRight`. -/
def mapCompRight (F : B ⥤ C) (G : C ⥤ D) :
    mapPair (𝟭 A) (F ⋙ G) ≅ mapPair (𝟭 A) F ⋙ mapPair (𝟭 A) G :=
  mapIsoWhiskerRight (Functor.leftUnitor _).symm _ ≪≫ mapPairComp (𝟭 A) F (𝟭 A) G

variable (D) in
/-- The structural isomorphism for composition of `pseudofunctorLeft`. -/
def mapCompLeft (F : A ⥤ B) (G : B ⥤ C) :
    mapPair (F ⋙ G) (𝟭 D) ≅ mapPair F (𝟭 D) ⋙ mapPair G (𝟭 D) :=
  mapIsoWhiskerLeft _ (Functor.leftUnitor _).symm ≪≫ mapPairComp F (𝟭 D) G (𝟭 D)

set_option backward.defeqAttrib.useBackward true in
variable (A) in
@[reassoc]
lemma mapWhiskerLeft_whiskerLeft (F : B ⥤ C) {G H : C ⥤ D} (η : G ⟶ H) :
    mapWhiskerLeft _ (whiskerLeft F η) =
    (mapCompRight A F G).hom ≫ whiskerLeft (mapPair (𝟭 A) F) (mapWhiskerLeft _ η) ≫
      (mapCompRight A F H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

set_option backward.defeqAttrib.useBackward true in
variable (D) in
@[reassoc]
lemma mapWhiskerRight_whiskerLeft (F : A ⥤ B) {G H : B ⥤ C} (η : G ⟶ H) :
    mapWhiskerRight (whiskerLeft F η) (𝟭 D) =
    (mapCompLeft D F G).hom ≫ whiskerLeft (mapPair F (𝟭 D)) (mapWhiskerRight η _) ≫
      (mapCompLeft D F H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (A) in
@[reassoc]
lemma mapWhiskerLeft_whiskerRight {F G : B ⥤ C} (η : F ⟶ G) (H : C ⥤ D) :
    mapWhiskerLeft _ (whiskerRight η H) =
    (mapCompRight A F H).hom ≫ whiskerRight (mapWhiskerLeft _ η) (mapPair (𝟭 A) H) ≫
      (mapCompRight A G H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (D) in
@[reassoc]
lemma mapWhiskerRight_whiskerRight {F G : A ⥤ B} (η : F ⟶ G) (H : B ⥤ C) :
    mapWhiskerRight (whiskerRight η H) _ =
    (mapCompLeft D F H).hom ≫ whiskerRight (mapWhiskerRight η _) (mapPair H (𝟭 D)) ≫
      (mapCompLeft D G H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

variable {E : Type*} [Category* E]

set_option backward.defeqAttrib.useBackward true in
variable (A) in
@[reassoc]
lemma mapWhiskerLeft_associator_hom (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E) :
    mapWhiskerLeft _ (F.associator G H).hom =
      (mapCompRight A (F ⋙ G) H).hom ≫ whiskerRight (mapCompRight A F G).hom (mapPair (𝟭 A) H) ≫
      ((mapPair (𝟭 A) F).associator (mapPair (𝟭 A) G) (mapPair (𝟭 A) H)).hom ≫
      whiskerLeft (mapPair (𝟭 A) F) (mapCompRight A G H).inv ≫ (mapCompRight A F (G ⋙ H)).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

set_option backward.defeqAttrib.useBackward true in
variable (E) in
lemma mapWhiskerRight_associator_hom (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    mapWhiskerRight (F.associator G H).hom _ =
    (mapCompLeft E (F ⋙ G) H).hom ≫ whiskerRight (mapCompLeft E F G).hom (mapPair H (𝟭 E)) ≫
      ((mapPair F (𝟭 E)).associator (mapPair G (𝟭 E)) (mapPair H (𝟭 E))).hom ≫
      whiskerLeft (mapPair F (𝟭 E)) (mapCompLeft E G H).inv ≫ (mapCompLeft E F (G ⋙ H)).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

set_option backward.defeqAttrib.useBackward true in
variable (A) in
lemma mapWhiskerLeft_leftUnitor_hom (F : B ⥤ C) :
    mapWhiskerLeft _ F.leftUnitor.hom =
    (mapCompRight A (𝟭 _) F).hom ≫ whiskerRight mapPairId.hom (mapPair _ F) ≫
      (mapPair _ F).leftUnitor.hom := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

set_option backward.defeqAttrib.useBackward true in
variable (C) in
lemma mapWhiskerRight_leftUnitor_hom (F : A ⥤ B) :
    mapWhiskerRight F.leftUnitor.hom (𝟭 C) =
    (mapCompLeft C (𝟭 A) F).hom ≫ whiskerRight mapPairId.hom (mapPair F (𝟭 C)) ≫
      (mapPair F (𝟭 C)).leftUnitor.hom := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

set_option backward.defeqAttrib.useBackward true in
variable (A) in
lemma mapWhiskerLeft_rightUnitor_hom (F : B ⥤ C) :
    mapWhiskerLeft _ F.rightUnitor.hom =
    (mapCompRight A F (𝟭 C)).hom ≫ whiskerLeft (mapPair _ F) mapPairId.hom ≫
      (mapPair (𝟭 A) _).rightUnitor.hom := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

set_option backward.defeqAttrib.useBackward true in
variable (C) in
lemma mapWhiskerRight_rightUnitor_hom (F : A ⥤ B) :
    mapWhiskerRight F.rightUnitor.hom _ =
    (mapCompLeft C F (𝟭 B)).hom ≫ whiskerLeft (mapPair F _) mapPairId.hom ≫
      (mapPair _ (𝟭 C)).rightUnitor.hom := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

end

/-- The pseudofunctor sending `D` to `C ⋆ D`. -/
@[simps!]
def pseudofunctorRight (C : Type u₁) [Category.{v₁} C] :
    Pseudofunctor Cat.{v₂, u₂} Cat.{max v₁ v₂, max u₁ u₂} where
  obj D := Cat.of (C ⋆ D)
  map F := (mapPair (𝟭 C) F.toFunctor).toCatHom
  map₂ f := (mapWhiskerLeft (𝟭 C) f.toNatTrans).toCatHom₂
  mapId D := Cat.Hom.isoMk mapPairId
  mapComp F G:= Cat.Hom.isoMk <| mapCompRight C F.toFunctor G.toFunctor
  map₂_whisker_left := by intros; exact congr($(mapWhiskerLeft_whiskerLeft C _ _).toCatHom₂)
  map₂_whisker_right := by intros; exact congr($(mapWhiskerLeft_whiskerRight C _ _).toCatHom₂)
  map₂_associator := by intros; exact congr($(mapWhiskerLeft_associator_hom C _ _ _).toCatHom₂)
  map₂_left_unitor := by intros; exact congr($(mapWhiskerLeft_leftUnitor_hom C _).toCatHom₂)
  map₂_right_unitor := by intros; exact congr($(mapWhiskerLeft_rightUnitor_hom C _).toCatHom₂)

/-- The pseudofunctor sending `C` to `C ⋆ D`. -/
@[simps!]
def pseudofunctorLeft (D : Type u₂) [Category.{v₂} D] :
    Pseudofunctor Cat.{v₁, u₁} Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := Cat.of (C ⋆ D)
  map F := (mapPair F.toFunctor (𝟭 D)).toCatHom
  map₂ := (mapWhiskerRight ·.toNatTrans _ |>.toCatHom₂)
  mapId D := Cat.Hom.isoMk <| mapPairId
  mapComp _ _ := Cat.Hom.isoMk <| mapCompLeft D _ _
  map₂_whisker_left := by intros; exact congr($(mapWhiskerRight_whiskerLeft D _ _).toCatHom₂)
  map₂_whisker_right := by intros; exact congr($(mapWhiskerRight_whiskerRight D _ _).toCatHom₂)
  map₂_associator := by intros; exact congr($(mapWhiskerRight_associator_hom D _ _ _).toCatHom₂)
  map₂_left_unitor := by intros; exact congr($(mapWhiskerRight_leftUnitor_hom D _).toCatHom₂)
  map₂_right_unitor := by intros; exact congr($(mapWhiskerRight_rightUnitor_hom D _).toCatHom₂)

end CategoryTheory.Join
