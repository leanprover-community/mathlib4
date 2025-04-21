/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Join.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# Pseudofunctoriality of categorical joins

In this file, we promote the join construction to two pseudofunctors
`Join.pseudofunctorLeft` and `Join.pseudoFunctorRight`, expressing its pseudofunctoriality in
each variable.

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Join

open Bicategory

/-- The `PrelaxFunctor` structure underlying `Join.pseudofunctorRight`. -/
@[simps]
def prelaxFunctorRight (C : Type u₁) [Category.{v₁} C] :
    PrelaxFunctor Cat.{v₂, u₂} Cat.{max v₁ v₂, max u₁ u₂} where
  obj D := Cat.of (C ⋆ D)
  map F := mapPair (𝟭 C) F
  map₂ := mapWhiskerLeft _
  map₂_id {x y} f := by
    apply natTrans_ext <;> aesop_cat
  map₂_comp η θ := by
    apply natTrans_ext <;>
    ( dsimp
      rw [← mapWhiskerLeft_comp] )

/-- The `PrelaxFunctor` structure underlying `Join.pseudofunctorLeft`. -/
@[simps]
def prelaxFunctorLeft (D : Type u₂) [Category.{v₂} D] :
    PrelaxFunctor Cat.{v₁, u₁} Cat.{max v₁ v₂, max u₁ u₂} where
  obj C := Cat.of (C ⋆ D)
  map F := mapPair F (𝟭 D)
  map₂ := (mapWhiskerRight · _)
  map₂_id {x y} f := by
    apply natTrans_ext <;> aesop_cat
  map₂_comp η θ := by
    apply natTrans_ext <;>
    ( dsimp
      rw [← mapWhiskerRight_comp] )

-- The proof gets too slow if we put it in a single `pseudofunctor` constructor,
-- so we break down the component proofs for the pseudofunctors over several lemmas.

section
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]


variable (A) in
/-- The structural isomorphism for composition of `pseudoFunctorRight`. -/
def mapCompRight (F : B ⥤ C) (G : C ⥤ D) :
    mapPair (𝟭 A) (F ⋙ G) ≅ mapPair (𝟭 A) F ⋙ mapPair (𝟭 A) G :=
  mapIsoWhiskerRight (Functor.leftUnitor _).symm _ ≪≫ mapPairComp (𝟭 A) F (𝟭 A) G

variable (D) in
/-- The structural isomorphism for composition of `pseudoFunctorLeft`. -/
def mapCompLeft (F : A ⥤ B) (G : B ⥤ C) :
    mapPair (F ⋙ G) (𝟭 D) ≅ mapPair F (𝟭 D) ⋙ mapPair G (𝟭 D) :=
  mapIsoWhiskerLeft _ (Functor.leftUnitor _).symm ≪≫ mapPairComp F (𝟭 D) G (𝟭 D)

variable (A) in
@[reassoc]
lemma mapWhiskerLeft_whiskerLeft (F : B ⥤ C) {G H : C ⥤ D} (η : G ⟶ H) :
    mapWhiskerLeft _ (whiskerLeft F η) =
      (mapCompRight A F G).hom ≫ whiskerLeft (mapPair (𝟭 A) F) (mapWhiskerLeft _ η) ≫
      (mapCompRight A F H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

variable (D) in
@[reassoc]
lemma mapWhiskerRight_whiskerLeft (F : A ⥤ B) {G H : B ⥤ C} (η : G ⟶ H) :
    mapWhiskerRight (whiskerLeft F η) (𝟭 D) =
      (mapCompLeft D F G).hom ≫ whiskerLeft (mapPair F (𝟭 D)) (mapWhiskerRight η _) ≫
      (mapCompLeft D F H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

variable (A) in
@[reassoc]
lemma mapWhiskerLeft_whiskerRight {F G: B ⥤ C} (η : F ⟶ G) (H : C ⥤ D) :
    mapWhiskerLeft _ (whiskerRight η H) =
      (mapCompRight A F H).hom ≫ whiskerRight (mapWhiskerLeft _ η) (mapPair (𝟭 A) H) ≫
      (mapCompRight A G H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

variable (D) in
@[reassoc]
lemma mapWhiskerRight_whiskerRight {F G: A ⥤ B} (η : F ⟶ G) (H : B ⥤ C) :
    mapWhiskerRight (whiskerRight η H) _ =
      (mapCompLeft D F H).hom ≫ whiskerRight (mapWhiskerRight η _) (mapPair H (𝟭 D)) ≫
      (mapCompLeft D G H).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

variable {E : Type*} [Category E]

variable (A) in
@[reassoc]
lemma mapWhiskerLeft_associator (F : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E) :
    mapWhiskerLeft _ (F.associator G H).hom =
      (mapCompRight A (F ⋙ G) H).hom ≫ whiskerRight (mapCompRight A F G).hom (mapPair (𝟭 A) H) ≫
        ((mapPair (𝟭 A) F).associator (mapPair (𝟭 A) G) (mapPair (𝟭 A) H)).hom ≫
      whiskerLeft (mapPair (𝟭 A) F) (mapCompRight A G H).inv ≫ (mapCompRight A F (G ⋙ H)).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompRight]

variable (E) in
lemma mapWhiskerRight_associator (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    mapWhiskerRight (F.associator G H).hom _ =
      (mapCompLeft E (F ⋙ G) H).hom ≫ whiskerRight (mapCompLeft E F G).hom (mapPair H (𝟭 E)) ≫
        ((mapPair F (𝟭 E)).associator (mapPair G (𝟭 E)) (mapPair H (𝟭 E))).hom ≫
      whiskerLeft (mapPair F (𝟭 E)) (mapCompLeft E G H).inv ≫ (mapCompLeft E F (G ⋙ H)).inv := by
  apply natTrans_ext <;> ext <;> simp [mapCompLeft]

end

/-- The pseudofunctor sending `D` to `C ⋆ D`. -/
@[simps!]
def pseudofunctorRight (C : Type u₁) [Category.{v₁} C] :
    Pseudofunctor Cat.{v₂, u₂} Cat.{max v₁ v₂, max u₁ u₂} where
  toPrelaxFunctor := prelaxFunctorRight C
  mapId D := mapPairId
  mapComp := mapCompRight C
  map₂_whisker_left := mapWhiskerLeft_whiskerLeft C
  map₂_whisker_right := mapWhiskerLeft_whiskerRight C
  map₂_associator := mapWhiskerLeft_associator C
  map₂_left_unitor {_ _} f := by
    apply NatTrans.ext
    ext x
    cases x
    all_goals
      dsimp [mapCompRight, mapCompLeft, leftUnitor]
      simp only [mapWhiskerLeft_app, Functor.id_obj, Category.assoc]
      repeat rw [NatTrans.comp_app]
      simp
  map₂_right_unitor {_ _} g := by
    apply NatTrans.ext
    ext x
    cases x
    all_goals
      dsimp [mapCompRight, mapCompLeft, rightUnitor]
      simp only [mapWhiskerLeft_app, Functor.id_obj, Category.assoc]
      repeat rw [NatTrans.comp_app]
      simp

/-- The pseudofunctor sending `C` to `C ⋆ D`. -/
@[simps!]
def pseudofunctorLeft (D : Type u₂) [Category.{v₂} D] :
    Pseudofunctor Cat.{v₁, u₁} Cat.{max v₁ v₂, max u₁ u₂} where
  toPrelaxFunctor := prelaxFunctorLeft D
  mapId D := mapPairId
  mapComp := mapCompLeft D
  map₂_whisker_left := mapWhiskerRight_whiskerLeft D
  map₂_whisker_right := mapWhiskerRight_whiskerRight D
  map₂_associator := mapWhiskerRight_associator D
  map₂_left_unitor {_ _} f := by
    apply NatTrans.ext
    ext x
    cases x
    all_goals
      dsimp [mapCompRight, mapCompLeft, leftUnitor]
      simp only [mapWhiskerLeft_app, Functor.id_obj, Category.assoc]
      repeat rw [NatTrans.comp_app]
      simp
  map₂_right_unitor {_ _} g := by
    apply NatTrans.ext
    ext x
    cases x
    all_goals
      dsimp [mapCompRight, mapCompLeft, rightUnitor]
      simp only [mapWhiskerLeft_app, Functor.id_obj, Category.assoc]
      repeat rw [NatTrans.comp_app]
      simp

end CategoryTheory.Join
