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

/-- The structural isomorphism for composition of `pseudoFunctorRight`. -/
def prelaxFunctorRight.mapCompRight (C : Type u₁) [Category.{v₁} C] {x y z : Cat.{v₂, u₂}}
    (f : x ⟶ y) (g : y ⟶ z) :
    (prelaxFunctorRight C).map (f ≫ g) ≅
    (prelaxFunctorRight C).map f ≫ (prelaxFunctorRight C).map g :=
  mapIsoWhiskerRight (Functor.leftUnitor _).symm _ ≪≫ mapPairComp (𝟭 C) f (𝟭 C) g

/-- The structural isomorphism for composition of `pseudoFunctorLeft`. -/
def prelaxFunctorLeft.mapCompLeft (D : Type u₂) [Category.{v₂} D] {x y z : Cat.{v₁, u₁}}
    (f : x ⟶ y) (g : y ⟶ z) :
    (prelaxFunctorLeft D).map (f ≫ g) ≅
    (prelaxFunctorLeft D).map f ≫ (prelaxFunctorLeft D).map g :=
  mapIsoWhiskerLeft _ (Functor.leftUnitor _).symm ≪≫ mapPairComp f (𝟭 D) g (𝟭 D)

lemma prelaxFunctorRight.map₂_whisker_left (C : Type u₁) [Category.{v₁} C]
    {a b c : Cat.{v₂, u₂}} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    (prelaxFunctorRight C).map₂ (f ◁ η) =
      (mapCompRight C f g).hom ≫ (prelaxFunctorRight C).map f ◁ (prelaxFunctorRight C).map₂ η ≫
      (mapCompRight C f h).inv := by
  apply natTrans_ext <;>
  ext <;>
  ( simp only [prelaxFunctorRight_toPrelaxFunctorStruct_toPrefunctor_obj, Cat.of_α,
    prelaxFunctorRight_toPrelaxFunctorStruct_toPrefunctor_map, Functor.comp_obj, inclLeft_obj,
    mapPair_obj_left, Functor.id_obj, Bicategory.whiskerLeft,
    prelaxFunctorRight_toPrelaxFunctorStruct_map₂, whiskerLeft_app, mapWhiskerLeft_app,
    mapCompRight, Iso.trans_hom, Iso.trans_inv, Category.assoc]
    repeat rw [NatTrans.comp_app]
    simp )

lemma prelaxFunctorLeft.map₂_whisker_left (D : Type u₂) [Category.{v₂} D]
    {a b c : Cat.{v₁, u₁}} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    (prelaxFunctorLeft D).map₂ (f ◁ η) =
      (mapCompLeft D f g).hom ≫ (prelaxFunctorLeft D).map f ◁ (prelaxFunctorLeft D).map₂ η ≫
      (mapCompLeft D f h).inv := by
  apply natTrans_ext <;>
  ext <;>
  ( simp only [prelaxFunctorLeft_toPrelaxFunctorStruct_toPrefunctor_obj, Cat.of_α,
    prelaxFunctorLeft_toPrelaxFunctorStruct_toPrefunctor_map, Functor.comp_obj, inclRight_obj,
    mapPair_obj_left, Functor.id_obj, Bicategory.whiskerLeft,
    prelaxFunctorRight_toPrelaxFunctorStruct_map₂, whiskerLeft_app, mapWhiskerLeft_app,
    mapCompLeft, Iso.trans_hom, Iso.trans_inv, Category.assoc]
    repeat rw [NatTrans.comp_app]
    simp )

lemma prelaxFunctorRight.map₂_whisker_right (C : Type u₁) [Category.{v₁} C]
    {a b c : Cat.{v₂, u₂}} {f g: a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (prelaxFunctorRight C).map₂ (η ▷ h) =
      (mapCompRight C f h).hom ≫ (prelaxFunctorRight C).map₂ η ▷ (prelaxFunctorRight C).map h ≫
      (mapCompRight C g h).inv := by
  apply natTrans_ext <;>
  ext <;>
  ( simp only [prelaxFunctorRight_toPrelaxFunctorStruct_toPrefunctor_obj, Cat.of_α,
    prelaxFunctorRight_toPrelaxFunctorStruct_toPrefunctor_map, Functor.comp_obj, inclLeft_obj,
    mapPair_obj_left, Functor.id_obj, Bicategory.whiskerLeft,
    prelaxFunctorRight_toPrelaxFunctorStruct_map₂, whiskerLeft_app, mapWhiskerLeft_app,
    mapCompRight, Iso.trans_hom, Iso.trans_inv, Category.assoc]
    repeat rw [NatTrans.comp_app]
    simp )

lemma prelaxFunctorLeft.map₂_whisker_right (D : Type u₂) [Category.{v₂} D]
    {a b c : Cat.{v₁, u₁}} {f g: a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (prelaxFunctorLeft D).map₂ (η ▷ h) =
      (mapCompLeft D f h).hom ≫ (prelaxFunctorLeft D).map₂ η ▷ (prelaxFunctorLeft D).map h ≫
      (mapCompLeft D g h).inv := by
  apply natTrans_ext <;>
  ext <;>
  ( simp only [prelaxFunctorLeft_toPrelaxFunctorStruct_toPrefunctor_obj, Cat.of_α,
    prelaxFunctorLeft_toPrelaxFunctorStruct_toPrefunctor_map, Functor.comp_obj, inclRight_obj,
    mapPair_obj_left, Functor.id_obj, Bicategory.whiskerLeft,
    prelaxFunctorRight_toPrelaxFunctorStruct_map₂, whiskerLeft_app, mapWhiskerLeft_app,
    mapCompLeft, Iso.trans_hom, Iso.trans_inv, Category.assoc]
    repeat rw [NatTrans.comp_app]
    simp )

lemma prelaxFunctorRight.map₂_associator (C : Type u₁) [Category.{v₁} C]
    {a b c d : Cat.{v₂, u₂}} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (prelaxFunctorRight C).map₂ (α_ f g h).hom =
      (mapCompRight C (f ≫ g) h).hom ≫ (mapCompRight C f g).hom ▷ (prelaxFunctorRight C).map h ≫
      (α_ ((prelaxFunctorRight C).map f) ((prelaxFunctorRight C).map g)
        ((prelaxFunctorRight C).map h)).hom ≫
      (prelaxFunctorRight C).map f ◁ (mapCompRight C g h).inv ≫ (mapCompRight C f (g ≫ h)).inv := by
  apply natTrans_ext <;>
  ext <;>
  ( simp only [prelaxFunctorRight_toPrelaxFunctorStruct_toPrefunctor_obj, Cat.of_α,
    prelaxFunctorRight_toPrelaxFunctorStruct_toPrefunctor_map, Functor.comp_obj, inclRight_obj,
    mapPair_obj_left, Cat.comp_obj, associator, prelaxFunctorRight_toPrelaxFunctorStruct_map₂,
    whiskerLeft_app, mapWhiskerRight_app, Functor.associator_hom_app, Functor.map_id, mapCompRight,
    Iso.trans_hom, mapIsoWhiskerLeft_hom, Iso.symm_hom, comp_whiskerRight, Bicategory.whiskerLeft,
    Iso.trans_inv, Category.assoc]
    repeat rw [NatTrans.comp_app]
    simp only [mapPair_obj_left, Functor.id_obj, Functor.comp_obj, mapWhiskerLeft_app,
      Functor.leftUnitor_inv_app, Functor.map_id, inclLeft_obj, Cat.comp_obj, Cat.of_α,
      mapPairComp_hom_app_left, whiskerLeft_app, Functor.associator_hom_app, whiskerLeft_app,
      Cat.comp_app, mapPairComp_inv_app_left, mapIsoWhiskerLeft_inv_app, Iso.symm_inv,
      Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp]
    simp )


lemma prelaxFunctorLeft.map₂_associator (D : Type u₂) [Category.{v₂} D]
    {a b c d: Cat.{v₁, u₁}} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (prelaxFunctorLeft D).map₂ (α_ f g h).hom =
      (mapCompLeft D (f ≫ g) h).hom ≫ (mapCompLeft D f g).hom ▷ (prelaxFunctorLeft D).map h ≫
      (α_ ((prelaxFunctorLeft D).map f) ((prelaxFunctorLeft D).map g)
        ((prelaxFunctorLeft D).map h)).hom ≫
      (prelaxFunctorLeft D).map f ◁ (mapCompLeft D g h).inv ≫ (mapCompLeft D f (g ≫ h)).inv := by
  apply natTrans_ext <;>
  ext <;>
  ( simp only [prelaxFunctorLeft_toPrelaxFunctorStruct_toPrefunctor_obj, Cat.of_α,
    prelaxFunctorLeft_toPrelaxFunctorStruct_toPrefunctor_map, Functor.comp_obj, inclLeft_obj,
    mapPair_obj_left, Cat.comp_obj, associator, prelaxFunctorLeft_toPrelaxFunctorStruct_map₂,
    whiskerLeft_app, mapWhiskerRight_app, Functor.associator_hom_app, Functor.map_id, mapCompLeft,
    Iso.trans_hom, mapIsoWhiskerLeft_hom, Iso.symm_hom, comp_whiskerRight, Bicategory.whiskerLeft,
    Iso.trans_inv, Category.assoc]
    repeat rw [NatTrans.comp_app]
    simp only [mapPair_obj_left, Functor.id_obj, Functor.comp_obj, mapWhiskerLeft_app,
      Functor.leftUnitor_inv_app, Functor.map_id, inclLeft_obj, Cat.comp_obj, Cat.of_α,
      mapPairComp_hom_app_left, whiskerLeft_app, Functor.associator_hom_app, whiskerLeft_app,
      Cat.comp_app, mapPairComp_inv_app_left, mapIsoWhiskerLeft_inv_app, Iso.symm_inv,
      Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp]
    simp )

open prelaxFunctorRight in
/-- The pseudofunctor sending `D` to `C ⋆ D`. -/
def pseudofunctorRight (C : Type u₁) [Category.{v₁} C] :
    Pseudofunctor Cat.{v₂, u₂} Cat.{max v₁ v₂, max u₁ u₂} where
  toPrelaxFunctor := prelaxFunctorRight C
  mapId D := mapPairId
  mapComp := mapCompRight C
  map₂_whisker_left := map₂_whisker_left C
  map₂_whisker_right := map₂_whisker_right C
  map₂_associator := map₂_associator C
  map₂_left_unitor {_ _} f := by
    apply NatTrans.ext
    ext x
    cases x <;>
      ( repeat rw [NatTrans.comp_app]
        simp only [prelaxFunctorRight_toPrelaxFunctorStruct_toPrefunctor_obj, Cat.of_α,
          prelaxFunctorRight_toPrelaxFunctorStruct_toPrefunctor_map, mapPair_obj_left,
          Functor.id_obj, leftUnitor, prelaxFunctorRight_toPrelaxFunctorStruct_map₂,
          mapWhiskerLeft_app, Cat.comp_obj, mapCompRight, Iso.trans_hom, Cat.id_obj,
          Cat.whiskerRight_app, mapPairId_hom_app, Functor.map_id, Functor.leftUnitor_hom_app,
          Category.comp_id]
        repeat rw [NatTrans.comp_app]
        simp )
  map₂_right_unitor {_ _} g := by
    apply NatTrans.ext
    ext x
    cases x <;>
      ( repeat rw [NatTrans.comp_app]
        simp only [prelaxFunctorRight_toPrelaxFunctorStruct_toPrefunctor_obj, Cat.of_α,
          prelaxFunctorRight_toPrelaxFunctorStruct_toPrefunctor_map, mapPair_obj_left,
          Functor.id_obj, rightUnitor, prelaxFunctorRight_toPrelaxFunctorStruct_map₂,
          mapWhiskerLeft_app, Cat.comp_obj, mapCompRight, Iso.trans_hom, Cat.id_obj,
          Cat.whiskerRight_app, mapPairId_hom_app, Functor.map_id, Functor.rightUnitor_hom_app,
          Category.comp_id]
        repeat rw [NatTrans.comp_app]
        simp )

open prelaxFunctorLeft in
/-- The pseudofunctor sending `C` to `C ⋆ D`. -/
def pseudofunctorLeft (D : Type u₂) [Category.{v₂} D] :
    Pseudofunctor Cat.{v₁, u₁} Cat.{max v₁ v₂, max u₁ u₂} where
  toPrelaxFunctor := prelaxFunctorLeft D
  mapId D := mapPairId
  mapComp := mapCompLeft D
  map₂_whisker_left := map₂_whisker_left D
  map₂_whisker_right := map₂_whisker_right D
  map₂_associator := map₂_associator D
  map₂_left_unitor {_ _} f := by
    apply NatTrans.ext
    ext x
    cases x <;>
      ( repeat rw [NatTrans.comp_app]
        simp only [prelaxFunctorLeft_toPrelaxFunctorStruct_toPrefunctor_obj, Cat.of_α,
          prelaxFunctorLeft_toPrelaxFunctorStruct_toPrefunctor_map, mapPair_obj_left,
          Functor.id_obj, leftUnitor, prelaxFunctorLeft_toPrelaxFunctorStruct_map₂,
          mapWhiskerLeft_app, Cat.comp_obj, mapCompLeft, Iso.trans_hom, Cat.id_obj,
          Cat.whiskerRight_app, mapPairId_hom_app, Functor.map_id, Functor.leftUnitor_hom_app,
          Category.comp_id]
        repeat rw [NatTrans.comp_app]
        simp )
  map₂_right_unitor {_ _} g := by
    apply NatTrans.ext
    ext x
    cases x <;>
      ( repeat rw [NatTrans.comp_app]
        simp only [prelaxFunctorLeft_toPrelaxFunctorStruct_toPrefunctor_obj, Cat.of_α,
          prelaxFunctorLeft_toPrelaxFunctorStruct_toPrefunctor_map, mapPair_obj_left,
          Functor.id_obj, rightUnitor, prelaxFunctorLeft_toPrelaxFunctorStruct_map₂,
          mapWhiskerLeft_app, Cat.comp_obj, mapCompLeft, Iso.trans_hom, Cat.id_obj,
          Cat.whiskerRight_app, mapPairId_hom_app, Functor.map_id, Functor.rightUnitor_hom_app,
          Category.comp_id]
        repeat rw [NatTrans.comp_app]
        simp )

end CategoryTheory.Join
