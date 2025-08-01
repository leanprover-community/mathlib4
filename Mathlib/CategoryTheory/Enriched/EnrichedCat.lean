/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# The bicategory of `V`-enriched categories

We define the bicategory `EnrichedCat V` of (bundled) `V`-enriched categories for a fixed monoidal
category `V`.

## Future work

* Define change of base and `ForgetEnrichment` as 2-functors.
* Define the bicategory of enriched ordinary categories.
-/


universe w v u u₁ u₂

namespace CategoryTheory

open MonoidalCategory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

/-- Category of `V`-enriched categories for a monoidal category `V`. -/
def EnrichedCat := Bundled (EnrichedCategory.{w, v, u} V)

namespace EnrichedCat

instance : CoeSort (EnrichedCat V) (Type u) :=
  ⟨Bundled.α⟩

instance str (C : EnrichedCat.{w, v, u} V) : EnrichedCategory.{w, v, u} V C :=
  Bundled.str C

/-- Construct a bundled `EnrichedCat` from the underlying type and the typeclass. -/
def of (C : Type u) [EnrichedCategory.{w} V C] : EnrichedCat.{w, v, u} V :=
  Bundled.of C

open EnrichedCategory

variable {C D E E' : EnrichedCat.{w, v, u} V}

/-- Whisker a `V`-enriched natural transformation on the left. -/
@[simps]
def whiskerLeft
    (F : EnrichedFunctor V C D) {G H : EnrichedFunctor V D E} (α : EnrichedNatTrans G H) :
    EnrichedFunctor.comp V F G ⟶ EnrichedFunctor.comp V F H where
  app X := α.app (F.obj X)
  naturality X Y := by
    simp only [EnrichedFunctor.comp_obj, F.comp_map]
    rw [← whiskerLeft_comp_tensorHom, Category.assoc, ← GradedNatTrans.naturality α,
     ← whiskerRight_comp_tensorHom]
    simp

/-- Whisker a `V`-enriched natural transformation on the right. -/
@[simps]
def whiskerRight
    {F G : EnrichedFunctor V C D} (α : EnrichedNatTrans F G) (H : EnrichedFunctor V D E) :
    EnrichedFunctor.comp V F H ⟶ EnrichedFunctor.comp V G H where
  app X := α.app X ≫ H.map _ _
  naturality X Y := by
    simp only [Category.assoc, EnrichedFunctor.comp_obj, F.comp_map, tensor_comp]
    rw [← H.map_comp, reassoc_of% (GradedNatTrans.naturality α X Y)]
    simp

/-- Composing the `V`-enriched identity functor with any functor is isomorphic to that functor. -/
def leftUnitor (F : EnrichedFunctor V C D) :
    EnrichedFunctor.comp V (EnrichedFunctor.id V _) F ≅ F :=
  EnrichedFunctor.isoOfComponents (fun X => Iso.refl _) fun X Y => by
    simp only [EnrichedFunctor.comp_obj, EnrichedFunctor.id_obj, ForgetEnrichment.to_of,
      EnrichedFunctor.comp_map, EnrichedFunctor.id_map, Category.id_comp, Iso.refl_hom,
      ForgetEnrichment.homTo_id]
    rw [tensorHom_def, Category.assoc, (Iso.inv_comp_eq _).mp (e_comp_id ..),
      tensorHom_def', Category.assoc, (Iso.inv_comp_eq _).mp (e_id_comp ..)]
    simp

/-- Composing any `V`-enriched functor with the identity functor is isomorphic to the former
functor. -/
def rightUnitor (F : EnrichedFunctor V C D) :
    EnrichedFunctor.comp V F (EnrichedFunctor.id V _) ≅ F :=
  EnrichedFunctor.isoOfComponents (fun X => Iso.refl _) fun X Y => by
    simp only [EnrichedFunctor.comp_obj, EnrichedFunctor.id_obj, ForgetEnrichment.to_of,
      EnrichedFunctor.comp_map, EnrichedFunctor.id_map, Category.comp_id, Iso.refl_hom,
      ForgetEnrichment.homTo_id]
    rw [tensorHom_def, Category.assoc, (Iso.inv_comp_eq _).mp (e_comp_id ..),
      tensorHom_def', Category.assoc, (Iso.inv_comp_eq _).mp (e_id_comp ..)]
    simp

/-- Composition of `V`-enriched functors is associative up to isomorphism. -/
def associator (F : EnrichedFunctor V C D) (G : EnrichedFunctor V D E)
    (H : EnrichedFunctor V E E') :
    EnrichedFunctor.comp V (EnrichedFunctor.comp V F G) H ≅
    EnrichedFunctor.comp V F (EnrichedFunctor.comp V G H) :=
  EnrichedFunctor.isoOfComponents (fun X => Iso.refl _) fun X Y => by
    simp only [EnrichedFunctor.comp_obj, ForgetEnrichment.to_of, EnrichedFunctor.comp_map,
      Category.assoc, Iso.refl_hom, ForgetEnrichment.homTo_id]
    rw [tensorHom_def, Category.assoc, (Iso.inv_comp_eq _).mp (e_comp_id ..),
      tensorHom_def', Category.assoc, (Iso.inv_comp_eq _).mp (e_id_comp ..)]
    simp

/-- The bicategory structure on `EnrichedCat V` for a monoidal category `V`. -/
instance bicategory : Bicategory (EnrichedCat.{w, v, u} V) where
  Hom C D := EnrichedFunctor V C D
  id C := EnrichedFunctor.id V C
  comp F G := EnrichedFunctor.comp V F G
  whiskerLeft F G H α := whiskerLeft V F α
  whiskerRight α H := whiskerRight V α H
  associator F G H := associator V F G H
  leftUnitor F := leftUnitor V F
  rightUnitor F := rightUnitor V F
  pentagon F G H I := by
    refine EnrichedNatTrans.ext fun X => ?_
    simp [whiskerRight, whiskerLeft, associator, tensorHom_def]
  triangle F G := by
    refine EnrichedNatTrans.ext fun X => ?_
    simp [whiskerRight, whiskerLeft, associator, leftUnitor, rightUnitor, tensorHom_def]
  id_whiskerLeft α := by
    refine EnrichedNatTrans.ext fun X => ?_
    simp only [Center.tensorUnit_fst, EnrichedFunctor.comp_obj, EnrichedFunctor.id_obj, whiskerLeft,
      leftUnitor, EnrichedNatTrans.comp_app, EnrichedFunctor.isoOfComponents_hom_app,
      EnrichedIso.refl_hom, EnrichedFunctor.isoOfComponents_inv_app, EnrichedIso.refl_inv,
      tensorHom_def, whiskerRight_id, Category.assoc, e_comp_id, Category.comp_id,
      Iso.inv_hom_id_assoc]
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
      (Iso.inv_comp_eq _).mp (e_id_comp ..)]
    monoidal
  comp_whiskerLeft F G H I α := by
    refine EnrichedNatTrans.ext fun X => ?_
    simp only [Center.tensorUnit_fst, EnrichedFunctor.comp_obj, whiskerLeft, associator,
      EnrichedNatTrans.comp_app, EnrichedFunctor.isoOfComponents_hom_app, EnrichedIso.refl_hom,
      EnrichedFunctor.isoOfComponents_inv_app, EnrichedIso.refl_inv]
    rw [tensorHom_def', tensorHom_def]
    simp only [whiskerRight_id, Category.assoc, e_comp_id, Category.comp_id, Iso.inv_hom_id_assoc,
      id_whiskerLeft, e_id_comp]
    monoidal
  id_whiskerRight F G := by
    refine EnrichedNatTrans.ext fun X => ?_
    simp [whiskerRight]
  comp_whiskerRight α β F := by
    refine EnrichedNatTrans.ext fun X => ?_
    simp [whiskerRight]
  whiskerRight_id α := by
    refine EnrichedNatTrans.ext fun X => ?_
    simp only [Center.tensorUnit_fst, EnrichedFunctor.comp_obj, EnrichedFunctor.id_obj,
      whiskerRight, EnrichedFunctor.id_map, Category.comp_id, rightUnitor,
      EnrichedNatTrans.comp_app, EnrichedFunctor.isoOfComponents_hom_app, EnrichedIso.refl_hom,
      EnrichedFunctor.isoOfComponents_inv_app, EnrichedIso.refl_inv, tensorHom_def, whiskerRight_id,
      Category.assoc, e_comp_id, Iso.inv_hom_id_assoc]
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
      (Iso.inv_comp_eq _).mp (e_id_comp ..)]
    monoidal
  whiskerRight_comp α F G := by
    refine EnrichedNatTrans.ext fun X => ?_
    simp only [Center.tensorUnit_fst, EnrichedFunctor.comp_obj, whiskerRight,
      EnrichedFunctor.comp_map, associator, Category.assoc, EnrichedNatTrans.comp_app,
      EnrichedFunctor.isoOfComponents_inv_app, EnrichedIso.refl_inv,
      EnrichedFunctor.isoOfComponents_hom_app, EnrichedIso.refl_hom]
    rw [tensorHom_def', tensorHom_def]
    simp only [whiskerRight_id, Category.assoc, e_comp_id, Category.comp_id, Iso.inv_hom_id_assoc,
      whiskerLeft_comp, id_whiskerLeft, e_id_comp]
    monoidal
  whisker_assoc F G H α J := by
    refine EnrichedNatTrans.ext fun X => ?_
    simp only [Center.tensorUnit_fst, EnrichedFunctor.comp_obj, whiskerRight, whiskerLeft,
      associator, EnrichedNatTrans.comp_app, EnrichedFunctor.isoOfComponents_hom_app,
      EnrichedIso.refl_hom, EnrichedFunctor.isoOfComponents_inv_app, EnrichedIso.refl_inv]
    rw [tensorHom_def', tensorHom_def]
    simp only [whiskerRight_id, Category.assoc, e_comp_id, Category.comp_id, Iso.inv_hom_id_assoc,
      whiskerLeft_comp, id_whiskerLeft, e_id_comp]
    monoidal
  whisker_exchange {_} {_} {_} {F} {G} {H} {J} α β := by
    refine EnrichedNatTrans.ext fun X => ?_
    simp only [Center.tensorUnit_fst, EnrichedFunctor.comp_obj, EnrichedNatTrans.comp_app,
      whiskerLeft_app, whiskerRight_app, Iso.cancel_iso_inv_left]
    have := (Iso.eq_inv_comp _).mp (β.naturality (F.obj X) (G.obj X))
    rw [tensorHom_def', whiskerLeft_comp, Category.assoc, Category.assoc, ← tensorHom_def'_assoc,
      ← (Iso.eq_inv_comp _).mp (β.naturality (F.obj X) (G.obj X)), tensorHom_def',
      ← whiskerRight_comp_tensorHom, tensorHom_def']
    monoidal

end EnrichedCat

end CategoryTheory
