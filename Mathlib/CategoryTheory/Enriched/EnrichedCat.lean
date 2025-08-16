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

open EnrichedCategory ForgetEnrichment

variable {C D E E' : EnrichedCat.{w, v, u} V}

/-- Whisker a `V`-enriched natural transformation on the left. -/
@[simps!]
def whiskerLeft
    (F : EnrichedFunctor V C D) {G H : EnrichedFunctor V D E} (α : G.forget ⟶ H.forget) :
    (F.comp V G).forget ⟶ (F.comp V H).forget :=
  (F.forgetComp G).hom ≫ F.forget.whiskerLeft α ≫ (F.forgetComp H).inv

/-- Whisker a `V`-enriched natural transformation on the right. -/
@[simps!]
def whiskerRight
    {F G : EnrichedFunctor V C D} (α : F.forget ⟶ G.forget) (H : EnrichedFunctor V D E) :
    (F.comp V H).forget ⟶ (G.comp V H).forget :=
  (F.forgetComp H).hom ≫ Functor.whiskerRight α H.forget ≫ (G.forgetComp H).inv

/-- Composing the `V`-enriched identity functor with any functor is isomorphic to that functor. -/
@[simps!]
def leftUnitor (F : EnrichedFunctor V C D) : (EnrichedFunctor.id V _).comp V F ≅ F :=
  EnrichedFunctor.isoMk <| (EnrichedFunctor.id V C).forgetComp F ≪≫
    Functor.isoWhiskerRight (EnrichedFunctor.forgetId V C) _ ≪≫ Functor.leftUnitor F.forget

/-- Composing any `V`-enriched functor with the identity functor is isomorphic to the former
functor. -/
@[simps!]
def rightUnitor (F : EnrichedFunctor V C D) :
    EnrichedFunctor.comp V F (EnrichedFunctor.id V _) ≅ F :=
  EnrichedFunctor.isoMk <| F.forgetComp _ ≪≫
    Functor.isoWhiskerLeft _ (EnrichedFunctor.forgetId V D) ≪≫ Functor.rightUnitor F.forget

/-- Composition of `V`-enriched functors is associative up to isomorphism. -/
@[simps!]
def associator (F : EnrichedFunctor V C D) (G : EnrichedFunctor V D E)
    (H : EnrichedFunctor V E E') :
    EnrichedFunctor.comp V (EnrichedFunctor.comp V F G) H ≅
    EnrichedFunctor.comp V F (EnrichedFunctor.comp V G H) :=
  EnrichedFunctor.isoMk <| (F.comp V G).forgetComp H ≪≫
    Functor.isoWhiskerRight (F.forgetComp G) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (G.forgetComp H).symm ≪≫
    (F.forgetComp _).symm

lemma comp_whiskerRight {F G H : EnrichedFunctor V C D} (α : F ⟶ G)
    (β : G ⟶ H) (I : EnrichedFunctor V D E) :
    whiskerRight V (α ≫ β) I = whiskerRight V α I ≫ whiskerRight V β I := by
  refine EnrichedFunctor.hom_ext fun X => ?_
  simp only [EnrichedFunctor.forget, EnrichedFunctor.comp_obj, EnrichedFunctor.comp_map,
    whiskerRight_app, to_of, NatTrans.comp_app, homTo_comp, Category.assoc,
    EnrichedFunctor.map_comp, Category.comp_id]
  simp [← ForgetEnrichment.homOf_comp]

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
    refine EnrichedFunctor.hom_ext fun X => ?_
    simp [EnrichedFunctor.forget]
  triangle F G := by
    refine EnrichedFunctor.hom_ext fun X => ?_
    simp [EnrichedFunctor.forget]
  whiskerLeft_id F G := by
    refine EnrichedFunctor.hom_ext fun X => ?_
    simp [EnrichedFunctor.forget]
  id_whiskerLeft α := by
    refine EnrichedFunctor.hom_ext fun X => ?_
    simp [EnrichedFunctor.forget]
  comp_whiskerLeft F G H I α := by
    refine EnrichedFunctor.hom_ext fun X => ?_
    simp [EnrichedFunctor.forget]
  id_whiskerRight F G := by
    refine EnrichedFunctor.hom_ext fun X => ?_
    simp [EnrichedFunctor.forget]
  comp_whiskerRight := comp_whiskerRight V
  whiskerRight_id α := by
    refine EnrichedFunctor.hom_ext fun X => ?_
    simp [EnrichedFunctor.forget]
  whiskerLeft_comp F G H I α β := by
    refine EnrichedFunctor.hom_ext fun X => ?_
    simp [EnrichedFunctor.forget]
  whiskerRight_comp α F G := by
    refine EnrichedFunctor.hom_ext fun X => ?_
    simp [EnrichedFunctor.forget]
  whisker_assoc F G H α J := by
    refine EnrichedFunctor.hom_ext fun X => ?_
    simp [EnrichedFunctor.forget]
  whisker_exchange {_} {_} {_} {F} {G} {H} {J} α β := by
    refine EnrichedFunctor.hom_ext fun X => ?_
    simp only [EnrichedFunctor.forget, EnrichedFunctor.comp_obj, EnrichedFunctor.comp_map,
      EnrichedFunctor.category_comp, NatTrans.comp_app, whiskerRight_app, to_of, Category.comp_id,
      whiskerLeft_app]
    exact (β.naturality (α.app (ForgetEnrichment.of V X))).symm

end EnrichedCat

end CategoryTheory
