/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# The bicategory of `V`-enriched categories

We define the bicategory `EnrichedCat V` of (bundled) `V`-enriched categories for a fixed monoidal
category `V`.

## Future work

* Define change of base and `ForgetEnrichment` as 2-functors.
* Define the bicategory of enriched ordinary categories.
-/


universe w v v₂ u u₁ u₂ u₃

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

variable {V} {C : Type u} [EnrichedCategory V C] {D : Type u₁} [EnrichedCategory V D]
  {E : Type u₂} [EnrichedCategory V E] {E' : Type u₃} [EnrichedCategory V E']

/-- Whisker a `V`-enriched natural transformation on the left. -/
@[simps!]
def whiskerLeft
    (F : EnrichedFunctor V C D) {G H : EnrichedFunctor V D E} (α : G ⟶ H) :
    F.comp V G ⟶ F.comp V H :=
  ⟨(F.forgetComp G).hom ≫ F.forget.whiskerLeft α.out ≫ (F.forgetComp H).inv⟩

/-- Whisker a `V`-enriched natural transformation on the right. -/
@[simps!]
def whiskerRight
    {F G : EnrichedFunctor V C D} (α : F ⟶ G) (H : EnrichedFunctor V D E) :
    F.comp V H ⟶ G.comp V H :=
  ⟨(F.forgetComp H).hom ≫ Functor.whiskerRight α.out H.forget ≫ (G.forgetComp H).inv⟩

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
    whiskerRight ⟨α.out ≫ β.out⟩ I = whiskerRight α I ≫ whiskerRight β I := by
  ext X
  simp only [whiskerRight_out_app, NatTrans.comp_app, EnrichedFunctor.category_comp_out,
    EnrichedFunctor.forget, EnrichedFunctor.comp_obj, EnrichedFunctor.comp_map]
  simp [← ForgetEnrichment.homOf_comp]

lemma whisker_exchange {F G : EnrichedFunctor V C D} {H I : EnrichedFunctor V D E}
    (α : F ⟶ G) (β : H ⟶ I) :
    whiskerLeft F β ≫ whiskerRight α I = whiskerRight α H ≫ whiskerLeft G β := by
  ext X
  simp only [EnrichedFunctor.forget_obj, EnrichedFunctor.comp_obj,
    EnrichedFunctor.category_comp_out, NatTrans.comp_app, whiskerLeft_out_app,
    whiskerRight_out_app]
  exact (β.out.naturality (α.out.app (ForgetEnrichment.of V X))).symm

/-- The bicategory structure on `EnrichedCat V` for a monoidal category `V`. -/
instance bicategory : Bicategory (EnrichedCat.{w, v, u} V) where
  Hom C D := EnrichedFunctor V C D
  id C := EnrichedFunctor.id V C
  comp F G := EnrichedFunctor.comp V F G
  whiskerLeft F G H := whiskerLeft F
  whiskerRight := whiskerRight
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  comp_whiskerRight := comp_whiskerRight
  whisker_exchange := whisker_exchange

-- TODO replace `mapId` and `mapComp` by handcrafted pointwise iso so that
-- we don't need `erw`
def forget : Pseudofunctor (EnrichedCat.{w, v, u} V) Cat where
  obj C := .of <| ForgetEnrichment V C
  map F := (EnrichedFunctor.forget F).toCatHom
  map₂ α := α.out
  mapId C := NatIso.ofComponents (by cat_disch) fun F => by
    simp [Functor.toCatHom]
    erw [EnrichedFunctor.id_map]
    simp
  mapComp F G := NatIso.ofComponents (by cat_disch) fun H => by
    simp [Functor.toCatHom]
    erw [EnrichedFunctor.comp_map]

variable (W : Type v₂) [Category.{w} W] [MonoidalCategory W]

variable {W} in
def transportEnrichment (F : V ⥤ W) [F.LaxMonoidal] :
    Pseudofunctor (EnrichedCat.{w, v, u} V) (EnrichedCat W) where
  obj C := .of W <| TransportEnrichment F C
  map F := by { _ }

end EnrichedCat

end CategoryTheory
