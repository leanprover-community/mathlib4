/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Preservation of zero objects and zero morphisms

We define the class `PreservesZeroMorphisms` and show basic properties.

## Main results

We provide the following results:
* Left adjoints and right adjoints preserve zero morphisms;
* full functors preserve zero morphisms;
* if both categories involved have a zero object, then a functor preserves zero morphisms if and
  only if it preserves the zero object;
* functors which preserve initial or terminal objects preserve zero morphisms.

-/


universe v u v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E]

section ZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

/-- A functor preserves zero morphisms if it sends zero morphisms to zero morphisms. -/
class PreservesZeroMorphisms (F : C ⥤ D) : Prop where
  /-- For any pair objects `F (0: X ⟶ Y) = (0 : F X ⟶ F Y)` -/
  map_zero : ∀ X Y : C, F.map (0 : X ⟶ Y) = 0 := by aesop

@[simp]
protected theorem map_zero (F : C ⥤ D) [PreservesZeroMorphisms F] (X Y : C) :
    F.map (0 : X ⟶ Y) = 0 :=
  PreservesZeroMorphisms.map_zero _ _

lemma map_isZero (F : C ⥤ D) [PreservesZeroMorphisms F] {X : C} (hX : IsZero X) :
    IsZero (F.obj X) := by
  simp only [IsZero.iff_id_eq_zero] at hX ⊢
  rw [← F.map_id, hX, F.map_zero]

theorem zero_of_map_zero (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y : C} (f : X ⟶ Y)
    (h : F.map f = 0) : f = 0 :=
  F.map_injective <| h.trans <| Eq.symm <| F.map_zero _ _

theorem map_eq_zero_iff (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y : C} {f : X ⟶ Y} :
    F.map f = 0 ↔ f = 0 :=
  ⟨F.zero_of_map_zero _, by
    rintro rfl
    exact F.map_zero _ _⟩

instance (priority := 100) preservesZeroMorphisms_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] :
    PreservesZeroMorphisms F where
  map_zero X Y := by
    let adj := Adjunction.ofIsLeftAdjoint F
    calc
      F.map (0 : X ⟶ Y) = F.map 0 ≫ F.map (adj.unit.app Y) ≫ adj.counit.app (F.obj Y) := ?_
      _ = F.map 0 ≫ F.map ((rightAdjoint F).map (0 : F.obj X ⟶ _)) ≫ adj.counit.app (F.obj Y) := ?_
      _ = 0 := ?_
    · rw [Adjunction.left_triangle_components]
      exact (Category.comp_id _).symm
    · simp only [← Category.assoc, ← F.map_comp, zero_comp]
    · simp only [Adjunction.counit_naturality, comp_zero]

instance (priority := 100) preservesZeroMorphisms_of_isRightAdjoint (G : C ⥤ D) [IsRightAdjoint G] :
    PreservesZeroMorphisms G where
  map_zero X Y := by
    let adj := Adjunction.ofIsRightAdjoint G
    calc
      G.map (0 : X ⟶ Y) = adj.unit.app (G.obj X) ≫ G.map (adj.counit.app X) ≫ G.map 0 := ?_
      _ = adj.unit.app (G.obj X) ≫ G.map ((leftAdjoint G).map (0 : _ ⟶ G.obj X)) ≫ G.map 0 := ?_
      _ = 0 := ?_
    · rw [Adjunction.right_triangle_components_assoc]
    · simp only [← G.map_comp, comp_zero]
    · simp only [id_obj, comp_obj, Adjunction.unit_naturality_assoc, zero_comp]

instance (priority := 100) preservesZeroMorphisms_of_full (F : C ⥤ D) [Full F] :
    PreservesZeroMorphisms F where
  map_zero X Y :=
    calc
      F.map (0 : X ⟶ Y) = F.map (0 ≫ F.preimage (0 : F.obj Y ⟶ F.obj Y)) := by rw [zero_comp]
      _ = 0 := by rw [F.map_comp, F.map_preimage, comp_zero]

instance preservesZeroMorphisms_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] :
    (F ⋙ G).PreservesZeroMorphisms := ⟨by simp⟩

lemma preservesZeroMorphisms_of_iso {F₁ F₂ : C ⥤ D} [F₁.PreservesZeroMorphisms] (e : F₁ ≅ F₂) :
    F₂.PreservesZeroMorphisms where
  map_zero X Y := by simp only [← cancel_epi (e.hom.app X), ← e.hom.naturality,
    F₁.map_zero, zero_comp, comp_zero]

open ZeroObject

lemma preservesZeroMorphisms_of_fac_of_essSurj (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
   [H.PreservesZeroMorphisms] [HasZeroObject C] (e : F ⋙ G ≅ H) :
    G.PreservesZeroMorphisms := ⟨by
  have := preservesZeroMorphisms_of_iso e.symm
  intro X Y
  have h : (0 : X ⟶ Y) = 0 ≫ 𝟙 (F.obj 0) ≫ 0 := by simp only [comp_zero]
  simp only [h, G.map_comp, ← F.map_id, id_zero]
  erw [(F ⋙ G).map_zero]
  simp only [zero_comp, comp_zero]⟩

instance preservesZeroMorphisms_evaluation_obj (j : D) :
    PreservesZeroMorphisms ((evaluation D C).obj j) where

instance (F : C ⥤ D ⥤ E) [∀ X, (F.obj X).PreservesZeroMorphisms] :
    F.flip.PreservesZeroMorphisms where

instance (F : C ⥤ D ⥤ E) [F.PreservesZeroMorphisms] (Y : D) :
    (F.flip.obj Y).PreservesZeroMorphisms where

omit [HasZeroMorphisms C] in
@[simp] lemma whiskerRight_zero {F G : C ⥤ D} (H : D ⥤ E) [H.PreservesZeroMorphisms] :
    whiskerRight (0 : F ⟶ G) H = 0 := by aesop_cat

end ZeroMorphisms

section ZeroObject

variable [HasZeroObject C] [HasZeroObject D]

open ZeroObject

variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)

/-- A functor that preserves zero morphisms also preserves the zero object. -/
@[simps]
def mapZeroObject [PreservesZeroMorphisms F] : F.obj 0 ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := by rw [← F.map_id, id_zero, F.map_zero, zero_comp]
  inv_hom_id := by rw [id_zero, comp_zero]

variable {F}

theorem preservesZeroMorphisms_of_map_zero_object (i : F.obj 0 ≅ 0) : PreservesZeroMorphisms F where
  map_zero X Y :=
    calc
      F.map (0 : X ⟶ Y) = F.map (0 : X ⟶ 0) ≫ F.map 0 := by rw [← Functor.map_comp, comp_zero]
      _ = F.map 0 ≫ (i.hom ≫ i.inv) ≫ F.map 0 := by rw [Iso.hom_inv_id, Category.id_comp]
      _ = 0 := by simp only [zero_of_to_zero i.hom, zero_comp, comp_zero]

instance (priority := 100) preservesZeroMorphisms_of_preserves_initial_object
    [PreservesColimit (Functor.empty.{0} C) F] : PreservesZeroMorphisms F :=
  preservesZeroMorphisms_of_map_zero_object <|
    F.mapIso HasZeroObject.zeroIsoInitial ≪≫
      PreservesInitial.iso F ≪≫ HasZeroObject.zeroIsoInitial.symm

instance (priority := 100) preservesZeroMorphisms_of_preserves_terminal_object
    [PreservesLimit (Functor.empty.{0} C) F] : PreservesZeroMorphisms F :=
  preservesZeroMorphisms_of_map_zero_object <|
    F.mapIso HasZeroObject.zeroIsoTerminal ≪≫
      PreservesTerminal.iso F ≪≫ HasZeroObject.zeroIsoTerminal.symm

/-- Variant of `preservesZeroMorphisms_of_preserves_terminal_object` where we do not
assume `D` has a zero object. -/
instance preservesZeroMorphisms_of_preserves_terminal_object'
    {C D : Type _} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)
    [HasTerminal C] [PreservesLimit (Functor.empty.{0} C) F] : F.PreservesZeroMorphisms := ⟨by
  have : F.map (𝟙 (⊤_ C)) = 0 := (IsTerminal.isTerminalObj _ _ terminalIsTerminal).hom_ext _ _
  intro X Y
  have eq : (0 : X ⟶ Y) = 0 ≫ 𝟙 (⊤_ C) ≫ 0 := by simp
  rw [eq, F.map_comp, F.map_comp, this, zero_comp, comp_zero]⟩

variable (F)

/-- Preserving zero morphisms implies preserving terminal objects. -/
lemma preservesTerminalObject_of_preservesZeroMorphisms [PreservesZeroMorphisms F] :
    PreservesLimit (Functor.empty.{0} C) F :=
  preservesTerminal_of_iso F <|
    F.mapIso HasZeroObject.zeroIsoTerminal.symm ≪≫ mapZeroObject F ≪≫ HasZeroObject.zeroIsoTerminal

/-- Preserving zero morphisms implies preserving terminal objects. -/
lemma preservesInitialObject_of_preservesZeroMorphisms [PreservesZeroMorphisms F] :
    PreservesColimit (Functor.empty.{0} C) F :=
  preservesInitial_of_iso F <|
    HasZeroObject.zeroIsoInitial.symm ≪≫
      (mapZeroObject F).symm ≪≫ (F.mapIso HasZeroObject.zeroIsoInitial.symm).symm

end ZeroObject

section

variable [HasZeroObject D] [HasZeroMorphisms D]
  (G : C ⥤ D) (hG : IsZero G) (J : Type*) [Category J]

include hG

/-- A zero functor preserves limits. -/
lemma preservesLimitsOfShape_of_isZero : PreservesLimitsOfShape J G where
  preservesLimit {K} := ⟨fun _ => ⟨by
    rw [Functor.isZero_iff] at hG
    exact IsLimit.ofIsZero _ ((K ⋙ G).isZero (fun X ↦ hG _)) (hG _)⟩⟩

/-- A zero functor preserves colimits. -/
lemma preservesColimitsOfShape_of_isZero : PreservesColimitsOfShape J G where
  preservesColimit {K} := ⟨fun _ => ⟨by
    rw [Functor.isZero_iff] at hG
    exact IsColimit.ofIsZero _ ((K ⋙ G).isZero (fun X ↦ hG _)) (hG _)⟩⟩

/-- A zero functor preserves limits. -/
lemma preservesLimitsOfSize_of_isZero : PreservesLimitsOfSize.{v, u} G where
  preservesLimitsOfShape := G.preservesLimitsOfShape_of_isZero hG _

/-- A zero functor preserves colimits. -/
lemma preservesColimitsOfSize_of_isZero : PreservesColimitsOfSize.{v, u} G where
  preservesColimitsOfShape := G.preservesColimitsOfShape_of_isZero hG _

end

end CategoryTheory.Functor
