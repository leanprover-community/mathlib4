/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

#align_import category_theory.limits.preserves.shapes.zero from "leanprover-community/mathlib"@"bbe25d4d92565a5fd773e52e041a90387eee3c93"

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


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type _} [Category E]

section ZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

/-- A functor preserves zero morphisms if it sends zero morphisms to zero morphisms. -/
class PreservesZeroMorphisms (F : C ⥤ D) : Prop where
  /-- For any pair objects `F (0: X ⟶ Y) = (0 : F X ⟶ F Y)` -/
  map_zero : ∀ X Y : C, F.map (0 : X ⟶ Y) = 0 := by aesop
#align category_theory.functor.preserves_zero_morphisms CategoryTheory.Functor.PreservesZeroMorphisms

@[simp]
protected theorem map_zero (F : C ⥤ D) [PreservesZeroMorphisms F] (X Y : C) :
    F.map (0 : X ⟶ Y) = 0 :=
  PreservesZeroMorphisms.map_zero _ _
#align category_theory.functor.map_zero CategoryTheory.Functor.map_zero

theorem zero_of_map_zero (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y : C} (f : X ⟶ Y)
    (h : F.map f = 0) : f = 0 :=
  F.map_injective <| h.trans <| Eq.symm <| F.map_zero _ _
#align category_theory.functor.zero_of_map_zero CategoryTheory.Functor.zero_of_map_zero

theorem map_eq_zero_iff (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y : C} {f : X ⟶ Y} :
    F.map f = 0 ↔ f = 0 :=
  ⟨F.zero_of_map_zero _, by
    rintro rfl
    exact F.map_zero _ _⟩
#align category_theory.functor.map_eq_zero_iff CategoryTheory.Functor.map_eq_zero_iff

instance (priority := 100) preservesZeroMorphisms_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] :
    PreservesZeroMorphisms F where
  map_zero X Y := by
    let adj := Adjunction.ofLeftAdjoint F
    dsimp
    calc
      F.map (0 : X ⟶ Y) = F.map 0 ≫ F.map (adj.unit.app Y) ≫ adj.counit.app (F.obj Y) := ?_
      _ = F.map 0 ≫ F.map ((rightAdjoint F).map (0 : F.obj X ⟶ _)) ≫ adj.counit.app (F.obj Y) := ?_
      _ = 0 := ?_
    · rw [Adjunction.left_triangle_components]
      exact (Category.comp_id _).symm
    · simp only [← Category.assoc, ← F.map_comp, zero_comp]
    · simp only [Adjunction.counit_naturality, comp_zero]
#align category_theory.functor.preserves_zero_morphisms_of_is_left_adjoint CategoryTheory.Functor.preservesZeroMorphisms_of_isLeftAdjoint

instance (priority := 100) preservesZeroMorphisms_of_isRightAdjoint (G : C ⥤ D) [IsRightAdjoint G] :
    PreservesZeroMorphisms G where
  map_zero X Y := by
    let adj := Adjunction.ofRightAdjoint G
    calc
      G.map (0 : X ⟶ Y) = adj.unit.app (G.obj X) ≫ G.map (adj.counit.app X) ≫ G.map 0 := ?_
      _ = adj.unit.app (G.obj X) ≫ G.map ((leftAdjoint G).map (0 : _ ⟶ G.obj X)) ≫ G.map 0 := ?_
      _ = 0 := ?_
    · rw [Adjunction.right_triangle_components_assoc]
    · simp only [← G.map_comp, comp_zero]
    · simp only [id_obj, comp_obj, Adjunction.unit_naturality_assoc, zero_comp]
#align category_theory.functor.preserves_zero_morphisms_of_is_right_adjoint CategoryTheory.Functor.preservesZeroMorphisms_of_isRightAdjoint

instance (priority := 100) preservesZeroMorphisms_of_full (F : C ⥤ D) [Full F] :
    PreservesZeroMorphisms F where
  map_zero X Y :=
    calc
      F.map (0 : X ⟶ Y) = F.map (0 ≫ F.preimage (0 : F.obj Y ⟶ F.obj Y)) := by rw [zero_comp]
      _ = 0 := by rw [F.map_comp, F.image_preimage, comp_zero]
#align category_theory.functor.preserves_zero_morphisms_of_full CategoryTheory.Functor.preservesZeroMorphisms_of_full

instance (F : C ⥤ D) (G : D ⥤ E) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] :
    (F ⋙ G).PreservesZeroMorphisms := ⟨by simp⟩

lemma preservesZeroMorphisms_of_iso {F₁ F₂ : C ⥤ D} [F₁.PreservesZeroMorphisms] (e : F₁ ≅ F₂) :
    F₂.PreservesZeroMorphisms := ⟨fun X Y => by
  simp only [← cancel_epi (e.hom.app X), ← e.hom.naturality, F₁.map_zero, zero_comp, comp_zero]⟩

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
#align category_theory.functor.map_zero_object CategoryTheory.Functor.mapZeroObject

variable {F}

theorem preservesZeroMorphisms_of_map_zero_object (i : F.obj 0 ≅ 0) : PreservesZeroMorphisms F where
  map_zero X Y :=
    calc
      F.map (0 : X ⟶ Y) = F.map (0 : X ⟶ 0) ≫ F.map 0 := by rw [← Functor.map_comp, comp_zero]
      _ = F.map 0 ≫ (i.hom ≫ i.inv) ≫ F.map 0 := by rw [Iso.hom_inv_id, Category.id_comp]
      _ = 0 := by simp only [zero_of_to_zero i.hom, zero_comp, comp_zero]
#align category_theory.functor.preserves_zero_morphisms_of_map_zero_object CategoryTheory.Functor.preservesZeroMorphisms_of_map_zero_object

instance (priority := 100) preservesZeroMorphisms_of_preserves_initial_object
    [PreservesColimit (Functor.empty.{0} C) F] : PreservesZeroMorphisms F :=
  preservesZeroMorphisms_of_map_zero_object <|
    F.mapIso HasZeroObject.zeroIsoInitial ≪≫
      PreservesInitial.iso F ≪≫ HasZeroObject.zeroIsoInitial.symm
#align category_theory.functor.preserves_zero_morphisms_of_preserves_initial_object CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_initial_object

instance (priority := 100) preservesZeroMorphisms_of_preserves_terminal_object
    [PreservesLimit (Functor.empty.{0} C) F] : PreservesZeroMorphisms F :=
  preservesZeroMorphisms_of_map_zero_object <|
    F.mapIso HasZeroObject.zeroIsoTerminal ≪≫
      PreservesTerminal.iso F ≪≫ HasZeroObject.zeroIsoTerminal.symm
#align category_theory.functor.preserves_zero_morphisms_of_preserves_terminal_object CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_object

instance preservesZeroMorphisms_of_preserves_terminal_object'
    {C D : Type _} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)
    [HasTerminal C] [PreservesLimit (Functor.empty.{0} C) F] : F.PreservesZeroMorphisms := ⟨by
  have : F.map (𝟙 (⊤_ C)) = 0 := (IsTerminal.isTerminalObj _ _ terminalIsTerminal).hom_ext _ _
  intro X Y
  have eq : (0 : X ⟶ Y) = 0 ≫ 𝟙 (⊤_ C) ≫ 0 := by simp
  rw [eq, F.map_comp, F.map_comp, this, zero_comp, comp_zero]⟩

variable (F)

/-- Preserving zero morphisms implies preserving terminal objects. -/
def preservesTerminalObjectOfPreservesZeroMorphisms [PreservesZeroMorphisms F] :
    PreservesLimit (Functor.empty C) F :=
  preservesTerminalOfIso F <|
    F.mapIso HasZeroObject.zeroIsoTerminal.symm ≪≫ mapZeroObject F ≪≫ HasZeroObject.zeroIsoTerminal
#align category_theory.functor.preserves_terminal_object_of_preserves_zero_morphisms CategoryTheory.Functor.preservesTerminalObjectOfPreservesZeroMorphisms

/-- Preserving zero morphisms implies preserving terminal objects. -/
def preservesInitialObjectOfPreservesZeroMorphisms [PreservesZeroMorphisms F] :
    PreservesColimit (Functor.empty C) F :=
  preservesInitialOfIso F <|
    HasZeroObject.zeroIsoInitial.symm ≪≫
      (mapZeroObject F).symm ≪≫ (F.mapIso HasZeroObject.zeroIsoInitial.symm).symm
#align category_theory.functor.preserves_initial_object_of_preserves_zero_morphisms CategoryTheory.Functor.preservesInitialObjectOfPreservesZeroMorphisms

end ZeroObject

end CategoryTheory.Functor
