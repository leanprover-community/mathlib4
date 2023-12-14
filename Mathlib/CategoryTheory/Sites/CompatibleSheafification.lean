/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.CompatiblePlus
import Mathlib.CategoryTheory.Sites.LeftExact

#align_import category_theory.sites.compatible_sheafification from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!

In this file, we prove that sheafification is compatible with functors which
preserve the correct limits and colimits.

-/


namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe w₁ w₂ v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {D : Type w₁} [Category.{max v u} D]

variable {E : Type w₂} [Category.{max v u} E]

variable (F : D ⥤ E)

-- porting note: Removed this and made whatever necessary noncomputable
-- noncomputable section

variable [∀ (α β : Type max v u) (fst snd : β → α), HasLimitsOfShape (WalkingMulticospan fst snd) D]

variable [∀ (α β : Type max v u) (fst snd : β → α), HasLimitsOfShape (WalkingMulticospan fst snd) E]

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ E]

variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]

variable [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]

variable (P : Cᵒᵖ ⥤ D)

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`.

Use the lemmas `whisker_right_to_sheafify_sheafify_comp_iso_hom`,
`to_sheafify_comp_sheafify_comp_iso_inv` and `sheafify_comp_iso_inv_eq_sheafify_lift` to reduce
the components of this isomorphisms to a state that can be handled using the universal property
of sheafification. -/
noncomputable def sheafifyCompIso : J.plusPlus P ⋙ F ≅ J.plusPlus (P ⋙ F) :=
  J.plusCompIso _ _ ≪≫ (J.plusFunctor _).mapIso (J.plusCompIso _ _)
#align category_theory.grothendieck_topology.sheafify_comp_iso CategoryTheory.GrothendieckTopology.sheafifyCompIso

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `F`. -/
noncomputable def sheafificationWhiskerLeftIso (P : Cᵒᵖ ⥤ D)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (whiskeringLeft _ _ E).obj (J.plusPlus P) ≅
    (whiskeringLeft _ _ _).obj P ⋙ J.plusPlusFunctor E := by
  refine' J.plusFunctorWhiskerLeftIso _ ≪≫ _ ≪≫ Functor.associator _ _ _
  refine' isoWhiskerRight _ _
  refine' J.plusFunctorWhiskerLeftIso _
#align category_theory.grothendieck_topology.sheafification_whisker_left_iso CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso

@[simp]
theorem sheafificationWhiskerLeftIso_hom_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (sheafificationWhiskerLeftIso J P).hom.app F = (J.sheafifyCompIso F P).hom := by
  dsimp [sheafificationWhiskerLeftIso, sheafifyCompIso]
  rw [Category.comp_id]
#align category_theory.grothendieck_topology.sheafification_whisker_left_iso_hom_app CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso_hom_app

@[simp]
theorem sheafificationWhiskerLeftIso_inv_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (sheafificationWhiskerLeftIso J P).inv.app F = (J.sheafifyCompIso F P).inv := by
  dsimp [sheafificationWhiskerLeftIso, sheafifyCompIso]
  erw [Category.id_comp]
#align category_theory.grothendieck_topology.sheafification_whisker_left_iso_inv_app CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso_inv_app

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `P`. -/
noncomputable def sheafificationWhiskerRightIso :
    J.plusPlusFunctor D ⋙ (whiskeringRight _ _ _).obj F ≅
      (whiskeringRight _ _ _).obj F ⋙ J.plusPlusFunctor E := by
  refine' Functor.associator _ _ _ ≪≫ _
  refine' isoWhiskerLeft (J.plusFunctor D) (J.plusFunctorWhiskerRightIso _) ≪≫ _
  refine' _ ≪≫ Functor.associator _ _ _
  refine' (Functor.associator _ _ _).symm ≪≫ _
  exact isoWhiskerRight (J.plusFunctorWhiskerRightIso _) (J.plusFunctor E)
#align category_theory.grothendieck_topology.sheafification_whisker_right_iso CategoryTheory.GrothendieckTopology.sheafificationWhiskerRightIso

@[simp]
theorem sheafificationWhiskerRightIso_hom_app :
    (J.sheafificationWhiskerRightIso F).hom.app P = (J.sheafifyCompIso F P).hom := by
  dsimp [sheafificationWhiskerRightIso, sheafifyCompIso]
  simp only [Category.id_comp, Category.comp_id]
  erw [Category.id_comp]
#align category_theory.grothendieck_topology.sheafification_whisker_right_iso_hom_app CategoryTheory.GrothendieckTopology.sheafificationWhiskerRightIso_hom_app

@[simp]
theorem sheafificationWhiskerRightIso_inv_app :
    (J.sheafificationWhiskerRightIso F).inv.app P = (J.sheafifyCompIso F P).inv := by
  dsimp [sheafificationWhiskerRightIso, sheafifyCompIso]
  simp only [Category.id_comp, Category.comp_id]
  erw [Category.id_comp]
#align category_theory.grothendieck_topology.sheafification_whisker_right_iso_inv_app CategoryTheory.GrothendieckTopology.sheafificationWhiskerRightIso_inv_app

@[simp, reassoc]
theorem whiskerRight_toSheafify_sheafifyCompIso_hom :
    whiskerRight (J.toPlusPlus _) _ ≫ (J.sheafifyCompIso F P).hom = J.toPlusPlus _ := by
  dsimp [sheafifyCompIso]
  erw [whiskerRight_comp, Category.assoc]
  slice_lhs 2 3 => rw [plusCompIso_whiskerRight]
  rw [Category.assoc, ← J.plusMap_comp, whiskerRight_toPlus_comp_plusCompIso_hom, ←
    Category.assoc, whiskerRight_toPlus_comp_plusCompIso_hom]
  rfl
#align category_theory.grothendieck_topology.whisker_right_to_sheafify_sheafify_comp_iso_hom CategoryTheory.GrothendieckTopology.whiskerRight_toSheafify_sheafifyCompIso_hom

@[simp, reassoc]
theorem toSheafify_comp_sheafifyCompIso_inv :
    J.toPlusPlus _ ≫ (J.sheafifyCompIso F P).inv = whiskerRight (J.toPlusPlus _) _ := by
  rw [Iso.comp_inv_eq]; simp
#align category_theory.grothendieck_topology.to_sheafify_comp_sheafify_comp_iso_inv CategoryTheory.GrothendieckTopology.toSheafify_comp_sheafifyCompIso_inv

section

-- We will sheafify `D`-valued presheaves in this section.
variable [ConcreteCategory.{max v u} D] [PreservesLimits (forget D)]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)] [ReflectsIsomorphisms (forget D)]

@[simp]
theorem sheafifyCompIso_inv_eq_sheafifyLift :
    (J.sheafifyCompIso F P).inv =
      J.plusPlusLift (whiskerRight (J.toPlusPlus P) F)
        (HasSheafCompose.isSheaf _ ((J.plusPlus_isSheaf _))) := by
  apply J.plusPlusLift_unique
  rw [Iso.comp_inv_eq]
  simp
#align category_theory.grothendieck_topology.sheafify_comp_iso_inv_eq_sheafify_lift CategoryTheory.GrothendieckTopology.sheafifyCompIso_inv_eq_sheafifyLift

-- We will sheafify `E`-valued presheaves in this section.
variable [ConcreteCategory.{max v u} E] [PreservesLimits (forget E)]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget E)] [ReflectsIsomorphisms (forget E)]

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`. -/
@[simps!]
noncomputable def sheafifyCompIso' : J.sheafify P ⋙ F ≅ J.sheafify (P ⋙ F) :=
  isoWhiskerRight (plusPlusIsoSheafify _ _ _).symm F ≪≫ J.sheafifyCompIso _ _ ≪≫
    plusPlusIsoSheafify _ _ _

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `F`. -/
@[simps!]
noncomputable def sheafificationWhiskerLeftIso' (P : Cᵒᵖ ⥤ D)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (whiskeringLeft _ _ E).obj (J.sheafify P) ≅
    (whiskeringLeft _ _ _).obj P ⋙ J.sheafification E :=
  (whiskeringLeft Cᵒᵖ D E).mapIso (plusPlusIsoSheafify J D P).symm ≪≫
    J.sheafificationWhiskerLeftIso P ≪≫ isoWhiskerLeft _ (plusPlusFunctorIsoSheafification J E)

end

end CategoryTheory.GrothendieckTopology
