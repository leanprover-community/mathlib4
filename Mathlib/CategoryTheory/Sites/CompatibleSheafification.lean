/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.CompatiblePlus
import Mathlib.CategoryTheory.Sites.Sheafification

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
noncomputable def sheafifyCompIso : J.sheafify P ⋙ F ≅ J.sheafify (P ⋙ F) :=
  J.plusCompIso _ _ ≪≫ (J.plusFunctor _).mapIso (J.plusCompIso _ _)
#align category_theory.grothendieck_topology.sheafify_comp_iso CategoryTheory.GrothendieckTopology.sheafifyCompIso

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `F`. -/
noncomputable def sheafificationWhiskerLeftIso (P : Cᵒᵖ ⥤ D)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (whiskeringLeft _ _ E).obj (J.sheafify P) ≅
    (whiskeringLeft _ _ _).obj P ⋙ J.sheafification E := by
  refine' J.plusFunctorWhiskerLeftIso _ ≪≫ _ ≪≫ Functor.associator _ _ _
  -- ⊢ (whiskeringLeft Cᵒᵖ D E).obj (plusObj J P) ⋙ plusFunctor J E ≅ ((whiskeringL …
  refine' isoWhiskerRight _ _
  -- ⊢ (whiskeringLeft Cᵒᵖ D E).obj (plusObj J P) ≅ (whiskeringLeft Cᵒᵖ D E).obj P  …
  refine' J.plusFunctorWhiskerLeftIso _
  -- 🎉 no goals
#align category_theory.grothendieck_topology.sheafification_whisker_left_iso CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso

@[simp]
theorem sheafificationWhiskerLeftIso_hom_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (sheafificationWhiskerLeftIso J P).hom.app F = (J.sheafifyCompIso F P).hom := by
  dsimp [sheafificationWhiskerLeftIso, sheafifyCompIso]
  -- ⊢ (plusCompIso J F (plusObj J P)).hom ≫ plusMap J (plusCompIso J F P).hom ≫ 𝟙  …
  rw [Category.comp_id]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.sheafification_whisker_left_iso_hom_app CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso_hom_app

@[simp]
theorem sheafificationWhiskerLeftIso_inv_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (sheafificationWhiskerLeftIso J P).inv.app F = (J.sheafifyCompIso F P).inv := by
  dsimp [sheafificationWhiskerLeftIso, sheafifyCompIso]
  -- ⊢ (𝟙 (plusObj J (plusObj J (P ⋙ F))) ≫ plusMap J (plusCompIso J F P).inv) ≫ (p …
  erw [Category.id_comp]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.sheafification_whisker_left_iso_inv_app CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso_inv_app

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `P`. -/
noncomputable def sheafificationWhiskerRightIso :
    J.sheafification D ⋙ (whiskeringRight _ _ _).obj F ≅
      (whiskeringRight _ _ _).obj F ⋙ J.sheafification E := by
  refine' Functor.associator _ _ _ ≪≫ _
  -- ⊢ plusFunctor J D ⋙ plusFunctor J D ⋙ (whiskeringRight Cᵒᵖ D E).obj F ≅ (whisk …
  refine' isoWhiskerLeft (J.plusFunctor D) (J.plusFunctorWhiskerRightIso _) ≪≫ _
  -- ⊢ plusFunctor J D ⋙ (whiskeringRight Cᵒᵖ D E).obj F ⋙ plusFunctor J E ≅ (whisk …
  refine' _ ≪≫ Functor.associator _ _ _
  -- ⊢ plusFunctor J D ⋙ (whiskeringRight Cᵒᵖ D E).obj F ⋙ plusFunctor J E ≅ ((whis …
  refine' (Functor.associator _ _ _).symm ≪≫ _
  -- ⊢ (plusFunctor J D ⋙ (whiskeringRight Cᵒᵖ D E).obj F) ⋙ plusFunctor J E ≅ ((wh …
  exact isoWhiskerRight (J.plusFunctorWhiskerRightIso _) (J.plusFunctor E)
  -- 🎉 no goals
#align category_theory.grothendieck_topology.sheafification_whisker_right_iso CategoryTheory.GrothendieckTopology.sheafificationWhiskerRightIso

@[simp]
theorem sheafificationWhiskerRightIso_hom_app :
    (J.sheafificationWhiskerRightIso F).hom.app P = (J.sheafifyCompIso F P).hom := by
  dsimp [sheafificationWhiskerRightIso, sheafifyCompIso]
  -- ⊢ 𝟙 (plusObj J (plusObj J P) ⋙ F) ≫ (plusCompIso J F (plusObj J P)).hom ≫ (𝟙 ( …
  simp only [Category.id_comp, Category.comp_id]
  -- ⊢ 𝟙 (plusObj J (plusObj J P) ⋙ F) ≫ (plusCompIso J F (plusObj J P)).hom ≫ plus …
  erw [Category.id_comp]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.sheafification_whisker_right_iso_hom_app CategoryTheory.GrothendieckTopology.sheafificationWhiskerRightIso_hom_app

@[simp]
theorem sheafificationWhiskerRightIso_inv_app :
    (J.sheafificationWhiskerRightIso F).inv.app P = (J.sheafifyCompIso F P).inv := by
  dsimp [sheafificationWhiskerRightIso, sheafifyCompIso]
  -- ⊢ ((𝟙 (plusObj J (plusObj J (P ⋙ F))) ≫ plusMap J (plusCompIso J F P).inv ≫ 𝟙  …
  simp only [Category.id_comp, Category.comp_id]
  -- ⊢ (𝟙 (plusObj J (plusObj J (P ⋙ F))) ≫ plusMap J (plusCompIso J F P).inv) ≫ (p …
  erw [Category.id_comp]
  -- 🎉 no goals
#align category_theory.grothendieck_topology.sheafification_whisker_right_iso_inv_app CategoryTheory.GrothendieckTopology.sheafificationWhiskerRightIso_inv_app

@[simp, reassoc]
theorem whiskerRight_toSheafify_sheafifyCompIso_hom :
    whiskerRight (J.toSheafify _) _ ≫ (J.sheafifyCompIso F P).hom = J.toSheafify _ := by
  dsimp [sheafifyCompIso]
  -- ⊢ whiskerRight (toSheafify J P) F ≫ (plusCompIso J F (plusObj J P)).hom ≫ plus …
  erw [whiskerRight_comp, Category.assoc]
  -- ⊢ whiskerRight (toPlus J P) F ≫ whiskerRight (plusMap J (toPlus J P)) F ≫ (plu …
  slice_lhs 2 3 => rw [plusCompIso_whiskerRight]
  -- ⊢ whiskerRight (toPlus J P) F ≫ ((plusCompIso J F P).hom ≫ plusMap J (whiskerR …
  rw [Category.assoc, ← J.plusMap_comp, whiskerRight_toPlus_comp_plusCompIso_hom, ←
    Category.assoc, whiskerRight_toPlus_comp_plusCompIso_hom]
  rfl
  -- 🎉 no goals
#align category_theory.grothendieck_topology.whisker_right_to_sheafify_sheafify_comp_iso_hom CategoryTheory.GrothendieckTopology.whiskerRight_toSheafify_sheafifyCompIso_hom

@[simp, reassoc]
theorem toSheafify_comp_sheafifyCompIso_inv :
    J.toSheafify _ ≫ (J.sheafifyCompIso F P).inv = whiskerRight (J.toSheafify _) _ := by
  rw [Iso.comp_inv_eq]; simp
  -- ⊢ toSheafify J (P ⋙ F) = whiskerRight (toSheafify J P) F ≫ (sheafifyCompIso J  …
                        -- 🎉 no goals
#align category_theory.grothendieck_topology.to_sheafify_comp_sheafify_comp_iso_inv CategoryTheory.GrothendieckTopology.toSheafify_comp_sheafifyCompIso_inv

section

-- We will sheafify `D`-valued presheaves in this section.
variable [ConcreteCategory.{max v u} D] [PreservesLimits (forget D)]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)] [ReflectsIsomorphisms (forget D)]

@[simp]
theorem sheafifyCompIso_inv_eq_sheafifyLift :
    (J.sheafifyCompIso F P).inv =
      J.sheafifyLift (whiskerRight (J.toSheafify P) F) ((J.sheafify_isSheaf _).comp _) := by
  apply J.sheafifyLift_unique
  -- ⊢ toSheafify J (P ⋙ F) ≫ (sheafifyCompIso J F P).inv = whiskerRight (toSheafif …
  rw [Iso.comp_inv_eq]
  -- ⊢ toSheafify J (P ⋙ F) = whiskerRight (toSheafify J P) F ≫ (sheafifyCompIso J  …
  simp
  -- 🎉 no goals
#align category_theory.grothendieck_topology.sheafify_comp_iso_inv_eq_sheafify_lift CategoryTheory.GrothendieckTopology.sheafifyCompIso_inv_eq_sheafifyLift

end

end CategoryTheory.GrothendieckTopology
