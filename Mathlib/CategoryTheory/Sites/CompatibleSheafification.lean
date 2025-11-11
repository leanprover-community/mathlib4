/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.CompatiblePlus
import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-!

In this file, we prove that sheafification is compatible with functors which
preserve the correct limits and colimits.

-/


namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor

open Opposite

universe w₁ w₂ v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type w₁} [Category.{max v u} D]
variable {E : Type w₂} [Category.{max v u} E]
variable (F : D ⥤ E)

variable [∀ (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) D]
variable [∀ (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) E]
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

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `F`. -/
noncomputable def sheafificationWhiskerLeftIso (P : Cᵒᵖ ⥤ D)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (whiskeringLeft _ _ E).obj (J.sheafify P) ≅
    (whiskeringLeft _ _ _).obj P ⋙ J.sheafification E := by
  refine J.plusFunctorWhiskerLeftIso _ ≪≫ ?_ ≪≫ associator _ _ _
  refine isoWhiskerRight ?_ _
  exact J.plusFunctorWhiskerLeftIso _

@[simp]
theorem sheafificationWhiskerLeftIso_hom_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (sheafificationWhiskerLeftIso J P).hom.app F = (J.sheafifyCompIso F P).hom := by
  dsimp [sheafificationWhiskerLeftIso, sheafifyCompIso]
  rw [Category.comp_id]

@[simp]
theorem sheafificationWhiskerLeftIso_inv_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (sheafificationWhiskerLeftIso J P).inv.app F = (J.sheafifyCompIso F P).inv := by
  dsimp [sheafificationWhiskerLeftIso, sheafifyCompIso]
  erw [Category.id_comp]

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `P`. -/
noncomputable def sheafificationWhiskerRightIso :
    J.sheafification D ⋙ (whiskeringRight _ _ _).obj F ≅
      (whiskeringRight _ _ _).obj F ⋙ J.sheafification E := by
  refine associator _ _ _ ≪≫ ?_
  refine isoWhiskerLeft (J.plusFunctor D) (J.plusFunctorWhiskerRightIso _) ≪≫ ?_
  refine ?_ ≪≫ associator _ _ _
  refine (associator _ _ _).symm ≪≫ ?_
  exact isoWhiskerRight (J.plusFunctorWhiskerRightIso _) (J.plusFunctor E)

@[simp]
theorem sheafificationWhiskerRightIso_hom_app :
    (J.sheafificationWhiskerRightIso F).hom.app P = (J.sheafifyCompIso F P).hom := by
  dsimp [sheafificationWhiskerRightIso, sheafifyCompIso]
  simp only [Category.id_comp, Category.comp_id]
  erw [Category.id_comp]

@[simp]
theorem sheafificationWhiskerRightIso_inv_app :
    (J.sheafificationWhiskerRightIso F).inv.app P = (J.sheafifyCompIso F P).inv := by
  dsimp [sheafificationWhiskerRightIso, sheafifyCompIso]
  simp only [Category.comp_id]
  erw [Category.id_comp]

@[simp, reassoc]
theorem whiskerRight_toSheafify_sheafifyCompIso_hom :
    whiskerRight (J.toSheafify _) _ ≫ (J.sheafifyCompIso F P).hom = J.toSheafify _ := by
  dsimp [sheafifyCompIso]
  erw [whiskerRight_comp, Category.assoc]
  slice_lhs 2 3 => rw [plusCompIso_whiskerRight]
  rw [Category.assoc, ← J.plusMap_comp, whiskerRight_toPlus_comp_plusCompIso_hom, ←
    Category.assoc, whiskerRight_toPlus_comp_plusCompIso_hom]
  rfl

@[simp, reassoc]
theorem toSheafify_comp_sheafifyCompIso_inv :
    J.toSheafify _ ≫ (J.sheafifyCompIso F P).inv = whiskerRight (J.toSheafify _) _ := by
  rw [Iso.comp_inv_eq]; simp

section

-- We will sheafify `D`-valued presheaves in this section.
variable {FD : D → D → Type*} {CD : D → Type (max v u)} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
variable [ConcreteCategory.{max v u} D FD] [PreservesLimits (forget D)]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)] [(forget D).ReflectsIsomorphisms]

@[simp]
theorem sheafifyCompIso_inv_eq_sheafifyLift :
    (J.sheafifyCompIso F P).inv =
      J.sheafifyLift (whiskerRight (J.toSheafify P) F)
        (HasSheafCompose.isSheaf _ ((J.sheafify_isSheaf _))) := by
  apply J.sheafifyLift_unique
  rw [Iso.comp_inv_eq]
  simp

end

end CategoryTheory.GrothendieckTopology
