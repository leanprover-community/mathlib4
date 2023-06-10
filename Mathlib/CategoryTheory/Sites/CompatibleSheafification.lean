/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module category_theory.sites.compatible_sheafification
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Sites.CompatiblePlus
import Mathbin.CategoryTheory.Sites.Sheafification

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

noncomputable section

variable [∀ (α β : Type max v u) (fst snd : β → α), HasLimitsOfShape (WalkingMulticospan fst snd) D]

variable [∀ (α β : Type max v u) (fst snd : β → α), HasLimitsOfShape (WalkingMulticospan fst snd) E]

variable [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ D]

variable [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ E]

variable [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ F]

variable [∀ (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]

variable (P : Cᵒᵖ ⥤ D)

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`.

Use the lemmas `whisker_right_to_sheafify_sheafify_comp_iso_hom`,
`to_sheafify_comp_sheafify_comp_iso_inv` and `sheafify_comp_iso_inv_eq_sheafify_lift` to reduce
the components of this isomorphisms to a state that can be handled using the universal property
of sheafification. -/
def sheafifyCompIso : J.sheafify P ⋙ F ≅ J.sheafify (P ⋙ F) :=
  J.plusCompIso _ _ ≪≫ (J.plusFunctor _).mapIso (J.plusCompIso _ _)
#align category_theory.grothendieck_topology.sheafify_comp_iso CategoryTheory.GrothendieckTopology.sheafifyCompIso

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `F`. -/
def sheafificationWhiskerLeftIso (P : Cᵒᵖ ⥤ D)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (whiskeringLeft _ _ E).obj (J.sheafify P) ≅ (whiskeringLeft _ _ _).obj P ⋙ J.sheafification E :=
  by
  refine' J.plus_functor_whisker_left_iso _ ≪≫ _ ≪≫ functor.associator _ _ _
  refine' iso_whisker_right _ _
  refine' J.plus_functor_whisker_left_iso _
#align category_theory.grothendieck_topology.sheafification_whisker_left_iso CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso

@[simp]
theorem sheafificationWhiskerLeftIso_hom_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (sheafificationWhiskerLeftIso J P).Hom.app F = (J.sheafifyCompIso F P).Hom :=
  by
  dsimp [sheafification_whisker_left_iso, sheafify_comp_iso]
  rw [category.comp_id]
#align category_theory.grothendieck_topology.sheafification_whisker_left_iso_hom_app CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso_hom_app

@[simp]
theorem sheafificationWhiskerLeftIso_inv_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (sheafificationWhiskerLeftIso J P).inv.app F = (J.sheafifyCompIso F P).inv :=
  by
  dsimp [sheafification_whisker_left_iso, sheafify_comp_iso]
  erw [category.id_comp]
#align category_theory.grothendieck_topology.sheafification_whisker_left_iso_inv_app CategoryTheory.GrothendieckTopology.sheafificationWhiskerLeftIso_inv_app

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `P`. -/
def sheafificationWhiskerRightIso :
    J.sheafification D ⋙ (whiskeringRight _ _ _).obj F ≅
      (whiskeringRight _ _ _).obj F ⋙ J.sheafification E :=
  by
  refine' functor.associator _ _ _ ≪≫ _
  refine' iso_whisker_left (J.plus_functor D) (J.plus_functor_whisker_right_iso _) ≪≫ _
  refine' _ ≪≫ functor.associator _ _ _
  refine' (functor.associator _ _ _).symm ≪≫ _
  exact iso_whisker_right (J.plus_functor_whisker_right_iso _) (J.plus_functor E)
#align category_theory.grothendieck_topology.sheafification_whisker_right_iso CategoryTheory.GrothendieckTopology.sheafificationWhiskerRightIso

@[simp]
theorem sheafificationWhiskerRightIso_hom_app :
    (J.sheafificationWhiskerRightIso F).Hom.app P = (J.sheafifyCompIso F P).Hom :=
  by
  dsimp [sheafification_whisker_right_iso, sheafify_comp_iso]
  simp only [category.id_comp, category.comp_id]
  erw [category.id_comp]
#align category_theory.grothendieck_topology.sheafification_whisker_right_iso_hom_app CategoryTheory.GrothendieckTopology.sheafificationWhiskerRightIso_hom_app

@[simp]
theorem sheafificationWhiskerRightIso_inv_app :
    (J.sheafificationWhiskerRightIso F).inv.app P = (J.sheafifyCompIso F P).inv :=
  by
  dsimp [sheafification_whisker_right_iso, sheafify_comp_iso]
  simp only [category.id_comp, category.comp_id]
  erw [category.id_comp]
#align category_theory.grothendieck_topology.sheafification_whisker_right_iso_inv_app CategoryTheory.GrothendieckTopology.sheafificationWhiskerRightIso_inv_app

@[simp, reassoc]
theorem whiskerRight_toSheafify_sheafifyCompIso_hom :
    whiskerRight (J.toSheafify _) _ ≫ (J.sheafifyCompIso F P).Hom = J.toSheafify _ :=
  by
  dsimp [sheafify_comp_iso]
  erw [whisker_right_comp, category.assoc]
  slice_lhs 2 3 => rw [plus_comp_iso_whisker_right]
  rw [category.assoc, ← J.plus_map_comp, whisker_right_to_plus_comp_plus_comp_iso_hom, ←
    category.assoc, whisker_right_to_plus_comp_plus_comp_iso_hom]
  rfl
#align category_theory.grothendieck_topology.whisker_right_to_sheafify_sheafify_comp_iso_hom CategoryTheory.GrothendieckTopology.whiskerRight_toSheafify_sheafifyCompIso_hom

@[simp, reassoc]
theorem toSheafify_comp_sheafifyCompIso_inv :
    J.toSheafify _ ≫ (J.sheafifyCompIso F P).inv = whiskerRight (J.toSheafify _) _ := by
  rw [iso.comp_inv_eq]; simp
#align category_theory.grothendieck_topology.to_sheafify_comp_sheafify_comp_iso_inv CategoryTheory.GrothendieckTopology.toSheafify_comp_sheafifyCompIso_inv

section

-- We will sheafify `D`-valued presheaves in this section.
variable [ConcreteCategory.{max v u} D] [PreservesLimits (forget D)]
  [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget D)] [ReflectsIsomorphisms (forget D)]

@[simp]
theorem sheafifyCompIso_inv_eq_sheafifyLift :
    (J.sheafifyCompIso F P).inv =
      J.sheafifyLift (whiskerRight (J.toSheafify _) _) ((J.sheafify_isSheaf _).comp _) :=
  by
  apply J.sheafify_lift_unique
  rw [iso.comp_inv_eq]
  simp
#align category_theory.grothendieck_topology.sheafify_comp_iso_inv_eq_sheafify_lift CategoryTheory.GrothendieckTopology.sheafifyCompIso_inv_eq_sheafifyLift

end

end CategoryTheory.GrothendieckTopology

