/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module category_theory.sites.adjunction
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.Whiskering
import Mathbin.CategoryTheory.Sites.Sheafification
import Mathbin.CategoryTheory.Sites.Whiskering

/-!

In this file, we show that an adjunction `F ⊣ G` induces an adjunction between
categories of sheaves, under certain hypotheses on `F` and `G`.

-/


namespace CategoryTheory

open CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe w₁ w₂ v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {D : Type w₁} [Category.{max v u} D]

variable {E : Type w₂} [Category.{max v u} E]

variable {F : D ⥤ E} {G : E ⥤ D}

variable [∀ (X : C) (S : J.cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (S.index P).multicospan F]

variable [ConcreteCategory.{max v u} D] [PreservesLimits (forget D)]

/-- The forgetful functor from `Sheaf J D` to sheaves of types, for a concrete category `D`
whose forgetful functor preserves the correct limits. -/
abbrev sheafForget : Sheaf J D ⥤ SheafOfTypes J :=
  sheafCompose J (forget D) ⋙ (sheafEquivSheafOfTypes J).Functor
#align category_theory.Sheaf_forget CategoryTheory.sheafForget

-- We need to sheafify...
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ D]
  [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget D)] [ReflectsIsomorphisms (forget D)]

namespace Sheaf

noncomputable section

/-- This is the functor sending a sheaf `X : Sheaf J E` to the sheafification
of `X ⋙ G`. -/
abbrev composeAndSheafify (G : E ⥤ D) : Sheaf J E ⥤ Sheaf J D :=
  sheafToPresheaf J E ⋙ (whiskeringRight _ _ _).obj G ⋙ presheafToSheaf J D
#align category_theory.Sheaf.compose_and_sheafify CategoryTheory.Sheaf.composeAndSheafify

/-- An auxiliary definition to be used in defining `category_theory.Sheaf.adjunction` below. -/
@[simps]
def composeEquiv (adj : G ⊣ F) (X : Sheaf J E) (Y : Sheaf J D) :
    ((composeAndSheafify J G).obj X ⟶ Y) ≃ (X ⟶ (sheafCompose J F).obj Y) :=
  let A := adj.whiskerRight Cᵒᵖ
  { toFun := fun η => ⟨A.homEquiv _ _ (J.toSheafify _ ≫ η.val)⟩
    invFun := fun γ => ⟨J.sheafifyLift ((A.homEquiv _ _).symm ((sheafToPresheaf _ _).map γ)) Y.2⟩
    left_inv := by
      intro η
      ext1
      dsimp
      symm
      apply J.sheafify_lift_unique
      rw [Equiv.symm_apply_apply]
    right_inv := by
      intro γ
      ext1
      dsimp
      rw [J.to_sheafify_sheafify_lift, Equiv.apply_symm_apply] }
#align category_theory.Sheaf.compose_equiv CategoryTheory.Sheaf.composeEquiv

/-- An adjunction `adj : G ⊣ F` with `F : D ⥤ E` and `G : E ⥤ D` induces an adjunction
between `Sheaf J D` and `Sheaf J E`, in contexts where one can sheafify `D`-valued presheaves,
and `F` preserves the correct limits. -/
@[simps unit_app_val counit_app_val]
def adjunction (adj : G ⊣ F) : composeAndSheafify J G ⊣ sheafCompose J F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := composeEquiv J adj
      homEquiv_naturality_left_symm := fun X' X Y f g =>
        by
        ext1
        dsimp
        simp
      homEquiv_naturality_right := fun X Y Y' f g =>
        by
        ext1
        dsimp
        simp }
#align category_theory.Sheaf.adjunction CategoryTheory.Sheaf.adjunction

instance [IsRightAdjoint F] : IsRightAdjoint (sheafCompose J F) :=
  ⟨_, adjunction J (Adjunction.ofRightAdjoint F)⟩

section ForgetToType

/-- This is the functor sending a sheaf of types `X` to the sheafification of `X ⋙ G`. -/
abbrev composeAndSheafifyFromTypes (G : Type max v u ⥤ D) : SheafOfTypes J ⥤ Sheaf J D :=
  (sheafEquivSheafOfTypes J).inverse ⋙ composeAndSheafify _ G
#align category_theory.Sheaf.compose_and_sheafify_from_types CategoryTheory.Sheaf.composeAndSheafifyFromTypes

/-- A variant of the adjunction between sheaf categories, in the case where the right adjoint
is the forgetful functor to sheaves of types. -/
def adjunctionToTypes {G : Type max v u ⥤ D} (adj : G ⊣ forget D) :
    composeAndSheafifyFromTypes J G ⊣ sheafForget J :=
  (sheafEquivSheafOfTypes J).symm.toAdjunction.comp (adjunction J adj)
#align category_theory.Sheaf.adjunction_to_types CategoryTheory.Sheaf.adjunctionToTypes

@[simp]
theorem adjunctionToTypes_unit_app_val {G : Type max v u ⥤ D} (adj : G ⊣ forget D)
    (Y : SheafOfTypes J) :
    ((adjunctionToTypes J adj).Unit.app Y).val =
      (adj.whiskerRight _).Unit.app ((sheafOfTypesToPresheaf J).obj Y) ≫
        whiskerRight (J.toSheafify _) (forget D) :=
  by
  dsimp [adjunction_to_types, adjunction.comp]
  simpa
#align category_theory.Sheaf.adjunction_to_types_unit_app_val CategoryTheory.Sheaf.adjunctionToTypes_unit_app_val

@[simp]
theorem adjunctionToTypes_counit_app_val {G : Type max v u ⥤ D} (adj : G ⊣ forget D)
    (X : Sheaf J D) :
    ((adjunctionToTypes J adj).counit.app X).val =
      J.sheafifyLift ((Functor.associator _ _ _).Hom ≫ (adj.whiskerRight _).counit.app _) X.2 :=
  by
  dsimp [adjunction_to_types, adjunction.comp, adjunction.whisker_right]
  rw [category.id_comp]
  apply J.sheafify_lift_unique
  rw [adjunction_counit_app_val, J.sheafify_map_sheafify_lift, J.to_sheafify_sheafify_lift]
  ext
  dsimp [Sheaf_equiv_SheafOfTypes, equivalence.symm, equivalence.to_adjunction,
    nat_iso.of_components]
  simp
#align category_theory.Sheaf.adjunction_to_types_counit_app_val CategoryTheory.Sheaf.adjunctionToTypes_counit_app_val

instance [IsRightAdjoint (forget D)] : IsRightAdjoint (sheafForget J) :=
  ⟨_, adjunctionToTypes J (Adjunction.ofRightAdjoint (forget D))⟩

end ForgetToType

end Sheaf

end CategoryTheory

