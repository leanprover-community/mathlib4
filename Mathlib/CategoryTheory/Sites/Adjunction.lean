/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Sheafification

#align_import category_theory.sites.adjunction from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!

In this file, we show that an adjunction `F ⊣ G` induces an adjunction between
categories of sheaves, under certain hypotheses on `F` and `G`.

-/


namespace CategoryTheory

open GrothendieckTopology CategoryTheory Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type*} [Category D]
variable {E : Type*} [Category E]
variable {F : D ⥤ E} {G : E ⥤ D}
variable [HasWeakSheafify J D] [HasSheafCompose J F]

/-- The forgetful functor from `Sheaf J D` to sheaves of types, for a concrete category `D`
whose forgetful functor preserves the correct limits. -/
abbrev sheafForget [ConcreteCategory D] [HasSheafCompose J (forget D)] :
    Sheaf J D ⥤ SheafOfTypes J :=
  sheafCompose J (forget D) ⋙ (sheafEquivSheafOfTypes J).functor
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf_forget CategoryTheory.sheafForget

namespace Sheaf

noncomputable section

/-- This is the functor sending a sheaf `X : Sheaf J E` to the sheafification
of `X ⋙ G`. -/
abbrev composeAndSheafify (G : E ⥤ D) : Sheaf J E ⥤ Sheaf J D :=
  sheafToPresheaf J E ⋙ (whiskeringRight _ _ _).obj G ⋙ presheafToSheaf J D
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.compose_and_sheafify CategoryTheory.Sheaf.composeAndSheafify

/-- An auxiliary definition to be used in defining `CategoryTheory.Sheaf.adjunction` below. -/
@[simps]
def composeEquiv (adj : G ⊣ F) (X : Sheaf J E) (Y : Sheaf J D) :
    ((composeAndSheafify J G).obj X ⟶ Y) ≃ (X ⟶ (sheafCompose J F).obj Y) :=
  let A := adj.whiskerRight Cᵒᵖ
  { toFun := fun η => ⟨A.homEquiv _ _ (toSheafify J _ ≫ η.val)⟩
    invFun := fun γ => ⟨sheafifyLift J ((A.homEquiv _ _).symm ((sheafToPresheaf _ _).map γ)) Y.2⟩
    left_inv := by
      intro η
      ext1
      dsimp
      symm
      apply sheafifyLift_unique
      rw [Equiv.symm_apply_apply]
    right_inv := by
      intro γ
      ext1
      dsimp
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
      erw [toSheafify_sheafifyLift, Equiv.apply_symm_apply] }
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.compose_equiv CategoryTheory.Sheaf.composeEquiv

-- These lemmas have always been bad (#7657), but leanprover/lean4#2644 made `simp` start noticing
attribute [nolint simpNF] CategoryTheory.Sheaf.composeEquiv_apply_val
  CategoryTheory.Sheaf.composeEquiv_symm_apply_val

/-- An adjunction `adj : G ⊣ F` with `F : D ⥤ E` and `G : E ⥤ D` induces an adjunction
between `Sheaf J D` and `Sheaf J E`, in contexts where one can sheafify `D`-valued presheaves,
and `F` preserves the correct limits. -/
@[simps! unit_app_val counit_app_val]
def adjunction (adj : G ⊣ F) : composeAndSheafify J G ⊣ sheafCompose J F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := composeEquiv J adj
      homEquiv_naturality_left_symm := fun f g => by
        ext1
        dsimp [composeEquiv]
        rw [sheafifyMap_sheafifyLift]
        erw [Adjunction.homEquiv_naturality_left_symm]
        rw [whiskeringRight_obj_map]
        rfl
      homEquiv_naturality_right := fun f g => by
        ext
        dsimp [composeEquiv]
        erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
        dsimp
        simp }
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.adjunction CategoryTheory.Sheaf.adjunction

instance [F.IsRightAdjoint] : (sheafCompose J F).IsRightAdjoint :=
  (adjunction J (Adjunction.ofIsRightAdjoint F)).isRightAdjoint

section ForgetToType

variable [ConcreteCategory D] [HasSheafCompose J (forget D)]

/-- This is the functor sending a sheaf of types `X` to the sheafification of `X ⋙ G`. -/
abbrev composeAndSheafifyFromTypes (G : Type max v u ⥤ D) : SheafOfTypes J ⥤ Sheaf J D :=
  (sheafEquivSheafOfTypes J).inverse ⋙ composeAndSheafify _ G
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.compose_and_sheafify_from_types CategoryTheory.Sheaf.composeAndSheafifyFromTypes

/-- A variant of the adjunction between sheaf categories, in the case where the right adjoint
is the forgetful functor to sheaves of types. -/
def adjunctionToTypes {G : Type max v u ⥤ D} (adj : G ⊣ forget D) :
    composeAndSheafifyFromTypes J G ⊣ sheafForget J :=
  (sheafEquivSheafOfTypes J).symm.toAdjunction.comp (adjunction J adj)
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.adjunction_to_types CategoryTheory.Sheaf.adjunctionToTypes

@[simp]
theorem adjunctionToTypes_unit_app_val {G : Type max v u ⥤ D} (adj : G ⊣ forget D)
    (Y : SheafOfTypes J) :
    ((adjunctionToTypes J adj).unit.app Y).val =
      (adj.whiskerRight _).unit.app ((sheafOfTypesToPresheaf J).obj Y) ≫
        whiskerRight (toSheafify J _) (forget D) := by
  dsimp [adjunctionToTypes, Adjunction.comp]
  simp
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.adjunction_to_types_unit_app_val CategoryTheory.Sheaf.adjunctionToTypes_unit_app_val

@[simp]
theorem adjunctionToTypes_counit_app_val {G : Type max v u ⥤ D} (adj : G ⊣ forget D)
    (X : Sheaf J D) :
    ((adjunctionToTypes J adj).counit.app X).val =
      sheafifyLift J ((Functor.associator _ _ _).hom ≫ (adj.whiskerRight _).counit.app _) X.2 := by
  apply sheafifyLift_unique
  dsimp only [adjunctionToTypes, Adjunction.comp, NatTrans.comp_app,
    instCategorySheaf_comp_val, instCategorySheaf_id_val]
  rw [adjunction_counit_app_val]
  erw [Category.id_comp, sheafifyMap_sheafifyLift, toSheafify_sheafifyLift]
  ext
  dsimp [sheafEquivSheafOfTypes, Equivalence.symm, Equivalence.toAdjunction,
    NatIso.ofComponents, Adjunction.whiskerRight, Adjunction.mkOfUnitCounit]
  simp

set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.adjunction_to_types_counit_app_val CategoryTheory.Sheaf.adjunctionToTypes_counit_app_val

instance [(forget D).IsRightAdjoint ] : (sheafForget J : Sheaf J D ⥤ _).IsRightAdjoint  :=
  (adjunctionToTypes J (Adjunction.ofIsRightAdjoint (forget D))).isRightAdjoint

end ForgetToType

end

end Sheaf

end CategoryTheory
