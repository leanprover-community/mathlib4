/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Whiskering

#align_import category_theory.sites.adjunction from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!

In this file, we show that an adjunction `F ⊣ G` induces an adjunction between
categories of sheaves, under certain hypotheses on `F` and `G`.

-/


namespace CategoryTheory

open GrothendieckTopology CategoryTheory Limits Opposite

universe w₁ w₂ v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {D : Type w₁} [Category.{max v u} D]

variable {E : Type w₂} [Category.{max v u} E]

variable {F : D ⥤ E} {G : E ⥤ D}

variable [∀ (X : C) (S : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (S.index P).multicospan F]

variable [ConcreteCategory.{max v u} D] [PreservesLimits (forget D)]

/-- The forgetful functor from `Sheaf J D` to sheaves of types, for a concrete category `D`
whose forgetful functor preserves the correct limits. -/
abbrev sheafForget : Sheaf J D ⥤ SheafOfTypes J :=
  sheafCompose J (forget D) ⋙ (sheafEquivSheafOfTypes J).functor
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf_forget CategoryTheory.sheafForget

-- We need to sheafify...
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)] [ReflectsIsomorphisms (forget D)]

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
  { toFun := fun η => ⟨A.homEquiv _ _ (J.toSheafify _ ≫ η.val)⟩
    invFun := fun γ => ⟨J.sheafifyLift ((A.homEquiv _ _).symm ((sheafToPresheaf _ _).map γ)) Y.2⟩
    left_inv := by
      intro η
      -- ⊢ (fun γ => { val := sheafifyLift J (↑(Adjunction.homEquiv A ((sheafToPresheaf …
      ext1
      -- ⊢ ((fun γ => { val := sheafifyLift J (↑(Adjunction.homEquiv A ((sheafToPreshea …
      dsimp
      -- ⊢ sheafifyLift J (↑(Adjunction.homEquiv (Adjunction.whiskerRight Cᵒᵖ adj) X.va …
      symm
      -- ⊢ η.val = sheafifyLift J (↑(Adjunction.homEquiv (Adjunction.whiskerRight Cᵒᵖ a …
      apply J.sheafifyLift_unique
      -- ⊢ toSheafify J (X.val ⋙ G) ≫ η.val = ↑(Adjunction.homEquiv (Adjunction.whisker …
      rw [Equiv.symm_apply_apply]
      -- 🎉 no goals
    right_inv := by
      intro γ
      -- ⊢ (fun η => { val := ↑(Adjunction.homEquiv A ((sheafToPresheaf J E).obj X) Y.v …
      ext1
      -- ⊢ ((fun η => { val := ↑(Adjunction.homEquiv A ((sheafToPresheaf J E).obj X) Y. …
      dsimp
      -- ⊢ ↑(Adjunction.homEquiv (Adjunction.whiskerRight Cᵒᵖ adj) X.val Y.val) (toShea …
      rw [J.toSheafify_sheafifyLift, Equiv.apply_symm_apply] }
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.compose_equiv CategoryTheory.Sheaf.composeEquiv

/-- An adjunction `adj : G ⊣ F` with `F : D ⥤ E` and `G : E ⥤ D` induces an adjunction
between `Sheaf J D` and `Sheaf J E`, in contexts where one can sheafify `D`-valued presheaves,
and `F` preserves the correct limits. -/
@[simps! unit_app_val counit_app_val]
def adjunction (adj : G ⊣ F) : composeAndSheafify J G ⊣ sheafCompose J F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := composeEquiv J adj
      homEquiv_naturality_left_symm := fun f g => by
        ext1
        -- ⊢ (↑(composeEquiv J adj X'✝ Y✝).symm (f ≫ g)).val = ((composeAndSheafify J G). …
        dsimp [composeEquiv]
        -- ⊢ sheafifyLift J (↑(Adjunction.homEquiv (Adjunction.whiskerRight Cᵒᵖ adj) X'✝. …
        rw [sheafifyMap_sheafifyLift]
        -- ⊢ sheafifyLift J (↑(Adjunction.homEquiv (Adjunction.whiskerRight Cᵒᵖ adj) X'✝. …
        erw [Adjunction.homEquiv_naturality_left_symm]
        -- ⊢ sheafifyLift J (((whiskeringRight Cᵒᵖ E D).obj G).map f.val ≫ ↑(Adjunction.h …
        rw [whiskeringRight_obj_map]
        -- ⊢ sheafifyLift J (whiskerRight f.val G ≫ ↑(Adjunction.homEquiv (Adjunction.whi …
        rfl
        -- 🎉 no goals
      homEquiv_naturality_right := fun f g => by
        ext
        -- ⊢ NatTrans.app (↑(composeEquiv J adj X✝ Y'✝) (f ≫ g)).val x✝ = NatTrans.app (↑ …
        dsimp [composeEquiv]
        -- ⊢ NatTrans.app (↑(Adjunction.homEquiv (Adjunction.whiskerRight Cᵒᵖ adj) X✝.val …
        erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
        -- ⊢ NatTrans.app (NatTrans.app (Adjunction.whiskerRight Cᵒᵖ adj).unit X✝.val ≫ ( …
        dsimp
        -- ⊢ NatTrans.app (NatTrans.app (Adjunction.whiskerRight Cᵒᵖ adj).unit X✝.val) x✝ …
        simp }
        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.adjunction CategoryTheory.Sheaf.adjunction

instance [IsRightAdjoint F] : IsRightAdjoint (sheafCompose J F) :=
  ⟨_, adjunction J (Adjunction.ofRightAdjoint F)⟩

section ForgetToType

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
        whiskerRight (J.toSheafify _) (forget D) := by
  dsimp [adjunctionToTypes, Adjunction.comp]
  -- ⊢ (NatTrans.app (Equivalence.toAdjunction (Equivalence.symm (sheafEquivSheafOf …
  simp
  -- ⊢ (NatTrans.app (Equivalence.toAdjunction (Equivalence.symm (sheafEquivSheafOf …
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.adjunction_to_types_unit_app_val CategoryTheory.Sheaf.adjunctionToTypes_unit_app_val

@[simp]
theorem adjunctionToTypes_counit_app_val {G : Type max v u ⥤ D} (adj : G ⊣ forget D)
    (X : Sheaf J D) :
    ((adjunctionToTypes J adj).counit.app X).val =
      J.sheafifyLift ((Functor.associator _ _ _).hom ≫ (adj.whiskerRight _).counit.app _) X.2 := by
  apply J.sheafifyLift_unique
  -- ⊢ toSheafify J (((whiskeringRight Cᵒᵖ (Type (max u v)) D).obj G).obj ((sheafTo …
  dsimp only [adjunctionToTypes, Adjunction.comp, NatTrans.comp_app,
    instCategorySheaf_comp_val, instCategorySheaf_id_val]
  rw [adjunction_counit_app_val]
  -- ⊢ toSheafify J (((whiskeringRight Cᵒᵖ (Type (max u v)) D).obj G).obj ((sheafTo …
  erw [Category.id_comp, J.sheafifyMap_sheafifyLift, J.toSheafify_sheafifyLift]
  -- ⊢ ((whiskeringRight Cᵒᵖ (Type (max u v)) D).obj G).map ((sheafToPresheaf J (Ty …
  ext
  -- ⊢ ↑(NatTrans.app (((whiskeringRight Cᵒᵖ (Type (max u v)) D).obj G).map ((sheaf …
  dsimp [sheafEquivSheafOfTypes, Equivalence.symm, Equivalence.toAdjunction,
    NatIso.ofComponents, Adjunction.whiskerRight, Adjunction.mkOfUnitCounit]
  simp
  -- 🎉 no goals

set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.adjunction_to_types_counit_app_val CategoryTheory.Sheaf.adjunctionToTypes_counit_app_val

instance [IsRightAdjoint (forget D)] : IsRightAdjoint (sheafForget J : Sheaf J D ⥤ _) :=
  ⟨_, adjunctionToTypes J (Adjunction.ofRightAdjoint (forget D))⟩

end ForgetToType

end

end Sheaf

end CategoryTheory
