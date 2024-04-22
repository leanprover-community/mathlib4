/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Whiskering

/-! # Functors which preserves sheafification

Given a Grothendieck topology `J` on `C` and `F : A ⥤ B`, we have defined
the type class `J.HasSheafCompose F` in the file `CategoryTheory.Sites.Whiskering`:
it says that the postcomposition with `F` induces a
functor `sheafCompose J F : Sheaf J A ⥤ Sheaf J B`.

In this file, assuming `HasWeakSheafify J A` and `HasWeakSheafify J B`,
we define a type class `PreservesSheafification J F` which expresses
that the sheafification commutes with the postcomposition with `F`.

We obtain `PreservesSheafification J (forget D)` when `D` is a concrete
category satisfying suitable conditions.

-/

universe v u

namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Type*} [Category A] [Category B]

section

variable (F : A ⥤ B) [HasWeakSheafify J A] [HasWeakSheafify J B] [J.HasSheafCompose F]
  (P : Cᵒᵖ ⥤ A)

/-- Given a Grothendieck topology `J` on `C`, and `F : A ⥤ B`, this is the natural
transformation defined for any presheaf `P : Cᵒᵖ ⥤ A`, from the associated sheaf of `P ⋙ B`
to the postcomposition with `F` of the associated sheaf of `P`. -/
noncomputable def presheafToSheafCompose :
    (whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B ⟶
      presheafToSheaf J A ⋙ sheafCompose J F where
  app P := ((sheafificationAdjunction J B).homEquiv _ _).symm (whiskerRight (toSheafify J P) F)
  naturality {P Q} f := by
    dsimp
    erw [← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_right_symm]
    dsimp
    rw [← whiskerRight_comp, ← whiskerRight_comp, toSheafify_naturality]

/-- The canonical map `sheafify J (P ⋙ F) ⟶ sheafify J P ⋙ F`. -/
noncomputable def sheafifyCompose :
    sheafify J (P ⋙ F) ⟶ sheafify J P ⋙ F :=
  (sheafToPresheaf J B).map ((presheafToSheafCompose J F).app P)

@[reassoc (attr := simp)]
lemma sheafifyCompose_fac :
    toSheafify J (P ⋙ F) ≫ sheafifyCompose J F P = whiskerRight (toSheafify J P) F := by
  dsimp only [sheafifyCompose, toSheafify, presheafToSheafCompose]
  erw [Adjunction.homEquiv_counit, Adjunction.unit_naturality_assoc]
  simp

/-- Given a Grothendieck topology `J` on `C` and `F : A ⥤ B`, this is the condition
that sheafification for `J` commutes with the postcomposition with `F`. -/
class PreservesSheafification : Prop where
  isIso : IsIso (presheafToSheafCompose J F) := by infer_instance

lemma PreservesSheafification.mk' (h : ∀ (P : Cᵒᵖ ⥤ A), IsIso (sheafifyCompose J F P)) :
    PreservesSheafification J F where
  isIso := by
    have : ∀ P, IsIso ((sheafToPresheaf J B).map ((presheafToSheafCompose J F).app P)) := h
    have : ∀ P, IsIso ((presheafToSheafCompose J F).app P) :=
      fun p => isIso_of_reflects_iso _ (sheafToPresheaf J B)
    apply NatIso.isIso_of_isIso_app

variable [PreservesSheafification J F]

attribute [instance] PreservesSheafification.isIso

/-- Given a Grothendieck topology `J` on `C` and `F : A ⥤ B`
such that `[PreservesSheafification J F]`, this is the condition
that sheafification for `J` commutes with the postcomposition with `F`. -/
noncomputable def presheafToSheafComposeIso :
    (whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B ≅
      presheafToSheaf J A ⋙ sheafCompose J F :=
  asIso (presheafToSheafCompose J F)

/-- The canonical isomorphism `sheafify J (P ⋙ F) ≅ sheafify J P ⋙ F` when
`F` preserves the sheafification. -/
noncomputable def sheafifyComposeIso :
    sheafify J (P ⋙ F) ≅ sheafify J P ⋙ F :=
  (sheafToPresheaf J B).mapIso ((presheafToSheafComposeIso J F).app P)

@[simp]
lemma sheafifyComposeIso_hom :
    (sheafifyComposeIso J F P).hom = sheafifyCompose J F P := rfl

@[reassoc (attr := simp)]
lemma sheafifyComposeIso_hom_inv_id :
    sheafifyCompose J F P ≫ (sheafifyComposeIso J F P).inv = 𝟙 _ :=
  (sheafifyComposeIso J F P).hom_inv_id

@[reassoc (attr := simp)]
lemma sheafifyComposeIso_inv_hom_id :
    (sheafifyComposeIso J F P).inv ≫ sheafifyCompose J F P = 𝟙 _ :=
  (sheafifyComposeIso J F P).inv_hom_id

instance : IsIso (sheafifyCompose J F P) :=
  (inferInstance : IsIso (sheafifyComposeIso J F P).hom)

@[reassoc (attr := simp)]
lemma sheafifyComposeIso_inv_fac :
    whiskerRight (toSheafify J P) F ≫ (sheafifyComposeIso J F P).inv =
      toSheafify J (P ⋙ F) := by
  rw [← cancel_mono (sheafifyCompose J F P), assoc, sheafifyComposeIso_inv_hom_id,
    comp_id, sheafifyCompose_fac]

end

namespace GrothendieckTopology

variable {D : Type*} [Category.{max v u} D]
  [ConcreteCategory.{max v u} D] [PreservesLimits (forget D)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]
  [∀ (α β : Type max u v) (fst snd : β → α),
      Limits.HasLimitsOfShape (Limits.WalkingMulticospan fst snd) D]
  [(forget D).ReflectsIsomorphisms]

@[reassoc]
lemma plusPlusIsoSheafify_hom_sheafifyCompose_forget (P : Cᵒᵖ ⥤ D) :
    (plusPlusIsoSheafify J _ (P ⋙ forget D)).hom ≫ sheafifyCompose J (forget D) P =
      (sheafifyCompIso J (forget D) P).inv ≫
        whiskerRight (plusPlusIsoSheafify J _ P).hom (forget D) := by
  sorry

@[reassoc]
lemma sheafifyCompose_forget_eq (P : Cᵒᵖ ⥤ D) :
    sheafifyCompose J (forget D) P =
      (plusPlusIsoSheafify J _ (P ⋙ forget D)).inv ≫
        (sheafifyCompIso J (forget D) P).inv ≫
          whiskerRight (plusPlusIsoSheafify J _ P).hom (forget D) := by
  rw [← cancel_epi (plusPlusIsoSheafify J _ (P ⋙ forget D)).hom,
    Iso.hom_inv_id_assoc, plusPlusIsoSheafify_hom_sheafifyCompose_forget]

instance : PreservesSheafification J (forget D) :=
  PreservesSheafification.mk' _ _ (fun P => by
    rw [J.sheafifyCompose_forget_eq]
    infer_instance)

end GrothendieckTopology

end CategoryTheory
