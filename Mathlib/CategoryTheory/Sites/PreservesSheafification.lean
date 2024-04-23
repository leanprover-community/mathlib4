/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Localization
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

We obtain `PreservesSheafification J F` when `F` is a functor between
concrete categories satisfying suitable conditions.

-/

universe v u

namespace CategoryTheory

open CategoryTheory Category Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Type*} [Category A] [Category B] (F : A ⥤ B)

namespace GrothendieckTopology

/-- A functor `F : A ⥤ B` preserves the sheafification for the Grothendieck
topology `J` on a category `C` if whenever a morphism of presheaves `f : P₁ ⟶ P₂`
in `Cᵒᵖ ⥤ A` is such that becomes an iso after sheafification, then it is
also the case of `whiskerRight f F : P₁ ⋙ F ⟶ P₂ ⋙ F`. -/
class PreservesSheafification : Prop where
  le : J.W ⊆ J.W.inverseImage ((whiskeringRight Cᵒᵖ A B).obj F)

variable [PreservesSheafification J F]

lemma W_of_preservesSheafification
    {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) (hf : J.W f) :
    J.W (whiskerRight f F) :=
  PreservesSheafification.le _ hf

variable [HasWeakSheafify J B]

lemma W_isInvertedBy_whiskeringRight_presheafToSheaf :
    J.W.IsInvertedBy (((whiskeringRight Cᵒᵖ A B).obj F) ⋙ presheafToSheaf J B) := by
  intro P₁ P₂ f hf
  dsimp
  rw [← W_iff]
  exact J.W_of_preservesSheafification F _ hf

end GrothendieckTopology

variable [HasWeakSheafify J A] [HasWeakSheafify J B]

/-- The functor `Sheaf J A ⥤ Sheaf J B` induced by a functor `F : A ⥤ B` which
preserves sheafification. -/
noncomputable def sheafCompose' [J.PreservesSheafification F] : Sheaf J A ⥤ Sheaf J B :=
  Localization.lift _ (J.W_isInvertedBy_whiskeringRight_presheafToSheaf F) (presheafToSheaf J A)

/-- The canonical isomorphism between `presheafToSheaf J A ⋙ sheafCompose' J F`
and `((whiskeringRight Cᵒᵖ A B).obj F) ⋙ presheafToSheaf J B` when `F : A ⥤ B`
preserves sheafification. -/
noncomputable def presheafToSheafCompSheafCompose' [J.PreservesSheafification F] :
    presheafToSheaf J A ⋙ sheafCompose' J F ≅
      ((whiskeringRight Cᵒᵖ A B).obj F) ⋙ presheafToSheaf J B :=
  Localization.fac _ _ _

variable {G₁ : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A} (adj₁ : G₁ ⊣ sheafToPresheaf J A)
  {G₂ : (Cᵒᵖ ⥤ B) ⥤ Sheaf J B} (adj₂ : G₂ ⊣ sheafToPresheaf J B)

lemma GrothendieckTopology.preservesSheafification_iff_of_adjunctions :
    J.PreservesSheafification F ↔ ∀ (P : Cᵒᵖ ⥤ A),
      IsIso (G₂.map (whiskerRight (adj₁.unit.app P) F)) := by
  simp only [← J.W_iff_isIso_map_of_adjunction adj₂]
  constructor
  · intro _ P
    apply W_of_preservesSheafification
    rw [J.W_iff_isIso_map_of_adjunction adj₁]
    infer_instance
  · intro h
    constructor
    intro P₁ P₂ f hf
    rw [J.W_iff_isIso_map_of_adjunction adj₁] at hf
    dsimp [MorphismProperty.inverseImage]
    rw [← J.W_postcomp_iff _ _ (h P₂), ← whiskerRight_comp]
    erw [adj₁.unit.naturality f]
    dsimp only [Functor.comp_map]
    rw [whiskerRight_comp, J.W_precomp_iff _ _ (h P₁)]
    apply J.W_of_isIso

section HasSheafCompose

variable [J.HasSheafCompose F]

end HasSheafCompose

#exit

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


def sheafCompose'Iso : sheafCompose' J F ≅ sheafCompose J F :=
  Localization.liftNatIso (presheafToSheaf J A) J.W
    (presheafToSheaf J A ⋙ sheafCompose' J F) (presheafToSheaf J A ⋙ sheafCompose J F) _ _
      (presheafToSheafCompSheafCompose' J F ≪≫ (by
        sorry))

end HasSheafCompose

#exit


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

section

variable {D E : Type*} [Category.{max v u} D] [Category.{max v u} E] (F : D ⥤ E)
  [∀ (α β : Type max v u) (fst snd : β → α), HasLimitsOfShape (WalkingMulticospan fst snd) D]
  [∀ (α β : Type max v u) (fst snd : β → α), HasLimitsOfShape (WalkingMulticospan fst snd) E]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ E]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
  [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
  [ConcreteCategory D] [ConcreteCategory E]
  [∀ X, PreservesColimitsOfShape (Cover J X)ᵒᵖ (forget D)]
  [∀ X, PreservesColimitsOfShape (Cover J X)ᵒᵖ (forget E)]
  [PreservesLimits (forget D)] [PreservesLimits (forget E)]
  [(forget D).ReflectsIsomorphisms] [(forget E).ReflectsIsomorphisms]

@[reassoc]
lemma plusPlusIsoSheafify_hom_sheafifyCompose (P : Cᵒᵖ ⥤ D) :
    (plusPlusIsoSheafify J _ (P ⋙ F)).hom ≫ sheafifyCompose J F P =
      (sheafifyCompIso J F P).inv ≫
        whiskerRight (plusPlusIsoSheafify J _ P).hom F := by
  sorry

@[reassoc]
lemma sheafifyCompose_eq (P : Cᵒᵖ ⥤ D) :
    sheafifyCompose J F P =
      (plusPlusIsoSheafify J _ (P ⋙ F)).inv ≫
        (sheafifyCompIso J F P).inv ≫
          whiskerRight (plusPlusIsoSheafify J _ P).hom F := by
  rw [← cancel_epi (plusPlusIsoSheafify J _ (P ⋙ F)).hom,
    Iso.hom_inv_id_assoc, plusPlusIsoSheafify_hom_sheafifyCompose]

instance : PreservesSheafification J F :=
  PreservesSheafification.mk' _ _ (fun P => by
    rw [J.sheafifyCompose_eq]
    infer_instance)

end

example {D : Type*} [Category.{max v u} D]
  [ConcreteCategory.{max v u} D] [PreservesLimits (forget D)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]
  [∀ (α β : Type max u v) (fst snd : β → α),
      Limits.HasLimitsOfShape (Limits.WalkingMulticospan fst snd) D]
  [(forget D).ReflectsIsomorphisms] : PreservesSheafification J (forget D) := inferInstance

end GrothendieckTopology

end CategoryTheory
