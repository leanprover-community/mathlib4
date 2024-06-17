/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Functors which preserves sheafification

In this file, given a Grothendieck topology `J` on `C` and `F : A ⥤ B`,
we define a type class `J.PreservesSheafification F`. We say that `F` preserves
the sheafification if whenever a morphism of presheaves `P₁ ⟶ P₂` induces
an isomorphism on the associated sheaves, then the induced map `P₁ ⋙ F ⟶ P₂ ⋙ F`
also induces an isomorphism on the associated sheaves. (Note: it suffices to check
this property for the map from any presheaf `P` to its associated sheaf, see
`GrothendieckTopology.preservesSheafification_iff_of_adjunctions`).

In general, we define `Sheaf.composeAndSheafify J F : Sheaf J A ⥤ Sheaf J B` as the functor
which sends a sheaf `G` to the sheafification of the composition `G.val ⋙ F`.
It `J.PreservesSheafification F`, we show that this functor can also be thought
as the localization of the functor `_ ⋙ F` on presheaves: we construct an isomorphism
`presheafToSheafCompComposeAndSheafifyIso` between
`presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F` and
`(whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B`.

Moreover, if we assume `J.HasSheafCompose F`, we obtain an isomorphism
`sheafifyComposeIso J F P : sheafify J (P ⋙ F) ≅ sheafify J P ⋙ F`.

We show that under suitable assumptions, the forget functor from a concrete
category preserves sheafification; this holds more generally for
functors between such concrete categories which commute both with
suitable limits and colimits.

## TODO
* construct an isomorphism `Sheaf.composeAndSheafify J F ≅ sheafCompose J F`

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
  le : J.W ≤ J.W.inverseImage ((whiskeringRight Cᵒᵖ A B).obj F)

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

section

variable [HasWeakSheafify J B]

/-- This is the functor sending a sheaf `X : Sheaf J A` to the sheafification
of `X.val ⋙ F`. -/
noncomputable abbrev Sheaf.composeAndSheafify : Sheaf J A ⥤ Sheaf J B :=
  sheafToPresheaf J A ⋙ (whiskeringRight _ _ _).obj F ⋙ presheafToSheaf J B
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.compose_and_sheafify CategoryTheory.Sheaf.composeAndSheafify

variable [HasWeakSheafify J A]

/-- The canonical natural transformation from
`(whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B` to
`presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F`. -/
@[simps!]
noncomputable def toPresheafToSheafCompComposeAndSheafify :
    (whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B ⟶
      presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F :=
  whiskerRight (sheafificationAdjunction J A).unit
    ((whiskeringRight _ _ _).obj F ⋙ presheafToSheaf J B)

variable [J.PreservesSheafification F]

instance : IsIso (toPresheafToSheafCompComposeAndSheafify J F) := by
  have : J.PreservesSheafification F := inferInstance
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  dsimp
  simpa only [← J.W_iff] using J.W_of_preservesSheafification F _ (J.W_toSheafify X)

/-- The canonical isomorphism between `presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F`
and `(whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B` when `F : A ⥤ B`
preserves sheafification. -/
@[simps! inv_app]
noncomputable def presheafToSheafCompComposeAndSheafifyIso :
    presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F ≅
      (whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B :=
  (asIso (toPresheafToSheafCompComposeAndSheafify J F)).symm

noncomputable instance : Localization.Lifting (presheafToSheaf J A) J.W
    ((whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B) (Sheaf.composeAndSheafify J F) :=
  ⟨presheafToSheafCompComposeAndSheafifyIso J F⟩

end

section

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
    rw [← MorphismProperty.postcomp_iff _ _ _ (h P₂), ← whiskerRight_comp]
    erw [adj₁.unit.naturality f]
    dsimp only [Functor.comp_map]
    rw [whiskerRight_comp, MorphismProperty.precomp_iff _ _ _ (h P₁)]
    apply Localization.LeftBousfield.W_of_isIso

section HasSheafCompose

variable [J.HasSheafCompose F]

/-- The canonical natural transformation
`(whiskeringRight Cᵒᵖ A B).obj F ⋙ G₂ ⟶ G₁ ⋙ sheafCompose J F`
when `F : A ⥤ B` is such that `J.HasSheafCompose F`, and that `G₁` and `G₂` are
left adjoints to the forget functors `sheafToPresheaf`. -/
def sheafComposeNatTrans :
    (whiskeringRight Cᵒᵖ A B).obj F ⋙ G₂ ⟶ G₁ ⋙ sheafCompose J F where
  app P := (adj₂.homEquiv _ _).symm (whiskerRight (adj₁.unit.app P) F)
  naturality {P Q} f:= by
    dsimp
    erw [← adj₂.homEquiv_naturality_left_symm,
      ← adj₂.homEquiv_naturality_right_symm]
    dsimp
    rw [← whiskerRight_comp, ← whiskerRight_comp]
    erw [adj₁.unit.naturality f]
    rfl

lemma sheafComposeNatTrans_fac (P : Cᵒᵖ ⥤ A) :
    adj₂.unit.app (P ⋙ F) ≫
      (sheafToPresheaf J B).map ((sheafComposeNatTrans J F adj₁ adj₂).app P) =
        whiskerRight (adj₁.unit.app P) F  := by
  dsimp only [sheafComposeNatTrans]
  erw [Adjunction.homEquiv_counit, Adjunction.unit_naturality_assoc,
    adj₂.right_triangle_components, comp_id]

lemma sheafComposeNatTrans_app_uniq (P : Cᵒᵖ ⥤ A)
    (α : G₂.obj (P ⋙ F) ⟶ (sheafCompose J F).obj (G₁.obj P))
    (hα : adj₂.unit.app (P ⋙ F) ≫ (sheafToPresheaf J B).map α =
        whiskerRight (adj₁.unit.app P) F) :
    α = (sheafComposeNatTrans J F adj₁ adj₂).app P := by
  apply (adj₂.homEquiv _ _).injective
  dsimp [sheafComposeNatTrans]
  erw [Equiv.apply_symm_apply]
  rw [← hα]
  apply adj₂.homEquiv_unit

lemma GrothendieckTopology.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose :
    J.PreservesSheafification F ↔ IsIso (sheafComposeNatTrans J F adj₁ adj₂) := by
  rw [J.preservesSheafification_iff_of_adjunctions F adj₁ adj₂,
    NatTrans.isIso_iff_isIso_app]
  apply forall_congr'
  intro P
  rw [← J.W_iff_isIso_map_of_adjunction adj₂, ← J.W_sheafToPreheaf_map_iff_isIso,
    ← sheafComposeNatTrans_fac J F adj₁ adj₂,
    MorphismProperty.precomp_iff _ _ _ (J.W_adj_unit_app adj₂ (P ⋙ F))]

variable [J.PreservesSheafification F]

instance : IsIso (sheafComposeNatTrans J F adj₁ adj₂) := by
  rw [← J.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose]
  infer_instance

/-- The canonical natural isomorphism
`(whiskeringRight Cᵒᵖ A B).obj F ⋙ G₂ ≅ G₁ ⋙ sheafCompose J F`
when `F : A ⥤ B` preserves sheafification, and that `G₁` and `G₂` are
left adjoints to the forget functors `sheafToPresheaf`. -/
noncomputable def sheafComposeNatIso :
    (whiskeringRight Cᵒᵖ A B).obj F ⋙ G₂ ≅ G₁ ⋙ sheafCompose J F :=
  asIso (sheafComposeNatTrans J F adj₁ adj₂)

end HasSheafCompose

end

section HasSheafCompose

variable [HasWeakSheafify J A] [HasWeakSheafify J B] [J.HasSheafCompose F]
  [J.PreservesSheafification F] (P : Cᵒᵖ ⥤ A)

/-- The canonical isomorphism `sheafify J (P ⋙ F) ≅ sheafify J P ⋙ F` when
`F` preserves the sheafification. -/
noncomputable def sheafifyComposeIso :
    sheafify J (P ⋙ F) ≅ sheafify J P ⋙ F :=
  (sheafToPresheaf J B).mapIso
    ((sheafComposeNatIso J F (sheafificationAdjunction J A) (sheafificationAdjunction J B)).app P)

@[reassoc (attr := simp)]
lemma sheafComposeIso_hom_fac :
    toSheafify J (P ⋙ F) ≫ (sheafifyComposeIso J F P).hom =
      whiskerRight (toSheafify J P) F :=
  sheafComposeNatTrans_fac J F (sheafificationAdjunction J A) (sheafificationAdjunction J B) P

@[reassoc (attr := simp)]
lemma sheafComposeIso_inv_fac :
    whiskerRight (toSheafify J P) F ≫ (sheafifyComposeIso J F P).inv =
      toSheafify J (P ⋙ F) := by
  rw [← sheafComposeIso_hom_fac, assoc, Iso.hom_inv_id, comp_id]

end HasSheafCompose

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

lemma sheafToPresheaf_map_sheafComposeNatTrans_eq_sheafifyCompIso_inv (P : Cᵒᵖ ⥤ D) :
    (sheafToPresheaf J E).map
      ((sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E)).app P) =
      (sheafifyCompIso J F P).inv := by
  suffices (sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E)).app P =
    ⟨(sheafifyCompIso J F P).inv⟩ by
    rw [this]
    rfl
  apply ((plusPlusAdjunction J E).homEquiv _ _).injective
  convert sheafComposeNatTrans_fac J F (plusPlusAdjunction J D) (plusPlusAdjunction J E) P
  all_goals
    dsimp [plusPlusAdjunction]
    simp

instance (P : Cᵒᵖ ⥤ D) :
    IsIso ((sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E)).app P) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf J E),
    sheafToPresheaf_map_sheafComposeNatTrans_eq_sheafifyCompIso_inv]
  infer_instance

instance : IsIso (sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E)) :=
  NatIso.isIso_of_isIso_app _

instance : PreservesSheafification J F := by
  rw [preservesSheafification_iff_of_adjunctions_of_hasSheafCompose _ _
    (plusPlusAdjunction J D) (plusPlusAdjunction J E)]
  infer_instance

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
