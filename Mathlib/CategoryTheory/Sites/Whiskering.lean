/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Sheafification

#align_import category_theory.sites.whiskering from "leanprover-community/mathlib"@"9f9015c645d85695581237cc761981036be8bd37"

/-!

In this file we construct the functor `Sheaf J A ⥤ Sheaf J B` between sheaf categories
obtained by composition with a functor `F : A ⥤ B`.

In order for the sheaf condition to be preserved, `F` must preserve the correct limits.
The lemma `Presheaf.IsSheaf.comp` says that composition with such an `F` indeed preserves the
sheaf condition.

The functor between sheaf categories is called `sheafCompose J F`.
Given a natural transformation `η : F ⟶ G`, we obtain a natural transformation
`sheafCompose J F ⟶ sheafCompose J G`, which we call `sheafCompose_map J η`.

Under the assumptions `HasWeakSheafify J A`, `HasWeakSheafify J B`, we define
a type class `PreservesSheafification J F` which expresses that sheafification
commutes with the postcomposition with `F`.

-/


namespace CategoryTheory

open CategoryTheory Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable {B : Type u₃} [Category.{v₃} B]
variable (J : GrothendieckTopology C)
variable {U : C} (R : Presieve U)
variable (F G H : A ⥤ B) (η : F ⟶ G) (γ : G ⟶ H)

/-- Describes the property of a functor to "preserve sheaves". -/
class GrothendieckTopology.HasSheafCompose : Prop where
  /-- For every sheaf `P`, `P ⋙ F` is a sheaf. -/
  isSheaf (P : Cᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf J P) : Presheaf.IsSheaf J (P ⋙ F)

variable [J.HasSheafCompose F] [J.HasSheafCompose G] [J.HasSheafCompose H]

/-- Composing a functor which `HasSheafCompose`, yields a functor between sheaf categories. -/
@[simps]
def sheafCompose : Sheaf J A ⥤ Sheaf J B where
  obj G := ⟨G.val ⋙ F, GrothendieckTopology.HasSheafCompose.isSheaf G.val G.2⟩
  map η := ⟨whiskerRight η.val _⟩
  map_id _ := Sheaf.Hom.ext _ _ <| whiskerRight_id _
  map_comp _ _ := Sheaf.Hom.ext _ _ <| whiskerRight_comp _ _ _
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf_compose CategoryTheory.sheafCompose

variable {F G}

/--
If `η : F ⟶ G` is a natural transformation then we obtain a morphism of functors
`sheafCompose J F ⟶ sheafCompose J G` by whiskering with `η` on the level of presheaves.
-/
def sheafCompose_map : sheafCompose J F ⟶ sheafCompose J G where
  app := fun X => .mk <| whiskerLeft _ η

@[simp]
lemma sheafCompose_id : sheafCompose_map (F := F) J (𝟙 _) = 𝟙 _ := rfl

@[simp]
lemma sheafCompose_comp :
    sheafCompose_map J (η ≫ γ) = sheafCompose_map J η ≫ sheafCompose_map J γ := rfl

namespace GrothendieckTopology.Cover

variable (F G) {J}
variable (P : Cᵒᵖ ⥤ A) {X : C} (S : J.Cover X)

/-- The multicospan associated to a cover `S : J.Cover X` and a presheaf of the form `P ⋙ F`
is isomorphic to the composition of the multicospan associated to `S` and `P`,
composed with `F`. -/
def multicospanComp : (S.index (P ⋙ F)).multicospan ≅ (S.index P).multicospan ⋙ F :=
  NatIso.ofComponents
    (fun t =>
      match t with
      | WalkingMulticospan.left a => eqToIso rfl
      | WalkingMulticospan.right b => eqToIso rfl)
    (by
      rintro (a | b) (a | b) (f | f | f)
      all_goals aesop_cat)
#align category_theory.grothendieck_topology.cover.multicospan_comp CategoryTheory.GrothendieckTopology.Cover.multicospanComp

@[simp]
theorem multicospanComp_app_left (a) :
    (S.multicospanComp F P).app (WalkingMulticospan.left a) = eqToIso rfl :=
  rfl
#align category_theory.grothendieck_topology.cover.multicospan_comp_app_left CategoryTheory.GrothendieckTopology.Cover.multicospanComp_app_left

@[simp]
theorem multicospanComp_app_right (b) :
    (S.multicospanComp F P).app (WalkingMulticospan.right b) = eqToIso rfl :=
  rfl
#align category_theory.grothendieck_topology.cover.multicospan_comp_app_right CategoryTheory.GrothendieckTopology.Cover.multicospanComp_app_right

@[simp]
theorem multicospanComp_hom_app_left (a) :
    (S.multicospanComp F P).hom.app (WalkingMulticospan.left a) = eqToHom rfl :=
  rfl
#align category_theory.grothendieck_topology.cover.multicospan_comp_hom_app_left CategoryTheory.GrothendieckTopology.Cover.multicospanComp_hom_app_left

@[simp]
theorem multicospanComp_hom_app_right (b) :
    (S.multicospanComp F P).hom.app (WalkingMulticospan.right b) = eqToHom rfl :=
  rfl
#align category_theory.grothendieck_topology.cover.multicospan_comp_hom_app_right CategoryTheory.GrothendieckTopology.Cover.multicospanComp_hom_app_right

@[simp]
theorem multicospanComp_hom_inv_left (P : Cᵒᵖ ⥤ A) {X : C} (S : J.Cover X) (a) :
    (S.multicospanComp F P).inv.app (WalkingMulticospan.left a) = eqToHom rfl :=
  rfl
#align category_theory.grothendieck_topology.cover.multicospan_comp_hom_inv_left CategoryTheory.GrothendieckTopology.Cover.multicospanComp_hom_inv_left

@[simp]
theorem multicospanComp_hom_inv_right (P : Cᵒᵖ ⥤ A) {X : C} (S : J.Cover X) (b) :
    (S.multicospanComp F P).inv.app (WalkingMulticospan.right b) = eqToHom rfl :=
  rfl
#align category_theory.grothendieck_topology.cover.multicospan_comp_hom_inv_right CategoryTheory.GrothendieckTopology.Cover.multicospanComp_hom_inv_right

/-- Mapping the multifork associated to a cover `S : J.Cover X` and a presheaf `P` with
respect to a functor `F` is isomorphic (upto a natural isomorphism of the underlying functors)
to the multifork associated to `S` and `P ⋙ F`. -/
def mapMultifork :
    F.mapCone (S.multifork P) ≅
      (Limits.Cones.postcompose (S.multicospanComp F P).hom).obj (S.multifork (P ⋙ F)) :=
  Cones.ext (eqToIso rfl)
    (by
      rintro (a | b)
      · dsimp
        erw [Category.id_comp, multicospanComp_hom_app_left, eqToHom_refl, Category.comp_id]
      · dsimp
        erw [Functor.map_comp, Category.assoc, Category.id_comp,
          multicospanComp_hom_app_right, eqToHom_refl, Category.comp_id]
        rfl)
#align category_theory.grothendieck_topology.cover.map_multifork CategoryTheory.GrothendieckTopology.Cover.mapMultifork

end GrothendieckTopology.Cover

/--
Composing a sheaf with a functor preserving the limit of `(S.index P).multicospan` yields a functor
between sheaf categories.
-/
instance hasSheafCompose_of_preservesMulticospan (F : A ⥤ B)
    [∀ (X : C) (S : J.Cover X) (P : Cᵒᵖ ⥤ A), PreservesLimit (S.index P).multicospan F] :
    J.HasSheafCompose F where
  isSheaf P hP := by
    rw [Presheaf.isSheaf_iff_multifork] at hP ⊢
    intro X S
    obtain ⟨h⟩ := hP X S
    replace h := isLimitOfPreserves F h
    replace h := Limits.IsLimit.ofIsoLimit h (S.mapMultifork F P)
    exact ⟨Limits.IsLimit.postcomposeHomEquiv (S.multicospanComp F P) _ h⟩

/--
Composing a sheaf with a functor preserving limits of the same size as the hom sets in `C` yields a
functor between sheaf categories.

Note: the size of the limit that `F` is required to preserve in
`hasSheafCompose_of_preservesMulticospan` is in general larger than this.
-/
instance hasSheafCompose_of_preservesLimitsOfSize [PreservesLimitsOfSize.{v₁, max u₁ v₁} F] :
    J.HasSheafCompose F where
  isSheaf _ hP := Presheaf.isSheaf_comp_of_isSheaf J _ F hP

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

namespace GrothendieckTopology

variable {D : Type*} [Category.{max v₁ u₁} D]
  [ConcreteCategory.{max v₁ u₁} D] [PreservesLimits (forget D)]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]
  [(forget D).ReflectsIsomorphisms]

/-- The canonical isomorphism `J.plusObj (P ⋙ forget D) ≅ J.plusObj P ⋙ forget D`. -/
def plusObjComposeForget (P : Cᵒᵖ ⥤ D) :
    J.plusObj (P ⋙ forget D) ≅ J.plusObj P ⋙ forget D := by
  sorry

@[reassoc (attr := simp)]
lemma plusObjComposeForget_hom_naturality {P Q : Cᵒᵖ ⥤ D} (φ : P ⟶ Q) :
    J.plusMap (whiskerRight φ (forget D)) ≫ (J.plusObjComposeForget Q).hom =
    (J.plusObjComposeForget P).hom ≫
      whiskerRight (J.plusMap φ) (forget D) := sorry

@[reassoc (attr := simp)]
lemma plusObjComposeForget_hom_fac (P : Cᵒᵖ ⥤ D) :
    J.toPlus (P ⋙ forget D) ≫ (J.plusObjComposeForget P).hom =
      whiskerRight (J.toPlus P) (forget D) := by
  sorry

/-- The canonical isomorphism `J.sheafify (P ⋙ forget D) ≅ J.sheafify P ⋙ forget D`. -/
noncomputable def sheafifyComposeForgetIso (P : Cᵒᵖ ⥤ D) :
    J.sheafify (P ⋙ forget D) ≅ J.sheafify P ⋙ forget D :=
  (J.plusFunctor _).mapIso (J.plusObjComposeForget P) ≪≫
    J.plusObjComposeForget (plusObj J P)

@[reassoc (attr := simp)]
lemma sheafifyComposeForget_fac (P : Cᵒᵖ ⥤ D) :
    J.toSheafify (P ⋙ forget D) ≫ (J.sheafifyComposeForgetIso P).hom =
      whiskerRight (J.toSheafify P) (forget D) := by
  dsimp [toSheafify, sheafifyComposeForgetIso]
  rw [assoc, ← plusMap_comp_assoc, plusObjComposeForget_hom_fac,
    plusObjComposeForget_hom_naturality, plusMap_toPlus,
    plusObjComposeForget_hom_fac_assoc, toPlus_naturality,
    plusMap_toPlus, whiskerRight_comp]

@[reassoc]
lemma sheafifyCompose_forget_eq (P : Cᵒᵖ ⥤ D) :
    sheafifyCompose J (forget D) P =
      (plusPlusIsoSheafify J _ (P ⋙ forget D)).inv ≫
        (J.sheafifyComposeForgetIso P).hom ≫
          whiskerRight (plusPlusIsoSheafify J _ P).hom (forget D) := by
  sorry

instance : PreservesSheafification J (forget D) :=
  PreservesSheafification.mk' _ _ (fun P => by
    rw [J.sheafifyCompose_forget_eq]
    infer_instance)

end GrothendieckTopology

end CategoryTheory
