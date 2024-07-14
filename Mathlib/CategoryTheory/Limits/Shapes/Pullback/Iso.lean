/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The pullback of an isomorphism

This file provides some basic results about the pullback (and pushout) of an isomorphism.

-/

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X Y Z : C}

section PullbackLeftIso

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso f]

/-- If `f : X ⟶ Z` is iso, then `X ×[Z] Y ≅ Y`. This is the explicit limit cone. -/
def pullbackConeOfLeftIso : PullbackCone f g :=
  PullbackCone.mk (g ≫ inv f) (𝟙 _) <| by simp
#align category_theory.limits.pullback_cone_of_left_iso CategoryTheory.Limits.pullbackConeOfLeftIso

@[simp]
theorem pullbackConeOfLeftIso_x : (pullbackConeOfLeftIso f g).pt = Y := rfl
set_option linter.uppercaseLean3 false in
#align category_theory.limits.pullback_cone_of_left_iso_X CategoryTheory.Limits.pullbackConeOfLeftIso_x

@[simp]
theorem pullbackConeOfLeftIso_fst : (pullbackConeOfLeftIso f g).fst = g ≫ inv f := rfl
#align category_theory.limits.pullback_cone_of_left_iso_fst CategoryTheory.Limits.pullbackConeOfLeftIso_fst

@[simp]
theorem pullbackConeOfLeftIso_snd : (pullbackConeOfLeftIso f g).snd = 𝟙 _ := rfl
#align category_theory.limits.pullback_cone_of_left_iso_snd CategoryTheory.Limits.pullbackConeOfLeftIso_snd

-- Porting note (#10618): simp can prove this; removed simp
theorem pullbackConeOfLeftIso_π_app_none : (pullbackConeOfLeftIso f g).π.app none = g := by simp
#align category_theory.limits.pullback_cone_of_left_iso_π_app_none CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_none

@[simp]
theorem pullbackConeOfLeftIso_π_app_left : (pullbackConeOfLeftIso f g).π.app left = g ≫ inv f :=
  rfl
#align category_theory.limits.pullback_cone_of_left_iso_π_app_left CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_left

@[simp]
theorem pullbackConeOfLeftIso_π_app_right : (pullbackConeOfLeftIso f g).π.app right = 𝟙 _ := rfl
#align category_theory.limits.pullback_cone_of_left_iso_π_app_right CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_right

/-- Verify that the constructed limit cone is indeed a limit. -/
def pullbackConeOfLeftIsoIsLimit : IsLimit (pullbackConeOfLeftIso f g) :=
  PullbackCone.isLimitAux' _ fun s => ⟨s.snd, by simp [← s.condition_assoc]⟩
#align category_theory.limits.pullback_cone_of_left_iso_is_limit CategoryTheory.Limits.pullbackConeOfLeftIsoIsLimit

theorem hasPullback_of_left_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsoIsLimit f g⟩⟩⟩
#align category_theory.limits.has_pullback_of_left_iso CategoryTheory.Limits.hasPullback_of_left_iso

attribute [local instance] hasPullback_of_left_iso

instance pullback_snd_iso_of_left_iso : IsIso (pullback.snd f g) := by
  refine ⟨⟨pullback.lift (g ≫ inv f) (𝟙 _) (by simp), ?_, by simp⟩⟩
  ext
  · simp [← pullback.condition_assoc]
  · simp [pullback.condition_assoc]
#align category_theory.limits.pullback_snd_iso_of_left_iso CategoryTheory.Limits.pullback_snd_iso_of_left_iso

@[reassoc (attr := simp)]
lemma pullback_inv_snd_fst_of_left_isIso :
    inv (pullback.snd f g) ≫ pullback.fst f g = g ≫ inv f := by
  rw [IsIso.inv_comp_eq, ← pullback.condition_assoc, IsIso.hom_inv_id, Category.comp_id]

end PullbackLeftIso

section PullbackRightIso

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g]

/-- If `g : Y ⟶ Z` is iso, then `X ×[Z] Y ≅ X`. This is the explicit limit cone. -/
def pullbackConeOfRightIso : PullbackCone f g :=
  PullbackCone.mk (𝟙 _) (f ≫ inv g) <| by simp
#align category_theory.limits.pullback_cone_of_right_iso CategoryTheory.Limits.pullbackConeOfRightIso

@[simp]
theorem pullbackConeOfRightIso_x : (pullbackConeOfRightIso f g).pt = X := rfl
set_option linter.uppercaseLean3 false in
#align category_theory.limits.pullback_cone_of_right_iso_X CategoryTheory.Limits.pullbackConeOfRightIso_x

@[simp]
theorem pullbackConeOfRightIso_fst : (pullbackConeOfRightIso f g).fst = 𝟙 _ := rfl
#align category_theory.limits.pullback_cone_of_right_iso_fst CategoryTheory.Limits.pullbackConeOfRightIso_fst

@[simp]
theorem pullbackConeOfRightIso_snd : (pullbackConeOfRightIso f g).snd = f ≫ inv g := rfl
#align category_theory.limits.pullback_cone_of_right_iso_snd CategoryTheory.Limits.pullbackConeOfRightIso_snd

-- Porting note (#10618): simp can prove this; removed simps
theorem pullbackConeOfRightIso_π_app_none : (pullbackConeOfRightIso f g).π.app none = f := by simp
#align category_theory.limits.pullback_cone_of_right_iso_π_app_none CategoryTheory.Limits.pullbackConeOfRightIso_π_app_none

@[simp]
theorem pullbackConeOfRightIso_π_app_left : (pullbackConeOfRightIso f g).π.app left = 𝟙 _ :=
  rfl
#align category_theory.limits.pullback_cone_of_right_iso_π_app_left CategoryTheory.Limits.pullbackConeOfRightIso_π_app_left

@[simp]
theorem pullbackConeOfRightIso_π_app_right : (pullbackConeOfRightIso f g).π.app right = f ≫ inv g :=
  rfl
#align category_theory.limits.pullback_cone_of_right_iso_π_app_right CategoryTheory.Limits.pullbackConeOfRightIso_π_app_right

/-- Verify that the constructed limit cone is indeed a limit. -/
def pullbackConeOfRightIsoIsLimit : IsLimit (pullbackConeOfRightIso f g) :=
  PullbackCone.isLimitAux' _ fun s => ⟨s.fst, by simp [s.condition_assoc]⟩
#align category_theory.limits.pullback_cone_of_right_iso_is_limit CategoryTheory.Limits.pullbackConeOfRightIsoIsLimit

theorem hasPullback_of_right_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfRightIsoIsLimit f g⟩⟩⟩
#align category_theory.limits.has_pullback_of_right_iso CategoryTheory.Limits.hasPullback_of_right_iso

attribute [local instance] hasPullback_of_right_iso

instance pullback_snd_iso_of_right_iso : IsIso (pullback.fst f g) := by
  refine ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g) (by simp), ?_, by simp⟩⟩
  ext
  · simp
  · simp [pullback.condition_assoc]
#align category_theory.limits.pullback_snd_iso_of_right_iso CategoryTheory.Limits.pullback_snd_iso_of_right_iso

@[reassoc (attr := simp)]
lemma pullback_inv_fst_snd_of_right_isIso :
    inv (pullback.fst f g) ≫ pullback.snd f g = f ≫ inv g := by
  rw [IsIso.inv_comp_eq, pullback.condition_assoc, IsIso.hom_inv_id, Category.comp_id]

end PullbackRightIso

section PushoutLeftIso

open WalkingSpan

variable (f : X ⟶ Y) (g : X ⟶ Z) [IsIso f]

/-- If `f : X ⟶ Y` is iso, then `Y ⨿[X] Z ≅ Z`. This is the explicit colimit cocone. -/
def pushoutCoconeOfLeftIso : PushoutCocone f g :=
  PushoutCocone.mk (inv f ≫ g) (𝟙 _) <| by simp
#align category_theory.limits.pushout_cocone_of_left_iso CategoryTheory.Limits.pushoutCoconeOfLeftIso

@[simp]
theorem pushoutCoconeOfLeftIso_x : (pushoutCoconeOfLeftIso f g).pt = Z := rfl
set_option linter.uppercaseLean3 false in
#align category_theory.limits.pushout_cocone_of_left_iso_X CategoryTheory.Limits.pushoutCoconeOfLeftIso_x

@[simp]
theorem pushoutCoconeOfLeftIso_inl : (pushoutCoconeOfLeftIso f g).inl = inv f ≫ g := rfl
#align category_theory.limits.pushout_cocone_of_left_iso_inl CategoryTheory.Limits.pushoutCoconeOfLeftIso_inl

@[simp]
theorem pushoutCoconeOfLeftIso_inr : (pushoutCoconeOfLeftIso f g).inr = 𝟙 _ := rfl
#align category_theory.limits.pushout_cocone_of_left_iso_inr CategoryTheory.Limits.pushoutCoconeOfLeftIso_inr

-- Porting note (#10618): simp can prove this; removed simp
theorem pushoutCoconeOfLeftIso_ι_app_none : (pushoutCoconeOfLeftIso f g).ι.app none = g := by
  simp
#align category_theory.limits.pushout_cocone_of_left_iso_ι_app_none CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_none

@[simp]
theorem pushoutCoconeOfLeftIso_ι_app_left : (pushoutCoconeOfLeftIso f g).ι.app left = inv f ≫ g :=
  rfl
#align category_theory.limits.pushout_cocone_of_left_iso_ι_app_left CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_left

@[simp]
theorem pushoutCoconeOfLeftIso_ι_app_right : (pushoutCoconeOfLeftIso f g).ι.app right = 𝟙 _ := rfl
#align category_theory.limits.pushout_cocone_of_left_iso_ι_app_right CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_right

/-- Verify that the constructed cocone is indeed a colimit. -/
def pushoutCoconeOfLeftIsoIsLimit : IsColimit (pushoutCoconeOfLeftIso f g) :=
  PushoutCocone.isColimitAux' _ fun s => ⟨s.inr, by simp [← s.condition]⟩
#align category_theory.limits.pushout_cocone_of_left_iso_is_limit CategoryTheory.Limits.pushoutCoconeOfLeftIsoIsLimit

theorem hasPushout_of_left_iso : HasPushout f g :=
  ⟨⟨⟨_, pushoutCoconeOfLeftIsoIsLimit f g⟩⟩⟩
#align category_theory.limits.has_pushout_of_left_iso CategoryTheory.Limits.hasPushout_of_left_iso

attribute [local instance] hasPushout_of_left_iso

instance pushout_inr_iso_of_left_iso : IsIso (pushout.inr f g) := by
  refine ⟨⟨pushout.desc (inv f ≫ g) (𝟙 _) (by simp), by simp, ?_⟩⟩
  ext
  · simp [← pushout.condition]
  · simp [pushout.condition_assoc]
#align category_theory.limits.pushout_inr_iso_of_left_iso CategoryTheory.Limits.pushout_inr_iso_of_left_iso

@[reassoc (attr := simp)]
lemma pushout_inl_inv_inr_of_right_isIso :
    pushout.inl f g ≫ inv (pushout.inr f g) = inv f ≫ g := by
  rw [IsIso.eq_inv_comp, pushout.condition_assoc, IsIso.hom_inv_id, Category.comp_id]

end PushoutLeftIso

section PushoutRightIso

open WalkingSpan

variable (f : X ⟶ Y) (g : X ⟶ Z) [IsIso g]

/-- If `f : X ⟶ Z` is iso, then `Y ⨿[X] Z ≅ Y`. This is the explicit colimit cocone. -/
def pushoutCoconeOfRightIso : PushoutCocone f g :=
  PushoutCocone.mk (𝟙 _) (inv g ≫ f) <| by simp
#align category_theory.limits.pushout_cocone_of_right_iso CategoryTheory.Limits.pushoutCoconeOfRightIso

@[simp]
theorem pushoutCoconeOfRightIso_x : (pushoutCoconeOfRightIso f g).pt = Y := rfl
set_option linter.uppercaseLean3 false in
#align category_theory.limits.pushout_cocone_of_right_iso_X CategoryTheory.Limits.pushoutCoconeOfRightIso_x

@[simp]
theorem pushoutCoconeOfRightIso_inl : (pushoutCoconeOfRightIso f g).inl = 𝟙 _ := rfl
#align category_theory.limits.pushout_cocone_of_right_iso_inl CategoryTheory.Limits.pushoutCoconeOfRightIso_inl

@[simp]
theorem pushoutCoconeOfRightIso_inr : (pushoutCoconeOfRightIso f g).inr = inv g ≫ f := rfl
#align category_theory.limits.pushout_cocone_of_right_iso_inr CategoryTheory.Limits.pushoutCoconeOfRightIso_inr

-- Porting note (#10618): simp can prove this; removed simp
theorem pushoutCoconeOfRightIso_ι_app_none : (pushoutCoconeOfRightIso f g).ι.app none = f := by
  simp
#align category_theory.limits.pushout_cocone_of_right_iso_ι_app_none CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_none

@[simp]
theorem pushoutCoconeOfRightIso_ι_app_left : (pushoutCoconeOfRightIso f g).ι.app left = 𝟙 _ := rfl
#align category_theory.limits.pushout_cocone_of_right_iso_ι_app_left CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_left

@[simp]
theorem pushoutCoconeOfRightIso_ι_app_right :
    (pushoutCoconeOfRightIso f g).ι.app right = inv g ≫ f := rfl
#align category_theory.limits.pushout_cocone_of_right_iso_ι_app_right CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_right

/-- Verify that the constructed cocone is indeed a colimit. -/
def pushoutCoconeOfRightIsoIsLimit : IsColimit (pushoutCoconeOfRightIso f g) :=
  PushoutCocone.isColimitAux' _ fun s => ⟨s.inl, by simp [← s.condition]⟩
#align category_theory.limits.pushout_cocone_of_right_iso_is_limit CategoryTheory.Limits.pushoutCoconeOfRightIsoIsLimit

theorem hasPushout_of_right_iso : HasPushout f g :=
  ⟨⟨⟨_, pushoutCoconeOfRightIsoIsLimit f g⟩⟩⟩
#align category_theory.limits.has_pushout_of_right_iso CategoryTheory.Limits.hasPushout_of_right_iso

attribute [local instance] hasPushout_of_right_iso

instance pushout_inl_iso_of_right_iso : IsIso (pushout.inl _ _ : _ ⟶ pushout f g) := by
  refine ⟨⟨pushout.desc (𝟙 _) (inv g ≫ f) (by simp), by simp, ?_⟩⟩
  ext
  · simp [← pushout.condition]
  · simp [pushout.condition]
#align category_theory.limits.pushout_inl_iso_of_right_iso CategoryTheory.Limits.pushout_inl_iso_of_right_iso

@[reassoc (attr := simp)]
lemma pushout_inr_inv_inl_of_right_isIso :
    pushout.inr f g ≫ inv (pushout.inl f g) = inv g ≫ f := by
  rw [IsIso.eq_inv_comp, ← pushout.condition_assoc, IsIso.hom_inv_id, Category.comp_id]

end PushoutRightIso


end CategoryTheory.Limits
