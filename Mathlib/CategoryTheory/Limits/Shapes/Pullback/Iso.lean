/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
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

@[simp]
theorem pullbackConeOfLeftIso_x : (pullbackConeOfLeftIso f g).pt = Y := rfl

@[simp]
theorem pullbackConeOfLeftIso_fst : (pullbackConeOfLeftIso f g).fst = g ≫ inv f := rfl

@[simp]
theorem pullbackConeOfLeftIso_snd : (pullbackConeOfLeftIso f g).snd = 𝟙 _ := rfl

theorem pullbackConeOfLeftIso_π_app_none : (pullbackConeOfLeftIso f g).π.app none = g := by simp

@[simp]
theorem pullbackConeOfLeftIso_π_app_left : (pullbackConeOfLeftIso f g).π.app left = g ≫ inv f :=
  rfl

@[simp]
theorem pullbackConeOfLeftIso_π_app_right : (pullbackConeOfLeftIso f g).π.app right = 𝟙 _ := rfl

/-- Verify that the constructed limit cone is indeed a limit. -/
def pullbackConeOfLeftIsoIsLimit : IsLimit (pullbackConeOfLeftIso f g) :=
  PullbackCone.isLimitAux' _ fun s => ⟨s.snd, by simp [← s.condition_assoc]⟩

theorem hasPullback_of_left_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsoIsLimit f g⟩⟩⟩

attribute [local instance] hasPullback_of_left_iso

instance pullback_snd_iso_of_left_iso : IsIso (pullback.snd f g) := by
  refine ⟨⟨pullback.lift (g ≫ inv f) (𝟙 _) (by simp), ?_, by simp⟩⟩
  ext
  · simp [← pullback.condition_assoc]
  · simp

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

@[simp]
theorem pullbackConeOfRightIso_x : (pullbackConeOfRightIso f g).pt = X := rfl

@[simp]
theorem pullbackConeOfRightIso_fst : (pullbackConeOfRightIso f g).fst = 𝟙 _ := rfl

@[simp]
theorem pullbackConeOfRightIso_snd : (pullbackConeOfRightIso f g).snd = f ≫ inv g := rfl

theorem pullbackConeOfRightIso_π_app_none : (pullbackConeOfRightIso f g).π.app none = f := by simp

@[simp]
theorem pullbackConeOfRightIso_π_app_left : (pullbackConeOfRightIso f g).π.app left = 𝟙 _ :=
  rfl

@[simp]
theorem pullbackConeOfRightIso_π_app_right : (pullbackConeOfRightIso f g).π.app right = f ≫ inv g :=
  rfl

/-- Verify that the constructed limit cone is indeed a limit. -/
def pullbackConeOfRightIsoIsLimit : IsLimit (pullbackConeOfRightIso f g) :=
  PullbackCone.isLimitAux' _ fun s => ⟨s.fst, by simp [s.condition_assoc]⟩

theorem hasPullback_of_right_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfRightIsoIsLimit f g⟩⟩⟩

attribute [local instance] hasPullback_of_right_iso

instance pullback_fst_iso_of_right_iso : IsIso (pullback.fst f g) := by
  refine ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g) (by simp), ?_, by simp⟩⟩
  ext
  · simp
  · simp [pullback.condition_assoc]

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

@[simp]
theorem pushoutCoconeOfLeftIso_x : (pushoutCoconeOfLeftIso f g).pt = Z := rfl

@[simp]
theorem pushoutCoconeOfLeftIso_inl : (pushoutCoconeOfLeftIso f g).inl = inv f ≫ g := rfl

@[simp]
theorem pushoutCoconeOfLeftIso_inr : (pushoutCoconeOfLeftIso f g).inr = 𝟙 _ := rfl

theorem pushoutCoconeOfLeftIso_ι_app_none : (pushoutCoconeOfLeftIso f g).ι.app none = g := by
  simp

@[simp]
theorem pushoutCoconeOfLeftIso_ι_app_left : (pushoutCoconeOfLeftIso f g).ι.app left = inv f ≫ g :=
  rfl

@[simp]
theorem pushoutCoconeOfLeftIso_ι_app_right : (pushoutCoconeOfLeftIso f g).ι.app right = 𝟙 _ := rfl

/-- Verify that the constructed cocone is indeed a colimit. -/
def pushoutCoconeOfLeftIsoIsLimit : IsColimit (pushoutCoconeOfLeftIso f g) :=
  PushoutCocone.isColimitAux' _ fun s => ⟨s.inr, by simp [← s.condition]⟩

theorem hasPushout_of_left_iso : HasPushout f g :=
  ⟨⟨⟨_, pushoutCoconeOfLeftIsoIsLimit f g⟩⟩⟩

attribute [local instance] hasPushout_of_left_iso

instance pushout_inr_iso_of_left_iso : IsIso (pushout.inr f g) := by
  refine ⟨⟨pushout.desc (inv f ≫ g) (𝟙 _) (by simp), by simp, ?_⟩⟩
  ext
  · simp [← pushout.condition]
  · simp

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

@[simp]
theorem pushoutCoconeOfRightIso_x : (pushoutCoconeOfRightIso f g).pt = Y := rfl

@[simp]
theorem pushoutCoconeOfRightIso_inl : (pushoutCoconeOfRightIso f g).inl = 𝟙 _ := rfl

@[simp]
theorem pushoutCoconeOfRightIso_inr : (pushoutCoconeOfRightIso f g).inr = inv g ≫ f := rfl

theorem pushoutCoconeOfRightIso_ι_app_none : (pushoutCoconeOfRightIso f g).ι.app none = f := by
  simp

@[simp]
theorem pushoutCoconeOfRightIso_ι_app_left : (pushoutCoconeOfRightIso f g).ι.app left = 𝟙 _ := rfl

@[simp]
theorem pushoutCoconeOfRightIso_ι_app_right :
    (pushoutCoconeOfRightIso f g).ι.app right = inv g ≫ f := rfl

/-- Verify that the constructed cocone is indeed a colimit. -/
def pushoutCoconeOfRightIsoIsLimit : IsColimit (pushoutCoconeOfRightIso f g) :=
  PushoutCocone.isColimitAux' _ fun s => ⟨s.inl, by simp [← s.condition]⟩

theorem hasPushout_of_right_iso : HasPushout f g :=
  ⟨⟨⟨_, pushoutCoconeOfRightIsoIsLimit f g⟩⟩⟩

attribute [local instance] hasPushout_of_right_iso

instance pushout_inl_iso_of_right_iso : IsIso (pushout.inl _ _ : _ ⟶ pushout f g) := by
  refine ⟨⟨pushout.desc (𝟙 _) (inv g ≫ f) (by simp), by simp, ?_⟩⟩
  ext
  · simp
  · simp [pushout.condition]

@[reassoc (attr := simp)]
lemma pushout_inr_inv_inl_of_right_isIso :
    pushout.inr f g ≫ inv (pushout.inl f g) = inv g ≫ f := by
  rw [IsIso.eq_inv_comp, ← pushout.condition_assoc, IsIso.hom_inv_id, Category.comp_id]

end PushoutRightIso


end CategoryTheory.Limits
