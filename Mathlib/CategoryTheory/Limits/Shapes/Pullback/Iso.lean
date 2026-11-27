/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# The pullback of an isomorphism

This file provides some basic results about the pullback (and pushout) of an isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X Y Z : C}

open WalkingCospan

section LeftIso

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso f]

to_dual_name_hint Fst Inl, Snd Inr, π ι

/-- If `f : X ⟶ Z` is iso, then `X ×[Z] Y ≅ Y`. This is the explicit limit cone. -/
@[to_dual /-- If `f : Z ⟶ X` is iso, then `X ⨿[Z] Y ≅ Y`. This is the explicit colimit cocone. -/]
def pullbackConeOfLeftIso : PullbackCone f g :=
  PullbackCone.mk (g ≫ inv f) (𝟙 _) <| by simp

@[to_dual (attr := simp)]
theorem pullbackConeOfLeftIso_x : (pullbackConeOfLeftIso f g).pt = Y := rfl

@[to_dual (attr := simp)]
theorem pullbackConeOfLeftIso_fst : (pullbackConeOfLeftIso f g).fst = g ≫ inv f := rfl

@[to_dual (attr := simp)]
theorem pullbackConeOfLeftIso_snd : (pullbackConeOfLeftIso f g).snd = 𝟙 _ := rfl

@[to_dual]
theorem pullbackConeOfLeftIso_π_app_none : (pullbackConeOfLeftIso f g).π.app none = g := by simp

@[to_dual (attr := simp)]
theorem pullbackConeOfLeftIso_π_app_left : (pullbackConeOfLeftIso f g).π.app left = g ≫ inv f :=
  rfl

@[to_dual (attr := simp)]
theorem pullbackConeOfLeftIso_π_app_right : (pullbackConeOfLeftIso f g).π.app right = 𝟙 _ := rfl

/-- Verify that the constructed limit cone is indeed a limit. -/
@[to_dual /-- Verify that the constructed cocone is indeed a colimit. -/]
def pullbackConeOfLeftIsoIsLimit : IsLimit (pullbackConeOfLeftIso f g) :=
  PullbackCone.isLimitAux' _ fun s => ⟨s.snd, by simp [← s.condition_assoc]⟩

@[deprecated (since := "2026-11-24")]
alias pushoutCoconeOfLeftIsoIsLimit := pushoutCoconeOfLeftIsoIsColimit

@[to_dual]
theorem hasPullback_of_left_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsoIsLimit f g⟩⟩⟩

attribute [local instance] hasPullback_of_left_iso

@[to_dual]
instance pullback_snd_iso_of_left_iso : IsIso (pullback.snd f g) := by
  refine ⟨⟨pullback.lift (g ≫ inv f) (𝟙 _) (by simp), ?_, by simp⟩⟩
  ext
  · simp [← pullback.condition_assoc]
  · simp

@[to_dual (attr := reassoc (attr := simp)) pushout_inl_inv_inr_of_right_isIso]
lemma pullback_inv_snd_fst_of_left_isIso :
    inv (pullback.snd f g) ≫ pullback.fst f g = g ≫ inv f := by
  rw [IsIso.inv_comp_eq, ← pullback.condition_assoc, IsIso.hom_inv_id, Category.comp_id]

end LeftIso

section RightIso

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g]

/-- If `g : Y ⟶ Z` is iso, then `X ×[Z] Y ≅ X`. This is the explicit limit cone. -/
@[to_dual /-- If `f : Z ⟶ Y` is iso, then `X ⨿[Z] Y ≅ X`. This is the explicit colimit cocone. -/]
def pullbackConeOfRightIso : PullbackCone f g :=
  PullbackCone.mk (𝟙 _) (f ≫ inv g) <| by simp

@[to_dual (attr := simp)]
theorem pullbackConeOfRightIso_x : (pullbackConeOfRightIso f g).pt = X := rfl

@[to_dual (attr := simp)]
theorem pullbackConeOfRightIso_fst : (pullbackConeOfRightIso f g).fst = 𝟙 _ := rfl

@[to_dual (attr := simp)]
theorem pullbackConeOfRightIso_snd : (pullbackConeOfRightIso f g).snd = f ≫ inv g := rfl

@[to_dual]
theorem pullbackConeOfRightIso_π_app_none : (pullbackConeOfRightIso f g).π.app none = f := by simp

@[to_dual]
theorem pullbackConeOfRightIso_π_app_left : (pullbackConeOfRightIso f g).π.app left = 𝟙 _ :=
  rfl

@[to_dual]
theorem pullbackConeOfRightIso_π_app_right : (pullbackConeOfRightIso f g).π.app right = f ≫ inv g :=
  rfl

/-- Verify that the constructed limit cone is indeed a limit. -/
@[to_dual /-- Verify that the constructed cocone is indeed a colimit. -/]
def pullbackConeOfRightIsoIsLimit : IsLimit (pullbackConeOfRightIso f g) :=
  PullbackCone.isLimitAux' _ fun s => ⟨s.fst, by simp [s.condition_assoc]⟩

@[deprecated (since := "2026-11-24")]
alias pushoutCoconeOfRightIsoIsLimit := pushoutCoconeOfRightIsoIsColimit

@[to_dual]
theorem hasPullback_of_right_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfRightIsoIsLimit f g⟩⟩⟩

attribute [local instance] hasPullback_of_right_iso

@[to_dual]
instance pullback_fst_iso_of_right_iso : IsIso (pullback.fst f g) := by
  refine ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g) (by simp), ?_, by simp⟩⟩
  ext
  · simp
  · simp [pullback.condition_assoc]

@[to_dual (attr := reassoc (attr := simp)) pushout_inr_inv_inl_of_right_isIso]
lemma pullback_inv_fst_snd_of_right_isIso :
    inv (pullback.fst f g) ≫ pullback.snd f g = f ≫ inv g := by
  rw [IsIso.inv_comp_eq, pullback.condition_assoc, IsIso.hom_inv_id, Category.comp_id]

end RightIso

end CategoryTheory.Limits
