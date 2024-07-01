/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel, Bhavik Mehta, Andrew Yang, Emily Riehl
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks.Mono

#align_import category_theory.limits.shapes.pullbacks from "leanprover-community/mathlib"@"7316286ff2942aa14e540add9058c6b0aa1c8070"

/-!
# Constructions with pullbacks

The file `Pullbacks/Diagrams.lean` provides results for some different constructions using
pullbacks. The dual results for pushouts are also available in this file.

## Main results
* The pullback by an isomorphism.

* Pasting laws

* Associativity of pullbacks

-/

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

section PullbackLeftIso

open WalkingCospan

-- TODO: this could go in pullback cone.... (would allow mono to move elsewhere)
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

instance pullback_snd_iso_of_left_iso : IsIso (pullback.snd : pullback f g ⟶ _) := by
  refine ⟨⟨pullback.lift (g ≫ inv f) (𝟙 _) (by simp), ?_, by simp⟩⟩
  ext
  · simp [← pullback.condition_assoc]
  · simp [pullback.condition_assoc]
#align category_theory.limits.pullback_snd_iso_of_left_iso CategoryTheory.Limits.pullback_snd_iso_of_left_iso

variable (i : Z ⟶ W) [Mono i]

-- TODO: can golf this easily w/ nth_rw + exact (or just simpa only!)
instance hasPullback_of_right_factors_mono (f : X ⟶ Z) : HasPullback i (f ≫ i) := by
  conv =>
    congr
    rw [← Category.id_comp i]
  infer_instance
#align category_theory.limits.has_pullback_of_right_factors_mono CategoryTheory.Limits.hasPullback_of_right_factors_mono

instance pullback_snd_iso_of_right_factors_mono (f : X ⟶ Z) :
    IsIso (pullback.snd : pullback i (f ≫ i) ⟶ _) := by
  #adaptation_note /-- nightly-testing 2024-04-01
  this could not be placed directly in the `show from` without `dsimp` -/
  have := limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono (𝟙 _) f i⟩ WalkingCospan.right
  dsimp only [cospan_right, id_eq, eq_mpr_eq_cast, PullbackCone.mk_pt, PullbackCone.mk_π_app,
    Functor.const_obj_obj, cospan_one] at this
  convert (congrArg IsIso (show _ ≫ pullback.snd = _ from this)).mp inferInstance
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
#align category_theory.limits.pullback_snd_iso_of_right_factors_mono CategoryTheory.Limits.pullback_snd_iso_of_right_factors_mono

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

instance pullback_snd_iso_of_right_iso : IsIso (pullback.fst : pullback f g ⟶ _) := by
  refine ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g) (by simp), ?_, by simp⟩⟩
  ext
  · simp
  · simp [pullback.condition_assoc]
#align category_theory.limits.pullback_snd_iso_of_right_iso CategoryTheory.Limits.pullback_snd_iso_of_right_iso

variable (i : Z ⟶ W) [Mono i]

instance hasPullback_of_left_factors_mono (f : X ⟶ Z) : HasPullback (f ≫ i) i := by
  conv =>
    congr
    case g => rw [← Category.id_comp i]
  infer_instance
#align category_theory.limits.has_pullback_of_left_factors_mono CategoryTheory.Limits.hasPullback_of_left_factors_mono

instance pullback_snd_iso_of_left_factors_mono (f : X ⟶ Z) :
    IsIso (pullback.fst : pullback (f ≫ i) i ⟶ _) := by
  #adaptation_note /-- nightly-testing 2024-04-01
  this could not be placed directly in the `show from` without `dsimp` -/
  have := limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono f (𝟙 _) i⟩ WalkingCospan.left
  dsimp only [cospan_left, id_eq, eq_mpr_eq_cast, PullbackCone.mk_pt, PullbackCone.mk_π_app,
    Functor.const_obj_obj, cospan_one] at this
  convert (congrArg IsIso (show _ ≫ pullback.fst = _ from this)).mp inferInstance
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
#align category_theory.limits.pullback_snd_iso_of_left_factors_mono CategoryTheory.Limits.pullback_snd_iso_of_left_factors_mono

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

instance pushout_inr_iso_of_left_iso : IsIso (pushout.inr : _ ⟶ pushout f g) := by
  refine ⟨⟨pushout.desc (inv f ≫ g) (𝟙 _) (by simp), by simp, ?_⟩⟩
  ext
  · simp [← pushout.condition]
  · simp [pushout.condition_assoc]
#align category_theory.limits.pushout_inr_iso_of_left_iso CategoryTheory.Limits.pushout_inr_iso_of_left_iso

variable (h : W ⟶ X) [Epi h]

instance hasPushout_of_right_factors_epi (f : X ⟶ Y) : HasPushout h (h ≫ f) := by
  conv =>
    congr
    rw [← Category.comp_id h]
  infer_instance
#align category_theory.limits.has_pushout_of_right_factors_epi CategoryTheory.Limits.hasPushout_of_right_factors_epi

instance pushout_inr_iso_of_right_factors_epi (f : X ⟶ Y) :
    IsIso (pushout.inr : _ ⟶ pushout h (h ≫ f)) := by
  convert (congrArg IsIso (show pushout.inr ≫ _ = _ from colimit.isoColimitCocone_ι_inv
    ⟨_, pushoutIsPushoutOfEpiComp (𝟙 _) f h⟩ WalkingSpan.right)).mp
    inferInstance
  · apply (Category.comp_id _).symm
  · apply (Category.comp_id _).symm
#align category_theory.limits.pushout_inr_iso_of_right_factors_epi CategoryTheory.Limits.pushout_inr_iso_of_right_factors_epi

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

instance pushout_inl_iso_of_right_iso : IsIso (pushout.inl : _ ⟶ pushout f g) := by
  refine ⟨⟨pushout.desc (𝟙 _) (inv g ≫ f) (by simp), by simp, ?_⟩⟩
  ext
  · simp [← pushout.condition]
  · simp [pushout.condition]
#align category_theory.limits.pushout_inl_iso_of_right_iso CategoryTheory.Limits.pushout_inl_iso_of_right_iso

variable (h : W ⟶ X) [Epi h]

instance hasPushout_of_left_factors_epi (f : X ⟶ Y) : HasPushout (h ≫ f) h := by
  conv =>
    congr
    case g => rw [← Category.comp_id h]
  infer_instance
#align category_theory.limits.has_pushout_of_left_factors_epi CategoryTheory.Limits.hasPushout_of_left_factors_epi

instance pushout_inl_iso_of_left_factors_epi (f : X ⟶ Y) :
    IsIso (pushout.inl : _ ⟶ pushout (h ≫ f) h) := by
  convert (congrArg IsIso (show pushout.inl ≫ _ = _ from colimit.isoColimitCocone_ι_inv
    ⟨_, pushoutIsPushoutOfEpiComp f (𝟙 _) h⟩ WalkingSpan.left)).mp
        inferInstance;
  · exact (Category.comp_id _).symm
  · exact (Category.comp_id _).symm
#align category_theory.limits.pushout_inl_iso_of_left_factors_epi CategoryTheory.Limits.pushout_inl_iso_of_left_factors_epi

end PushoutRightIso

section PasteLemma

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃)
variable (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) (i₃ : X₃ ⟶ Y₃)
variable (h₁ : i₁ ≫ g₁ = f₁ ≫ i₂) (h₂ : i₂ ≫ g₂ = f₂ ≫ i₃)

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the big square is a pullback if both the small squares are.
-/
def bigSquareIsPullback (H : IsLimit (PullbackCone.mk _ _ h₂))
    (H' : IsLimit (PullbackCone.mk _ _ h₁)) :
    IsLimit
      (PullbackCone.mk _ _
        (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
          rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc])) := by
  fapply PullbackCone.isLimitAux'
  intro s
  have : (s.fst ≫ g₁) ≫ g₂ = s.snd ≫ i₃ := by rw [← s.condition, Category.assoc]
  rcases PullbackCone.IsLimit.lift' H (s.fst ≫ g₁) s.snd this with ⟨l₁, hl₁, hl₁'⟩
  rcases PullbackCone.IsLimit.lift' H' s.fst l₁ hl₁.symm with ⟨l₂, hl₂, hl₂'⟩
  use l₂
  use hl₂
  use
    show l₂ ≫ f₁ ≫ f₂ = s.snd by
      rw [← hl₁', ← hl₂', Category.assoc]
      rfl
  intro m hm₁ hm₂
  apply PullbackCone.IsLimit.hom_ext H'
  · erw [hm₁, hl₂]
  · apply PullbackCone.IsLimit.hom_ext H
    · erw [Category.assoc, ← h₁, ← Category.assoc, hm₁, ← hl₂, Category.assoc, Category.assoc, h₁]
      rfl
    · erw [Category.assoc, hm₂, ← hl₁', ← hl₂']
#align category_theory.limits.big_square_is_pullback CategoryTheory.Limits.bigSquareIsPullback

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the big square is a pushout if both the small squares are.
-/
def bigSquareIsPushout (H : IsColimit (PushoutCocone.mk _ _ h₂))
    (H' : IsColimit (PushoutCocone.mk _ _ h₁)) :
    IsColimit
      (PushoutCocone.mk _ _
        (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
          rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc])) := by
  fapply PushoutCocone.isColimitAux'
  intro s
  have : i₁ ≫ s.inl = f₁ ≫ f₂ ≫ s.inr := by rw [s.condition, Category.assoc]
  rcases PushoutCocone.IsColimit.desc' H' s.inl (f₂ ≫ s.inr) this with ⟨l₁, hl₁, hl₁'⟩
  rcases PushoutCocone.IsColimit.desc' H l₁ s.inr hl₁' with ⟨l₂, hl₂, hl₂'⟩
  use l₂
  use
    show (g₁ ≫ g₂) ≫ l₂ = s.inl by
      rw [← hl₁, ← hl₂, Category.assoc]
      rfl
  use hl₂'
  intro m hm₁ hm₂
  apply PushoutCocone.IsColimit.hom_ext H
  · apply PushoutCocone.IsColimit.hom_ext H'
    · erw [← Category.assoc, hm₁, hl₂, hl₁]
    · erw [← Category.assoc, h₂, Category.assoc, hm₂, ← hl₂', ← Category.assoc, ← Category.assoc, ←
        h₂]
      rfl
  · erw [hm₂, hl₂']
#align category_theory.limits.big_square_is_pushout CategoryTheory.Limits.bigSquareIsPushout

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the left square is a pullback if the right square and the big square are.
-/
def leftSquareIsPullback (H : IsLimit (PullbackCone.mk _ _ h₂))
    (H' :
      IsLimit
        (PullbackCone.mk _ _
          (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
            rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]))) :
    IsLimit (PullbackCone.mk _ _ h₁) := by
  fapply PullbackCone.isLimitAux'
  intro s
  have : s.fst ≫ g₁ ≫ g₂ = (s.snd ≫ f₂) ≫ i₃ := by
    rw [← Category.assoc, s.condition, Category.assoc, Category.assoc, h₂]
  rcases PullbackCone.IsLimit.lift' H' s.fst (s.snd ≫ f₂) this with ⟨l₁, hl₁, hl₁'⟩
  use l₁
  use hl₁
  constructor
  · apply PullbackCone.IsLimit.hom_ext H
    · erw [Category.assoc, ← h₁, ← Category.assoc, hl₁, s.condition]
      rfl
    · erw [Category.assoc, hl₁']
      rfl
  · intro m hm₁ hm₂
    apply PullbackCone.IsLimit.hom_ext H'
    · erw [hm₁, hl₁]
    · erw [hl₁', ← hm₂]
      exact (Category.assoc _ _ _).symm
#align category_theory.limits.left_square_is_pullback CategoryTheory.Limits.leftSquareIsPullback

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the right square is a pushout if the left square and the big square are.
-/
def rightSquareIsPushout (H : IsColimit (PushoutCocone.mk _ _ h₁))
    (H' :
      IsColimit
        (PushoutCocone.mk _ _
          (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
            rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]))) :
    IsColimit (PushoutCocone.mk _ _ h₂) := by
  fapply PushoutCocone.isColimitAux'
  intro s
  have : i₁ ≫ g₁ ≫ s.inl = (f₁ ≫ f₂) ≫ s.inr := by
    rw [Category.assoc, ← s.condition, ← Category.assoc, ← Category.assoc, h₁]
  rcases PushoutCocone.IsColimit.desc' H' (g₁ ≫ s.inl) s.inr this with ⟨l₁, hl₁, hl₁'⟩
  dsimp at *
  use l₁
  refine ⟨?_, ?_, ?_⟩
  · apply PushoutCocone.IsColimit.hom_ext H
    · erw [← Category.assoc, hl₁]
      rfl
    · erw [← Category.assoc, h₂, Category.assoc, hl₁', s.condition]
  · exact hl₁'
  · intro m hm₁ hm₂
    apply PushoutCocone.IsColimit.hom_ext H'
    · erw [hl₁, Category.assoc, hm₁]
    · erw [hm₂, hl₁']
#align category_theory.limits.right_square_is_pushout CategoryTheory.Limits.rightSquareIsPushout

end PasteLemma

section

variable (f : X ⟶ Z) (g : Y ⟶ Z) (f' : W ⟶ X)
variable [HasPullback f g] [HasPullback f' (pullback.fst : pullback f g ⟶ _)]
variable [HasPullback (f' ≫ f) g]

/-- The canonical isomorphism `W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y` -/
noncomputable def pullbackRightPullbackFstIso :
    pullback f' (pullback.fst : pullback f g ⟶ _) ≅ pullback (f' ≫ f) g := by
  let this :=
    bigSquareIsPullback (pullback.snd : pullback f' (pullback.fst : pullback f g ⟶ _) ⟶ _)
      pullback.snd f' f pullback.fst pullback.fst g pullback.condition pullback.condition
      (pullbackIsPullback _ _) (pullbackIsPullback _ _)
  exact (this.conePointUniqueUpToIso (pullbackIsPullback _ _) : _)
#align category_theory.limits.pullback_right_pullback_fst_iso CategoryTheory.Limits.pullbackRightPullbackFstIso

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_hom_fst :
    (pullbackRightPullbackFstIso f g f').hom ≫ pullback.fst = pullback.fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left
#align category_theory.limits.pullback_right_pullback_fst_iso_hom_fst CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_hom_snd :
    (pullbackRightPullbackFstIso f g f').hom ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
#align category_theory.limits.pullback_right_pullback_fst_iso_hom_snd CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_snd

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_inv_fst :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.fst = pullback.fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left
#align category_theory.limits.pullback_right_pullback_fst_iso_inv_fst CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_inv_snd_snd :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd ≫ pullback.snd = pullback.snd :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.right
#align category_theory.limits.pullback_right_pullback_fst_iso_inv_snd_snd CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_snd

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_inv_snd_fst :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ f' := by
  rw [← pullback.condition]
  exact pullbackRightPullbackFstIso_inv_fst_assoc _ _ _ _
#align category_theory.limits.pullback_right_pullback_fst_iso_inv_snd_fst CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_fst

end

section

variable (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)
variable [HasPushout f g] [HasPushout (pushout.inr : _ ⟶ pushout f g) g']
variable [HasPushout f (g ≫ g')]

/-- The canonical isomorphism `(Y ⨿[X] Z) ⨿[Z] W ≅ Y ×[X] W` -/
noncomputable def pushoutLeftPushoutInrIso :
    pushout (pushout.inr : _ ⟶ pushout f g) g' ≅ pushout f (g ≫ g') :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
          (pushoutIsPushout _ _)).coconePointUniqueUpToIso
      (pushoutIsPushout _ _) :
    _)
#align category_theory.limits.pushout_left_pushout_inr_iso CategoryTheory.Limits.pushoutLeftPushoutInrIso

@[reassoc (attr := simp)]
theorem inl_pushoutLeftPushoutInrIso_inv :
    pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').inv = pushout.inl ≫ pushout.inl :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
          (pushoutIsPushout _ _)).comp_coconePointUniqueUpToIso_inv
      (pushoutIsPushout _ _) WalkingSpan.left :
    _)
#align category_theory.limits.inl_pushout_left_pushout_inr_iso_inv CategoryTheory.Limits.inl_pushoutLeftPushoutInrIso_inv

@[reassoc (attr := simp)]
theorem inr_pushoutLeftPushoutInrIso_hom :
    pushout.inr ≫ (pushoutLeftPushoutInrIso f g g').hom = pushout.inr :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
          (pushoutIsPushout _ _)).comp_coconePointUniqueUpToIso_hom
      (pushoutIsPushout _ _) WalkingSpan.right :
    _)
#align category_theory.limits.inr_pushout_left_pushout_inr_iso_hom CategoryTheory.Limits.inr_pushoutLeftPushoutInrIso_hom

@[reassoc (attr := simp)]
theorem inr_pushoutLeftPushoutInrIso_inv :
    pushout.inr ≫ (pushoutLeftPushoutInrIso f g g').inv = pushout.inr := by
  rw [Iso.comp_inv_eq, inr_pushoutLeftPushoutInrIso_hom]
#align category_theory.limits.inr_pushout_left_pushout_inr_iso_inv CategoryTheory.Limits.inr_pushoutLeftPushoutInrIso_inv

@[reassoc (attr := simp)]
theorem inl_inl_pushoutLeftPushoutInrIso_hom :
    pushout.inl ≫ pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').hom = pushout.inl := by
  rw [← Category.assoc, ← Iso.eq_comp_inv, inl_pushoutLeftPushoutInrIso_inv]
#align category_theory.limits.inl_inl_pushout_left_pushout_inr_iso_hom CategoryTheory.Limits.inl_inl_pushoutLeftPushoutInrIso_hom

@[reassoc (attr := simp)]
theorem inr_inl_pushoutLeftPushoutInrIso_hom :
    pushout.inr ≫ pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').hom = g' ≫ pushout.inr := by
  rw [← Category.assoc, ← Iso.eq_comp_inv, Category.assoc, inr_pushoutLeftPushoutInrIso_inv,
    pushout.condition]
#align category_theory.limits.inr_inl_pushout_left_pushout_inr_iso_hom CategoryTheory.Limits.inr_inl_pushoutLeftPushoutInrIso_hom

end

section PullbackAssoc

/-
The objects and morphisms are as follows:

           Z₂ - g₄ -> X₃
           |          |
           g₃         f₄
           ∨          ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
|          |
g₁         f₂
∨          ∨
X₁ - f₁ -> Y₁

where the two squares are pullbacks.

We can then construct the pullback squares

W  - l₂ -> Z₂ - g₄ -> X₃
|                     |
l₁                    f₄
∨                     ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂

and

W' - l₂' -> Z₂
|           |
l₁'         g₃
∨           ∨
Z₁          X₂
|           |
g₁          f₂
∨           ∨
X₁ -  f₁ -> Y₁

We will show that both `W` and `W'` are pullbacks over `g₁, g₂`, and thus we may construct a
canonical isomorphism between them. -/
variable {X₁ X₂ X₃ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₁) (f₃ : X₂ ⟶ Y₂)
variable (f₄ : X₃ ⟶ Y₂) [HasPullback f₁ f₂] [HasPullback f₃ f₄]

local notation "Z₁" => pullback f₁ f₂

local notation "Z₂" => pullback f₃ f₄

local notation "g₁" => (pullback.fst : Z₁ ⟶ X₁)

local notation "g₂" => (pullback.snd : Z₁ ⟶ X₂)

local notation "g₃" => (pullback.fst : Z₂ ⟶ X₂)

local notation "g₄" => (pullback.snd : Z₂ ⟶ X₃)

local notation "W" => pullback (g₂ ≫ f₃) f₄

local notation "W'" => pullback f₁ (g₃ ≫ f₂)

local notation "l₁" => (pullback.fst : W ⟶ Z₁)

local notation "l₂" =>
  (pullback.lift (pullback.fst ≫ g₂) pullback.snd
      (Eq.trans (Category.assoc _ _ _) pullback.condition) :
    W ⟶ Z₂)

local notation "l₁'" =>
  (pullback.lift pullback.fst (pullback.snd ≫ g₃)
      (pullback.condition.trans (Eq.symm (Category.assoc _ _ _))) :
    W' ⟶ Z₁)

local notation "l₂'" => (pullback.snd : W' ⟶ Z₂)

/-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
def pullbackPullbackLeftIsPullback [HasPullback (g₂ ≫ f₃) f₄] : IsLimit (PullbackCone.mk l₁ l₂
    (show l₁ ≫ g₂ = l₂ ≫ g₃ from (pullback.lift_fst _ _ _).symm)) := by
  apply leftSquareIsPullback
  · exact pullbackIsPullback f₃ f₄
  convert pullbackIsPullback (g₂ ≫ f₃) f₄
  rw [pullback.lift_snd]
#align category_theory.limits.pullback_pullback_left_is_pullback CategoryTheory.Limits.pullbackPullbackLeftIsPullback

/-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`. -/
def pullbackAssocIsPullback [HasPullback (g₂ ≫ f₃) f₄] :
    IsLimit
      (PullbackCone.mk (l₁ ≫ g₁) l₂
        (show (l₁ ≫ g₁) ≫ f₁ = l₂ ≫ g₃ ≫ f₂ by
          rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, pullback.condition])) := by
  apply PullbackCone.isLimitOfFlip
  apply bigSquareIsPullback
  · apply PullbackCone.isLimitOfFlip
    exact pullbackIsPullback f₁ f₂
  · apply PullbackCone.isLimitOfFlip
    apply pullbackPullbackLeftIsPullback
  · exact pullback.lift_fst _ _ _
  · exact pullback.condition.symm
#align category_theory.limits.pullback_assoc_is_pullback CategoryTheory.Limits.pullbackAssocIsPullback

theorem hasPullback_assoc [HasPullback (g₂ ≫ f₃) f₄] : HasPullback f₁ (g₃ ≫ f₂) :=
  ⟨⟨⟨_, pullbackAssocIsPullback f₁ f₂ f₃ f₄⟩⟩⟩
#align category_theory.limits.has_pullback_assoc CategoryTheory.Limits.hasPullback_assoc

/-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
def pullbackPullbackRightIsPullback [HasPullback f₁ (g₃ ≫ f₂)] :
    IsLimit (PullbackCone.mk l₁' l₂' (show l₁' ≫ g₂ = l₂' ≫ g₃ from pullback.lift_snd _ _ _)) := by
  apply PullbackCone.isLimitOfFlip
  apply leftSquareIsPullback
  · apply PullbackCone.isLimitOfFlip
    exact pullbackIsPullback f₁ f₂
  · apply PullbackCone.isLimitOfFlip
    exact IsLimit.ofIsoLimit (pullbackIsPullback f₁ (g₃ ≫ f₂))
      (PullbackCone.ext (Iso.refl _) (by simp) (by simp))
  · exact pullback.condition.symm
#align category_theory.limits.pullback_pullback_right_is_pullback CategoryTheory.Limits.pullbackPullbackRightIsPullback

/-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[Y₂] X₃`. -/
def pullbackAssocSymmIsPullback [HasPullback f₁ (g₃ ≫ f₂)] :
    IsLimit
      (PullbackCone.mk l₁' (l₂' ≫ g₄)
        (show l₁' ≫ g₂ ≫ f₃ = (l₂' ≫ g₄) ≫ f₄ by
          rw [pullback.lift_snd_assoc, Category.assoc, Category.assoc, pullback.condition])) := by
  apply bigSquareIsPullback
  · exact pullbackIsPullback f₃ f₄
  · apply pullbackPullbackRightIsPullback
#align category_theory.limits.pullback_assoc_symm_is_pullback CategoryTheory.Limits.pullbackAssocSymmIsPullback

theorem hasPullback_assoc_symm [HasPullback f₁ (g₃ ≫ f₂)] : HasPullback (g₂ ≫ f₃) f₄ :=
  ⟨⟨⟨_, pullbackAssocSymmIsPullback f₁ f₂ f₃ f₄⟩⟩⟩
#align category_theory.limits.has_pullback_assoc_symm CategoryTheory.Limits.hasPullback_assoc_symm

/- Porting note: these don't seem to be propagating change from
-- variable [HasPullback (g₂ ≫ f₃) f₄] [HasPullback f₁ (g₃ ≫ f₂)] -/
variable [HasPullback (g₂ ≫ f₃) f₄] [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)]

/-- The canonical isomorphism `(X₁ ×[Y₁] X₂) ×[Y₂] X₃ ≅ X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`. -/
noncomputable def pullbackAssoc [HasPullback ((pullback.snd : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)] :
    pullback (pullback.snd ≫ f₃ : pullback f₁ f₂ ⟶ _) f₄ ≅
      pullback f₁ (pullback.fst ≫ f₂ : pullback f₃ f₄ ⟶ _) :=
  (pullbackPullbackLeftIsPullback f₁ f₂ f₃ f₄).conePointUniqueUpToIso
    (pullbackPullbackRightIsPullback f₁ f₂ f₃ f₄)
#align category_theory.limits.pullback_assoc CategoryTheory.Limits.pullbackAssoc

@[reassoc (attr := simp)]
theorem pullbackAssoc_inv_fst_fst [HasPullback ((pullback.snd : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.fst = pullback.fst := by
  trans l₁' ≫ pullback.fst
  · rw [← Category.assoc]
    congr 1
    exact IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left
  · exact pullback.lift_fst _ _ _
#align category_theory.limits.pullback_assoc_inv_fst_fst CategoryTheory.Limits.pullbackAssoc_inv_fst_fst

@[reassoc (attr := simp)]
theorem pullbackAssoc_hom_fst [HasPullback ((pullback.snd : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).hom ≫ pullback.fst = pullback.fst ≫ pullback.fst := by
  rw [← Iso.eq_inv_comp, pullbackAssoc_inv_fst_fst]
#align category_theory.limits.pullback_assoc_hom_fst CategoryTheory.Limits.pullbackAssoc_hom_fst

@[reassoc (attr := simp)]
theorem pullbackAssoc_hom_snd_fst [HasPullback ((pullback.snd : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)] : (pullbackAssoc f₁ f₂ f₃ f₄).hom ≫
    pullback.snd ≫ pullback.fst = pullback.fst ≫ pullback.snd := by
  trans l₂ ≫ pullback.fst
  · rw [← Category.assoc]
    congr 1
    exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
  · exact pullback.lift_fst _ _ _
#align category_theory.limits.pullback_assoc_hom_snd_fst CategoryTheory.Limits.pullbackAssoc_hom_snd_fst

@[reassoc (attr := simp)]
theorem pullbackAssoc_hom_snd_snd [HasPullback ((pullback.snd : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd ≫ pullback.snd = pullback.snd := by
  trans l₂ ≫ pullback.snd
  · rw [← Category.assoc]
    congr 1
    exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
  · exact pullback.lift_snd _ _ _
#align category_theory.limits.pullback_assoc_hom_snd_snd CategoryTheory.Limits.pullbackAssoc_hom_snd_snd

@[reassoc (attr := simp)]
theorem pullbackAssoc_inv_fst_snd [HasPullback ((pullback.snd : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.snd =
    pullback.snd ≫ pullback.fst := by rw [Iso.inv_comp_eq, pullbackAssoc_hom_snd_fst]
#align category_theory.limits.pullback_assoc_inv_fst_snd CategoryTheory.Limits.pullbackAssoc_inv_fst_snd

@[reassoc (attr := simp)]
theorem pullbackAssoc_inv_snd [HasPullback ((pullback.snd : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.snd = pullback.snd ≫ pullback.snd := by
  rw [Iso.inv_comp_eq, pullbackAssoc_hom_snd_snd]
#align category_theory.limits.pullback_assoc_inv_snd CategoryTheory.Limits.pullbackAssoc_inv_snd

end PullbackAssoc

section PushoutAssoc

/-
The objects and morphisms are as follows:

           Z₂ - g₄ -> X₃
           |          |
           g₃         f₄
           ∨          ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
|          |
g₁         f₂
∨          ∨
X₁ - f₁ -> Y₁

where the two squares are pushouts.

We can then construct the pushout squares

Z₁ - g₂ -> X₂ - f₃ -> Y₂
|                     |
g₁                    l₂
∨                     ∨
X₁ - f₁ -> Y₁ - l₁ -> W

and

Z₂ - g₄  -> X₃
|           |
g₃          f₄
∨           ∨
X₂          Y₂
|           |
f₂          l₂'
∨           ∨
Y₁ - l₁' -> W'

We will show that both `W` and `W'` are pushouts over `f₂, f₃`, and thus we may construct a
canonical isomorphism between them. -/
variable {X₁ X₂ X₃ Z₁ Z₂ : C} (g₁ : Z₁ ⟶ X₁) (g₂ : Z₁ ⟶ X₂) (g₃ : Z₂ ⟶ X₂)
variable (g₄ : Z₂ ⟶ X₃) [HasPushout g₁ g₂] [HasPushout g₃ g₄]

local notation "Y₁" => pushout g₁ g₂

local notation "Y₂" => pushout g₃ g₄

local notation "f₁" => (pushout.inl : X₁ ⟶ Y₁)

local notation "f₂" => (pushout.inr : X₂ ⟶ Y₁)

local notation "f₃" => (pushout.inl : X₂ ⟶ Y₂)

local notation "f₄" => (pushout.inr : X₃ ⟶ Y₂)

local notation "W" => pushout g₁ (g₂ ≫ f₃)

local notation "W'" => pushout (g₃ ≫ f₂) g₄

local notation "l₁" =>
  (pushout.desc pushout.inl (f₃ ≫ pushout.inr) (pushout.condition.trans (Category.assoc _ _ _)) :
    Y₁ ⟶ W)

local notation "l₂" => (pushout.inr : Y₂ ⟶ W)

local notation "l₁'" => (pushout.inl : Y₁ ⟶ W')

local notation "l₂'" =>
  (pushout.desc (f₂ ≫ pushout.inl) pushout.inr
      (Eq.trans (Eq.symm (Category.assoc _ _ _)) pushout.condition) :
    Y₂ ⟶ W')

/-- `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃` is the pushout `(X₁ ⨿[Z₁] X₂) ×[X₂] (X₂ ⨿[Z₂] X₃)`. -/
def pushoutPushoutLeftIsPushout [HasPushout (g₃ ≫ f₂) g₄] :
    IsColimit
      (PushoutCocone.mk l₁' l₂' (show f₂ ≫ l₁' = f₃ ≫ l₂' from (pushout.inl_desc _ _ _).symm)) := by
  apply PushoutCocone.isColimitOfFlip
  apply rightSquareIsPushout
  · apply PushoutCocone.isColimitOfFlip
    exact pushoutIsPushout g₃ g₄
  · exact IsColimit.ofIsoColimit (PushoutCocone.flipIsColimit (pushoutIsPushout (g₃ ≫ f₂) g₄))
      (PushoutCocone.ext (Iso.refl _) (by simp) (by simp))
  · exact pushout.condition.symm
#align category_theory.limits.pushout_pushout_left_is_pushout CategoryTheory.Limits.pushoutPushoutLeftIsPushout

/-- `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃` is the pushout `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)`. -/
def pushoutAssocIsPushout [HasPushout (g₃ ≫ f₂) g₄] :
    IsColimit
      (PushoutCocone.mk (f₁ ≫ l₁') l₂'
        (show g₁ ≫ f₁ ≫ l₁' = (g₂ ≫ f₃) ≫ l₂' by
          rw [Category.assoc, pushout.inl_desc, pushout.condition_assoc])) := by
  apply bigSquareIsPushout
  · apply pushoutPushoutLeftIsPushout
  · exact pushoutIsPushout _ _
#align category_theory.limits.pushout_assoc_is_pushout CategoryTheory.Limits.pushoutAssocIsPushout

theorem hasPushout_assoc [HasPushout (g₃ ≫ f₂) g₄] : HasPushout g₁ (g₂ ≫ f₃) :=
  ⟨⟨⟨_, pushoutAssocIsPushout g₁ g₂ g₃ g₄⟩⟩⟩
#align category_theory.limits.has_pushout_assoc CategoryTheory.Limits.hasPushout_assoc

/-- `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)` is the pushout `(X₁ ⨿[Z₁] X₂) ×[X₂] (X₂ ⨿[Z₂] X₃)`. -/
def pushoutPushoutRightIsPushout [HasPushout g₁ (g₂ ≫ f₃)] :
    IsColimit (PushoutCocone.mk l₁ l₂ (show f₂ ≫ l₁ = f₃ ≫ l₂ from pushout.inr_desc _ _ _)) := by
  apply rightSquareIsPushout
  · exact pushoutIsPushout _ _
  · convert pushoutIsPushout g₁ (g₂ ≫ f₃)
    rw [pushout.inl_desc]
#align category_theory.limits.pushout_pushout_right_is_pushout CategoryTheory.Limits.pushoutPushoutRightIsPushout

/-- `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)` is the pushout `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃`. -/
def pushoutAssocSymmIsPushout [HasPushout g₁ (g₂ ≫ f₃)] :
    IsColimit
      (PushoutCocone.mk l₁ (f₄ ≫ l₂)
        (show (g₃ ≫ f₂) ≫ l₁ = g₄ ≫ f₄ ≫ l₂ by
          rw [Category.assoc, pushout.inr_desc, pushout.condition_assoc])) := by
  apply PushoutCocone.isColimitOfFlip
  apply bigSquareIsPushout
  · apply PushoutCocone.isColimitOfFlip
    apply pushoutPushoutRightIsPushout
  · apply PushoutCocone.isColimitOfFlip
    exact pushoutIsPushout g₃ g₄
  · exact pushout.condition.symm
  · exact (pushout.inr_desc _ _ _).symm
#align category_theory.limits.pushout_assoc_symm_is_pushout CategoryTheory.Limits.pushoutAssocSymmIsPushout

theorem hasPushout_assoc_symm [HasPushout g₁ (g₂ ≫ f₃)] : HasPushout (g₃ ≫ f₂) g₄ :=
  ⟨⟨⟨_, pushoutAssocSymmIsPushout g₁ g₂ g₃ g₄⟩⟩⟩
#align category_theory.limits.has_pushout_assoc_symm CategoryTheory.Limits.hasPushout_assoc_symm

-- Porting note: these are not propagating so moved into statements
-- variable [HasPushout (g₃ ≫ f₂) g₄] [HasPushout g₁ (g₂ ≫ f₃)]

/-- The canonical isomorphism `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃ ≅ X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)`. -/
noncomputable def pushoutAssoc [HasPushout (g₃ ≫ (pushout.inr : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl : X₂ ⟶ Y₂))] :
    pushout (g₃ ≫ pushout.inr : _ ⟶ pushout g₁ g₂) g₄ ≅
      pushout g₁ (g₂ ≫ pushout.inl : _ ⟶ pushout g₃ g₄) :=
  (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).coconePointUniqueUpToIso
    (pushoutPushoutRightIsPushout g₁ g₂ g₃ g₄)
#align category_theory.limits.pushout_assoc CategoryTheory.Limits.pushoutAssoc

@[reassoc (attr := simp)]
theorem inl_inl_pushoutAssoc_hom [HasPushout (g₃ ≫ (pushout.inr : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl : X₂ ⟶ Y₂))] :
    pushout.inl ≫ pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.inl := by
  trans f₁ ≫ l₁
  · congr 1
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_hom _
        WalkingCospan.left
  · exact pushout.inl_desc _ _ _
#align category_theory.limits.inl_inl_pushout_assoc_hom CategoryTheory.Limits.inl_inl_pushoutAssoc_hom

@[reassoc (attr := simp)]
theorem inr_inl_pushoutAssoc_hom [HasPushout (g₃ ≫ (pushout.inr : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl : X₂ ⟶ Y₂))] :
    pushout.inr ≫ pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.inl ≫ pushout.inr := by
  trans f₂ ≫ l₁
  · congr 1
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_hom _
        WalkingCospan.left
  · exact pushout.inr_desc _ _ _
#align category_theory.limits.inr_inl_pushout_assoc_hom CategoryTheory.Limits.inr_inl_pushoutAssoc_hom

@[reassoc (attr := simp)]
theorem inr_inr_pushoutAssoc_inv [HasPushout (g₃ ≫ (pushout.inr : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl : X₂ ⟶ Y₂))] :
    pushout.inr ≫ pushout.inr ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inr := by
  trans f₄ ≫ l₂'
  · congr 1
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_inv
        (pushoutPushoutRightIsPushout g₁ g₂ g₃ g₄) WalkingCospan.right
  · exact pushout.inr_desc _ _ _
#align category_theory.limits.inr_inr_pushout_assoc_inv CategoryTheory.Limits.inr_inr_pushoutAssoc_inv

@[reassoc (attr := simp)]
theorem inl_pushoutAssoc_inv [HasPushout (g₃ ≫ (pushout.inr : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl : X₂ ⟶ Y₂))] :
    pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inl ≫ pushout.inl := by
  rw [Iso.comp_inv_eq, Category.assoc, inl_inl_pushoutAssoc_hom]
#align category_theory.limits.inl_pushout_assoc_inv CategoryTheory.Limits.inl_pushoutAssoc_inv

@[reassoc (attr := simp)]
theorem inl_inr_pushoutAssoc_inv [HasPushout (g₃ ≫ (pushout.inr : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl : X₂ ⟶ Y₂))] :
    pushout.inl ≫ pushout.inr ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inr ≫ pushout.inl := by
  rw [← Category.assoc, Iso.comp_inv_eq, Category.assoc, inr_inl_pushoutAssoc_hom]
#align category_theory.limits.inl_inr_pushout_assoc_inv CategoryTheory.Limits.inl_inr_pushoutAssoc_inv

@[reassoc (attr := simp)]
theorem inr_pushoutAssoc_hom [HasPushout (g₃ ≫ (pushout.inr : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl : X₂ ⟶ Y₂))] :
    pushout.inr ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.inr ≫ pushout.inr := by
  rw [← Iso.eq_comp_inv, Category.assoc, inr_inr_pushoutAssoc_inv]
#align category_theory.limits.inr_pushout_assoc_hom CategoryTheory.Limits.inr_pushoutAssoc_hom

end PushoutAssoc

end CategoryTheory.Limits
