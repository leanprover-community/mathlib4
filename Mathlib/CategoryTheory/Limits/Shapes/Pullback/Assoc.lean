/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

#align_import category_theory.limits.shapes.pullbacks from "leanprover-community/mathlib"@"7316286ff2942aa14e540add9058c6b0aa1c8070"

/-!
# Associativity of pullbacks

This file shows that pullbacks (and pushouts) are associative up to natural isomorphism.

-/

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

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
