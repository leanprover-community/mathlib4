/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Pullbacks and pushouts in a monoidal category

For numerous simp lemmas of the form `f ≫ g = h`, we add accompanying simp lemmas of the form
`Q ◁ f ≫ Q ◁ g = Q ◁ h` and `f ▷ Q ≫ g ▷ Q = h ▷ Q`. This file and
`Mathlib.CategoryTheory.Monoidal.Limits.HasLimits` are needed to define a monoidal category
structure in `Mathlib.CategoryTheory.Monoidal.Arrow`.

Additionally, certain isomorphisms of pushouts and pullbacks involving terminal/initial objects are
defined.

## TODO
An attribute should be developed to automatically generate lemmas of this form.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MonoidalCategory

open Limits MonoidalCategory

variable {C : Type u} [Category.{v} C]

namespace IsPushout

variable [MonoidalCategory C] {Z X Y P W : C} {f : Z ⟶ X} {g : Z ⟶ Y}
    {inl : X ⟶ P} {inr : Y ⟶ P} (hP : IsPushout f g inl inr)
    {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k)

@[reassoc (attr := simp)]
lemma whiskerLeft_inl_desc {Q : C} :
    Q ◁ inl ≫ Q ◁ hP.desc h k w = Q ◁ h := by
  rw [← MonoidalCategory.whiskerLeft_comp, IsPushout.inl_desc]

@[reassoc (attr := simp)]
lemma whiskerLeft_inr_desc {Q : C} :
    Q ◁ inr ≫ Q ◁ hP.desc h k w = Q ◁ k := by
  rw [← MonoidalCategory.whiskerLeft_comp, IsPushout.inr_desc]

@[reassoc (attr := simp)]
lemma inl_desc_whiskerRight {Q : C} :
    inl ▷ Q ≫ hP.desc h k w ▷ Q = h ▷ Q := by
  rw [← comp_whiskerRight, IsPushout.inl_desc]

@[reassoc (attr := simp)]
lemma inr_desc_whiskerRight {Q : C} :
    inr ▷ Q ≫ hP.desc h k w ▷ Q = k ▷ Q := by
  rw [← comp_whiskerRight, IsPushout.inr_desc]

@[reassoc]
lemma whiskerLeft_w (hP : IsPushout f g inl inr) {Q : C} :
    Q ◁ f ≫ Q ◁ inl = Q ◁ g ≫ Q ◁ inr := by
  simp [← MonoidalCategory.whiskerLeft_comp, hP.w]

@[reassoc]
lemma w_whiskerRight (hP : IsPushout f g inl inr) {Q : C} :
    f ▷ Q ≫ inl ▷ Q = g ▷ Q ≫ inr ▷ Q := by
  simp [← MonoidalCategory.comp_whiskerRight, hP.w]

@[reassoc (attr := simp)]
lemma whiskerLeft_inl_isoPushout_inv [HasPushout f g] {Q : C} :
    Q ◁ pushout.inl _ _ ≫ Q ◁ hP.isoPushout.inv = Q ◁ inl := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
lemma whiskerLeft_inr_isoPushout_inv [HasPushout f g] {Q : C} :
    Q ◁ pushout.inr _ _ ≫ Q ◁ hP.isoPushout.inv = Q ◁ inr := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
lemma whiskerLeft_inl_isoPushout_hom [HasPushout f g] {Q : C} :
    Q ◁ inl ≫ Q ◁ hP.isoPushout.hom = Q ◁ pushout.inl _ _ := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
lemma whiskerLeft_inr_isoPushout_hom [HasPushout f g] {Q : C} :
    Q ◁ inr ≫ Q ◁ hP.isoPushout.hom = Q ◁ pushout.inr _ _ := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
lemma inl_isoPushout_inv_whiskerRight [HasPushout f g] {Q : C} :
    pushout.inl _ _ ▷ Q ≫ hP.isoPushout.inv ▷ Q = inl ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
lemma inr_isoPushout_inv_whiskerRight [HasPushout f g] {Q : C} :
    pushout.inr _ _ ▷ Q ≫ hP.isoPushout.inv ▷ Q = inr ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
lemma inl_isoPushout_hom_whiskerRight [HasPushout f g] {Q : C} :
    inl ▷ Q ≫ hP.isoPushout.hom ▷ Q = pushout.inl _ _ ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
lemma inr_isoPushout_hom_whiskerRight [HasPushout f g] {Q : C} :
    inr ▷ Q ≫ hP.isoPushout.hom ▷ Q = pushout.inr _ _ ▷ Q := by
  simp [← comp_whiskerRight]

end IsPushout

section Pushout

variable [MonoidalCategory C] [HasPushouts C]
  {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
  (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) {Q : C}

@[reassoc]
lemma Limits.pushout.whiskerLeft_condition :
    Q ◁ f ≫ Q ◁ pushout.inl f g = Q ◁ g ≫ Q ◁ pushout.inr f g := by
  simp [← MonoidalCategory.whiskerLeft_comp, pushout.condition]

@[reassoc]
lemma Limits.pushout.condition_whiskerRight :
    f ▷ Q ≫ pushout.inl f g ▷ Q = g ▷ Q ≫ pushout.inr f g ▷ Q := by
  simp [← comp_whiskerRight, pushout.condition]

variable {A B X Y Z W : C} {f : A ⟶ B} {g : X ⟶ Y}

@[reassoc]
lemma Limits.pushout.associator_naturality_left_condition {h : Z ⊗ W ⟶ X} :
    f ▷ Z ▷ W ≫ (α_ B Z W).hom ≫ B ◁ h ≫ pushout.inl (f ▷ X) (A ◁ g) =
      (α_ A Z W).hom ≫ A ◁ (h ≫ g) ≫ pushout.inr (f ▷ X) (A ◁ g) := by
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, pushout.condition,
    ← MonoidalCategory.whiskerLeft_comp_assoc]

@[reassoc]
lemma Limits.pushout.associator_inv_naturality_right_condition {h : Z ⊗ W ⟶ A} :
    Z ◁ W ◁ g ≫ (α_ Z W Y).inv ≫ h ▷ Y ≫ pushout.inr (f ▷ X) (A ◁ g) =
      (α_ Z W X).inv ≫ (h ≫ f) ▷ X ≫ pushout.inl (f ▷ X) (A ◁ g) := by
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ← pushout.condition,
    ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
lemma Limits.whiskerLeft_inl_comp_pushoutSymmetry_hom (f : X ⟶ Y) (g : X ⟶ Z) :
    Q ◁ pushout.inl f g ≫ Q ◁ (pushoutSymmetry f g).hom = Q ◁ pushout.inr g f := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
lemma Limits.whiskerLeft_inr_comp_pushoutSymmetry_hom (f : X ⟶ Y) (g : X ⟶ Z) :
    Q ◁ pushout.inr f g ≫ Q ◁ (pushoutSymmetry f g).hom = Q ◁ pushout.inl g f := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
lemma Limits.inl_comp_pushoutSymmetry_hom_whiskerRight (f : X ⟶ Y) (g : X ⟶ Z) :
    pushout.inl f g ▷ Q ≫ (pushoutSymmetry f g).hom ▷ Q = pushout.inr g f ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
lemma Limits.inr_comp_pushoutSymmetry_hom_whiskerRight (f : X ⟶ Y) (g : X ⟶ Z) :
    pushout.inr f g ▷ Q ≫ (pushoutSymmetry f g).hom ▷ Q = pushout.inl g f ▷ Q := by
  simp [← comp_whiskerRight]

end Pushout

noncomputable section

open MonoidalClosed

variable [HasPushouts C] [CartesianMonoidalCategory C] [MonoidalClosed C]

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `pushout (f ▷ I) (A ◁ (∅ ⟶ W)) ≅ A ⊗ W` in a CCC with pushouts and an
initial object. -/
@[simps]
def Limits.pushout.isInitialWhiskerLeftIso
    {A B : C} (f : A ⟶ B) {I : C} (i : IsInitial I) {W : C} :
    pushout (f ▷ I) (A ◁ i.to W) ≅ A ⊗ W where
  hom := pushout.desc ((i.ofIso (zeroMul i).symm).to _) (𝟙 _)
    ((i.ofIso (zeroMul i).symm).hom_ext _ _)
  inv := pushout.inr _ _
  hom_inv_id := pushout.hom_ext ((i.ofIso (zeroMul i).symm).hom_ext _ _) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `pushout  ((∅ ⟶ W) ▷ A) (I ◁ f) ≅ W ⊗ A` in a braided CCC with pushouts and
an initial object. -/
@[simps]
def Limits.pushout.isInitialWhiskerRightIso [BraidedCategory C]
    {A B : C} (f : A ⟶ B) {I : C} (i : IsInitial I) {W : C} :
    pushout (i.to W ▷ A) (I ◁ f) ≅ W ⊗ A where
  hom := pushout.desc (𝟙 _) ((i.ofIso (mulZero i).symm).to _)
    ((i.ofIso (mulZero i).symm).hom_ext _ _)
  inv := pushout.inl _ _
  hom_inv_id := pushout.hom_ext (by simp) ((i.ofIso (mulZero i).symm).hom_ext _ _)

end

noncomputable section

variable [HasPullbacks C]

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `pullback (A ⟹ W ⟶ A ⟹ ⋆) (B ⟹ ⋆ ⟶ A ⟹ ⋆) ≅ A ⟹ W` in a monoidal closed
category with pullbacks and a terminal object. -/
@[simps]
def Limits.pullback.ihomMapIsTerminalIso
    [MonoidalCategory C] [MonoidalClosed C]
    {A B : C} (f : A ⟶ B) {T : C} (t : IsTerminal T) {W : C} :
    pullback ((ihom A).map (t.from W)) ((MonoidalClosed.pre f).app T) ≅ (ihom A).obj W where
  hom := pullback.fst _ _
  inv := pullback.lift (𝟙 _) (MonoidalClosed.curry (t.from _)) (by
      rw [MonoidalClosed.curry_pre_app, MonoidalClosed.eq_curry_iff]
      exact t.hom_ext _ _)
  hom_inv_id :=
    have : (ihom B).IsRightAdjoint := Closed.adj.isRightAdjoint
    pullback.hom_ext (by simp) ((IsTerminal.isTerminalObj (ihom B) T t).hom_ext _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `pullback (∅ ⟹ A ⟶ ∅ ⟹ B) (W ⟹ B ⟶ ∅ ⟹ B) ≅ W ⟹ B` in a braided CCC
with pullbacks and an initial object. -/
@[simps]
def Limits.pullback.preAppIsInitialIso
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B : C} (f : A ⟶ B) {I : C} (i : IsInitial I) {W : C} :
    pullback ((ihom I).map f) ((MonoidalClosed.pre (i.to W)).app B) ≅ (ihom W).obj B where
  hom := pullback.snd _ _
  inv := pullback.lift (MonoidalClosed.curry ((i.ofIso (mulZero i).symm).to _)) (𝟙 _) (by
      rw [← MonoidalClosed.curry_natural_right, MonoidalClosed.curry_eq_iff]
      exact (i.ofIso (mulZero i).symm).hom_ext _ _)
  hom_inv_id := pullback.hom_ext (by
    simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
      ← MonoidalClosed.curry_natural_left, MonoidalClosed.curry_eq_iff]
    exact (i.ofIso (mulZero i).symm).hom_ext _ _) (by simp)

end

end CategoryTheory.MonoidalCategory
