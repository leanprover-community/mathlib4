/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.CommSq

/-!
# Pseudofunctors from strict bicategory

This file provides an API for pseudofunctors `F` from a strict bicategory `B`. In
particular, this shall apply to pseudofunctors from locally discrete bicategories.

Firstly, we study the compatibilities of the flexible variants `mapId'` and `mapComp'`
of `mapId` and `mapComp` with respect to the composition with identities and the
associativity.

Secondly, given a commutative square `t ≫ r = l ≫ b` in `B`, we construct an
isomorphism `F.map t ≫ F.map r ≅ F.map l ≫ F.map b`
(see `Pseudofunctor.isoMapOfCommSq`).

-/

@[expose] public section

namespace CategoryTheory

universe w₁ w₂ v₁ v₂ u₁ u₂

open Bicategory

namespace Pseudofunctor

variable {B : Type u₁} {C : Type u₂} [Bicategory.{w₁, v₁} B]
  [Strict B] [Bicategory.{w₂, v₂} C] (F : B ⥤ᵖ C)

set_option backward.defeqAttrib.useBackward true in
lemma mapComp'_comp_id {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    F.mapComp' f (𝟙 b₁) f = (ρ_ _).symm ≪≫ whiskerLeftIso _ (F.mapId b₁).symm := by
  ext
  rw [mapComp']
  dsimp
  rw [F.mapComp_id_right_hom f, Strict.rightUnitor_eqToIso, eqToIso.hom,
    ← F.map₂_comp_assoc, eqToHom_trans, eqToHom_refl, PrelaxFunctor.map₂_id,
    Category.id_comp]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
lemma mapComp'_comp_id_hom {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    (F.mapComp' f (𝟙 b₁) f).hom = (ρ_ _).inv ≫ _ ◁ (F.mapId b₁).inv := by
  simp [mapComp'_comp_id]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
lemma mapComp'_comp_id_inv {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    (F.mapComp' f (𝟙 b₁) f).inv = _ ◁ (F.mapId b₁).hom ≫ (ρ_ _).hom := by
  simp [mapComp'_comp_id]

set_option backward.defeqAttrib.useBackward true in
lemma mapComp'_id_comp {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    F.mapComp' (𝟙 b₀) f f = (λ_ _).symm ≪≫ whiskerRightIso (F.mapId b₀).symm _ := by
  ext
  rw [mapComp']
  dsimp
  rw [F.mapComp_id_left_hom f, Strict.leftUnitor_eqToIso, eqToIso.hom,
    ← F.map₂_comp_assoc, eqToHom_trans, eqToHom_refl, PrelaxFunctor.map₂_id,
    Category.id_comp]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
lemma mapComp'_id_comp_hom {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    (F.mapComp' (𝟙 b₀) f f).hom = (λ_ _).inv ≫ (F.mapId b₀).inv ▷ _ := by
  simp [mapComp'_id_comp]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
lemma mapComp'_id_comp_inv {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    (F.mapComp' (𝟙 b₀) f f).inv = (F.mapId b₀).hom ▷ _ ≫ (λ_ _).hom := by
  simp [mapComp'_id_comp]

section associativity

variable {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)
  (f₁₂ : b₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃) (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃) (f : b₀ ⟶ b₃)
  (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃)

set_option backward.defeqAttrib.useBackward true in
@[to_app (attr := reassoc)]
lemma mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom (hf : f₀₁ ≫ f₁₃ = f) :
    (F.mapComp' f₀₁ f₁₃ f).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃).hom =
    (F.mapComp' f₀₂ f₂₃ f).hom ≫
      (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃ ≫ (α_ _ _ _).hom := by
  subst h₀₂ h₁₃ hf
  simp [mapComp_assoc_right_hom, Strict.associator_eqToIso, mapComp']

set_option backward.defeqAttrib.useBackward true in
@[to_app (attr := reassoc)]
lemma mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom (hf : f₀₁ ≫ f₁₃ = f) :
    (F.mapComp' f₀₁ f₁₃ f).inv ≫ (F.mapComp' f₀₂ f₂₃ f).hom =
    F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom ≫
      (α_ _ _ _).inv ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃ := by
  rw [← cancel_epi (F.mapComp' f₀₁ f₁₃ f hf).hom, Iso.hom_inv_id_assoc,
    F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_assoc _ _ _ _ _ _ h₀₂ h₁₃ hf]
  simp

@[to_app (attr := reassoc)]
lemma whiskerLeft_mapComp'_inv_comp_mapComp'₀₁₃_inv (hf : f₀₁ ≫ f₁₃ = f) :
    F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv ≫ (F.mapComp' f₀₁ f₁₃ f hf).inv =
    (α_ _ _ _).inv ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃ ≫
      (F.mapComp' f₀₂ f₂₃ f).inv := by
  simp [← cancel_mono (F.mapComp' f₀₂ f₂₃ f).hom,
    F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom _ _ _ _ _ _ h₀₂ h₁₃ hf]

@[to_app (attr := reassoc)]
lemma mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight (hf : f₀₂ ≫ f₂₃ = f) :
    (F.mapComp' f₀₂ f₂₃ f).hom ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃ =
    (F.mapComp' f₀₁ f₁₃ f).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom ≫
      (α_ _ _ _).inv := by
  rw [F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_assoc _ _ _ _ _ f h₀₂ h₁₃ (by cat_disch)]
  simp

set_option backward.defeqAttrib.useBackward true in
@[to_app (attr := reassoc)]
lemma mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv (hf : f₀₂ ≫ f₂₃ = f) :
    (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃ ≫ (F.mapComp' f₀₂ f₂₃ f).inv =
    (α_ _ _ _).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv ≫
      (F.mapComp' f₀₁ f₁₃ f).inv := by
  rw [whiskerLeft_mapComp'_inv_comp_mapComp'₀₁₃_inv _ _ _ _ _ _ f h₀₂ h₁₃,
    Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
@[to_app (attr := reassoc)]
lemma mapComp'₀₁₃_inv (hf : f₀₁ ≫ f₁₃ = f) :
    (F.mapComp' f₀₁ f₁₃ f).inv =
    F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom ≫ (α_ _ _ _).inv ≫
      (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃ ≫ (F.mapComp' f₀₂ f₂₃ f).inv := by
  simp [← whiskerLeft_mapComp'_inv_comp_mapComp'₀₁₃_inv _ _ _ _ _ _ f h₀₂ h₁₃ hf]

@[to_app (attr := reassoc)]
lemma mapComp'₀₁₃_hom (hf : f₀₁ ≫ f₁₃ = f) :
    (F.mapComp' f₀₁ f₁₃ f).hom =
    (F.mapComp' f₀₂ f₂₃ f).hom ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃ ≫
    (α_ _ _ _).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv := by
  rw [← cancel_epi (F.mapComp' f₀₁ f₁₃ f).inv, Iso.inv_hom_id]
  simp [mapComp'₀₁₃_inv _ _ _ _ _ _ f h₀₂ h₁₃ hf]

set_option backward.defeqAttrib.useBackward true in
@[to_app (attr := reassoc)]
lemma mapComp'₀₂₃_hom (hf : f₀₂ ≫ f₂₃ = f) :
    (F.mapComp' f₀₂ f₂₃ f).hom =
    (F.mapComp' f₀₁ f₁₃ f).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom ≫
      (α_ _ _ _).inv ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃ := by
  simp [← mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_assoc _ _ _ _ _ _ f h₀₂ h₁₃ hf]

@[to_app (attr := reassoc)]
lemma mapComp'₀₂₃_inv (hf : f₀₂ ≫ f₂₃ = f) :
    (F.mapComp' f₀₂ f₂₃ f).inv =
    (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃ ≫ (α_ _ _ _).hom ≫
    F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv ≫ (F.mapComp' f₀₁ f₁₃ f).inv := by
  rw [← cancel_epi (F.mapComp' f₀₂ f₂₃ f).hom, Iso.hom_inv_id]
  simp [mapComp'₀₂₃_hom _ _ _ _ _ _ f h₀₂ h₁₃ hf]

set_option backward.defeqAttrib.useBackward true in
@[to_app (attr := reassoc)]
lemma mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom (hf : f₀₂ ≫ f₂₃ = f) :
    (F.mapComp' f₀₂ f₂₃ f).inv ≫ (F.mapComp' f₀₁ f₁₃ f).hom =
      (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃ ≫ (α_ _ _ _).hom ≫
      F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv := by
  simp [mapComp'₀₂₃_inv _ _ _ _ _ _ _ h₀₂ h₁₃ hf]

end associativity

section CommSq

variable {X₁ X₂ Y₁ Y₂ : B}

section

variable {t : X₁ ⟶ Y₁} {l : X₁ ⟶ X₂} {r : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂} (sq : CommSq t l r b)

/-- Given a commutative square `CommSq t l r b` in a strict bicategory `B` and
a pseudofunctor from `B`, this is the isomorphism
`F.map t ≫ F.map r ≅ F.map l ≫ F.map b`. -/
def isoMapOfCommSq : F.map t ≫ F.map r ≅ F.map l ≫ F.map b :=
  (F.mapComp t r).symm ≪≫ F.mapComp' _ _ _ (by rw [sq.w])

lemma isoMapOfCommSq_eq (φ : X₁ ⟶ Y₂) (hφ : t ≫ r = φ) :
    F.isoMapOfCommSq sq = (F.mapComp' t r φ (by rw [hφ])).symm ≪≫
      F.mapComp' l b φ (by rw [← hφ, sq.w]) := by
  subst hφ
  simp [isoMapOfCommSq, mapComp'_eq_mapComp]

end

/-- Equational lemma for `Pseudofunctor.isoMapOfCommSq` when
both vertical maps of the square are the same and horizontal maps are identities. -/
lemma isoMapOfCommSq_horiz_id (f : X₁ ⟶ X₂) :
    F.isoMapOfCommSq (t := 𝟙 _) (l := f) (r := f) (b := 𝟙 _) ⟨by simp⟩ =
      whiskerRightIso (F.mapId X₁) (F.map f) ≪≫ λ_ _ ≪≫ (ρ_ _).symm ≪≫
        (whiskerLeftIso (F.map f) (F.mapId X₂)).symm := by
  ext
  rw [isoMapOfCommSq_eq _ _ f (by simp), mapComp'_comp_id, mapComp'_id_comp]
  simp

/-- Equational lemma for `Pseudofunctor.isoMapOfCommSq` when
both horizontal maps of the square are the same and vertical maps are identities. -/
lemma isoMapOfCommSq_vert_id (f : X₁ ⟶ X₂) :
    F.isoMapOfCommSq (t := f) (l := 𝟙 _) (r := 𝟙 _) (b := f) ⟨by simp⟩ =
      whiskerLeftIso (F.map f) (F.mapId X₂) ≪≫ ρ_ _ ≪≫ (λ_ _).symm ≪≫
        (whiskerRightIso (F.mapId X₁) (F.map f)).symm := by
  ext
  rw [isoMapOfCommSq_eq _ _ f (by simp), mapComp'_comp_id, mapComp'_id_comp]
  simp

end CommSq

end Pseudofunctor

namespace LaxFunctor

variable {B : Type u₁} {C : Type u₂} [Bicategory.{w₁, v₁} B]
  [Strict B] [Bicategory.{w₂, v₂} C] (F : B ⥤ᴸ C)

section associativity

variable {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)
  (f₁₂ : b₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃) (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃) (f : b₀ ⟶ b₃)
  (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃)

@[reassoc]
lemma whiskerLeft_mapComp'_comp_mapComp' (hf : f₀₁ ≫ f₁₃ = f) :
    F.map f₀₁ ◁ F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃ ≫ F.mapComp' f₀₁ f₁₃ f hf =
    (α_ _ _ _).inv ≫ F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂ ▷ F.map f₂₃ ≫
      F.mapComp' f₀₂ f₂₃ f := by
  subst hf h₀₂ h₁₃
  have := F.map₂_associator f₀₁ f₁₂ f₂₃
  simp only [Strict.associator_eqToIso, eqToIso.hom] at this
  simp [LaxFunctor.mapComp', this]

@[reassoc]
lemma mapComp'_whiskerRight_comp_mapComp' (hf : f₀₂ ≫ f₂₃ = f) :
    F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂ ▷ F.map f₂₃ ≫ F.mapComp' f₀₂ f₂₃ f =
    (α_ _ _ _).hom ≫ F.map f₀₁ ◁ F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃ ≫
      F.mapComp' f₀₁ f₁₃ f := by
  rw [whiskerLeft_mapComp'_comp_mapComp' _ _ _ _ _ _ f h₀₂ h₁₃,
    Iso.hom_inv_id_assoc]

end associativity

end LaxFunctor

namespace OplaxFunctor

variable {B : Type u₁} {C : Type u₂} [Bicategory.{w₁, v₁} B]
  [Strict B] [Bicategory.{w₂, v₂} C] (F : B ⥤ᵒᵖᴸ C)

section associativity

variable {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)
  (f₁₂ : b₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃) (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃) (f : b₀ ⟶ b₃)
  (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃)

@[reassoc]
lemma mapComp'_comp_whiskerLeft_mapComp' (hf : f₀₁ ≫ f₁₃ = f) :
    F.mapComp' f₀₁ f₁₃ f ≫ F.map f₀₁ ◁ F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃ =
    F.mapComp' f₀₂ f₂₃ f ≫
      F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂ ▷ F.map f₂₃ ≫ (α_ _ _ _).hom := by
  subst h₀₂ h₁₃ hf
  have := F.map₂_associator f₀₁ f₁₂ f₂₃
  simp only [Strict.associator_eqToIso, eqToIso.hom] at this
  simp [OplaxFunctor.mapComp', ← this, PrelaxFunctor.map₂_eqToHom]


@[reassoc]
lemma mapComp'_comp_mapComp'_whiskerRight (hf : f₀₂ ≫ f₂₃ = f) :
    F.mapComp' f₀₂ f₂₃ f ≫ F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂ ▷ F.map f₂₃ =
    F.mapComp' f₀₁ f₁₃ f ≫ F.map f₀₁ ◁ F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃ ≫
      (α_ _ _ _).inv := by
  rw [F.mapComp'_comp_whiskerLeft_mapComp'_assoc _ _ _ _ _ f h₀₂ h₁₃ (by cat_disch)]
  simp

end associativity

end OplaxFunctor

end CategoryTheory
