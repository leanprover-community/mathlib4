/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.CommSq

/-!
# Pseudofunctors from strict bicategory

This file provides an API for pseudofunctors `F` from a strict bicategory `B`. In
particular, this shall apply to pseudofunctors from locally discrete bicategories.

We first introduce more flexible variants of `mapId` and `mapComp`: for example,
if `f` and `g` are composable morphisms and `fg` is such that `h : fg = f ≫ f`,
we provide an isomorphism `F.mapComp' f g fg h : F.map fg ≅ F.map f ≫ F.map g`.
We study the compatibilities of these isomorphisms with respect to composition
with identities and associativity.

Secondly, given a commutative square `t ≫ r = l ≫ b` in `B`, we construct an
isomorphism `F.map t ≫ F.map r ≅ F.map l ≫ F.map b`
(see `Pseudofunctor.isoMapOfCommSq`).

-/

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {B C : Type*} [Bicategory B] [Bicategory C] (F : Pseudofunctor B C)

/-- More flexible variant of `mapId`. -/
def mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by aesop_cat) :
    F.map f ≅ 𝟙 _ :=
  F.map₂Iso (eqToIso (by rw [hf])) ≪≫ F.mapId _

lemma mapId'_eq_mapId (b : B) :
    F.mapId' (𝟙 b) rfl = F.mapId b := by
  simp [mapId']

/-- More flexible variant of `mapComp`. -/
def mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg := by aesop_cat) :
    F.map fg ≅ F.map f ≫ F.map g :=
  F.map₂Iso (eqToIso (by rw [h])) ≪≫ F.mapComp f g

lemma mapComp'_eq_mapComp {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    F.mapComp' f g _ rfl = F.mapComp f g := by
  simp [mapComp']

variable [Strict B]

lemma mapComp'_comp_id {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    F.mapComp' f (𝟙 b₁) f = (ρ_ _).symm ≪≫ whiskerLeftIso _ (F.mapId b₁).symm := by
  ext
  dsimp [mapComp']
  rw [F.mapComp_id_right_hom f, Strict.rightUnitor_eqToIso, eqToIso.hom,
    ← F.map₂_comp_assoc, eqToHom_trans, eqToHom_refl, PrelaxFunctor.map₂_id,
    Category.id_comp]

lemma mapComp'_id_comp {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    F.mapComp' (𝟙 b₀) f f = (λ_ _).symm ≪≫ whiskerRightIso (F.mapId b₀).symm _ := by
  ext
  dsimp [mapComp']
  rw [F.mapComp_id_left_hom f, Strict.leftUnitor_eqToIso, eqToIso.hom,
    ← F.map₂_comp_assoc, eqToHom_trans, eqToHom_refl, PrelaxFunctor.map₂_id,
    Category.id_comp]

section associativity

variable {b₀ b₁ b₂ b₃ : B} (f₀₁ : b₀ ⟶ b₁)
  (f₁₂ : b₁ ⟶ b₂) (f₂₃ : b₂ ⟶ b₃) (f₀₂ : b₀ ⟶ b₂) (f₁₃ : b₁ ⟶ b₃) (f : b₀ ⟶ b₃)
  (h₀₂ : f₀₁ ≫ f₁₂ = f₀₂) (h₁₃ : f₁₂ ≫ f₂₃ = f₁₃)

@[reassoc]
lemma mapComp'_hom_comp_whiskerLeft_mapComp'_hom (hf : f₀₁ ≫ f₁₃ = f) :
    (F.mapComp' f₀₁ f₁₃ f).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom =
    (F.mapComp' f₀₂ f₂₃ f).hom ≫
      (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃ ≫ (α_ _ _ _).hom := by
  subst h₀₂ h₁₃ hf
  simp [mapComp_assoc_right_hom, Strict.associator_eqToIso, mapComp']

@[reassoc]
lemma mapComp'_inv_comp_mapComp'_hom (hf : f₀₁ ≫ f₁₃ = f) :
    (F.mapComp' f₀₁ f₁₃ f).inv ≫
      (F.mapComp' f₀₂ f₂₃ f).hom =
    F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom ≫
      (α_ _ _ _).inv ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃ := by
  rw [← cancel_epi (F.mapComp' f₀₁ f₁₃ f hf).hom, Iso.hom_inv_id_assoc,
    F.mapComp'_hom_comp_whiskerLeft_mapComp'_hom_assoc _ _ _ _ _ _ h₀₂ h₁₃ hf]
  simp

@[reassoc]
lemma whiskerLeft_mapComp'_inv_comp_mapComp'_inv (hf : f₀₁ ≫ f₁₃ = f) :
    F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv ≫ (F.mapComp' f₀₁ f₁₃ f hf).inv =
    (α_ _ _ _).inv ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃ ≫
      (F.mapComp' f₀₂ f₂₃ f).inv := by
  simp [← cancel_mono (F.mapComp' f₀₂ f₂₃ f).hom,
    F.mapComp'_inv_comp_mapComp'_hom _ _ _ _ _ _ h₀₂ h₁₃ hf]

@[reassoc]
lemma mapComp'_hom_comp_mapComp'_hom_whiskerRight (hf : f₀₂ ≫ f₂₃ = f) :
    (F.mapComp' f₀₂ f₂₃ f).hom ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃ =
    (F.mapComp' f₀₁ f₁₃ f).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom ≫
      (α_ _ _ _).inv := by
  rw [F.mapComp'_hom_comp_whiskerLeft_mapComp'_hom_assoc _ _ _ _ _ f h₀₂ h₁₃ (by aesop_cat)]
  simp

@[reassoc]
lemma mapComp'_inv_comp_mapComp'_hom' (hf : f₀₂ ≫ f₂₃ = f) :
    (F.mapComp' f₀₁ f₁₃ f).inv ≫ (F.mapComp' f₀₂ f₂₃ f).hom =
     F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).hom ≫
      (α_ _ _ _).inv ≫ (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃:= by
  simp only [← cancel_mono ((F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).hom ▷ F.map f₂₃),
    mapComp'_hom_comp_mapComp'_hom_whiskerRight _ _ _ _ _ _ _ h₀₂ h₁₃ hf,
    Category.assoc, Iso.inv_hom_id_assoc, inv_hom_whiskerRight, Category.comp_id]

@[reassoc]
lemma mapComp'_inv_whiskerRight_comp_mapComp'_inv (hf : f₀₂ ≫ f₂₃ = f) :
    (F.mapComp' f₀₁ f₁₂ f₀₂ h₀₂).inv ▷ F.map f₂₃ ≫ (F.mapComp' f₀₂ f₂₃ f).inv =
    (α_ _ _ _).hom ≫ F.map f₀₁ ◁ (F.mapComp' f₁₂ f₂₃ f₁₃ h₁₃).inv ≫
      (F.mapComp' f₀₁ f₁₃ f).inv := by
  rw [whiskerLeft_mapComp'_inv_comp_mapComp'_inv _ _ _ _ _ _ f h₀₂ h₁₃,
    Iso.hom_inv_id_assoc]

end associativity

section CommSq

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₁ Z₂ : B}

section

variable {t : X₁ ⟶ Y₁} {l : X₁ ⟶ X₂} {r : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂} (sq : CommSq t l r b)

/-- Given a commutative square `CommSq t l r b` in a strict bicategory `B` and
a pseudofunctor from `B`, this is the natural isomorphism
`F.map t ≫ F.map r ≅ F.map l ≫ F.map b`. -/
def isoMapOfCommSq : F.map t ≫ F.map r ≅ F.map l ≫ F.map b :=
  (F.mapComp t r).symm ≪≫ F.mapComp' _ _ _ (by rw [sq.w])

lemma isoMapOfCommSq_eq (φ : X₁ ⟶ Y₂) (hφ : t ≫ r = φ) :
    F.isoMapOfCommSq sq =
    (F.mapComp' t r φ (by rw [hφ])).symm ≪≫
      F.mapComp' l b φ (by rw [← hφ, sq.w]) := by
  subst hφ
  simp [isoMapOfCommSq, mapComp'_eq_mapComp]

lemma isoMapOfCommSq_flip : F.isoMapOfCommSq sq.flip =
    (F.isoMapOfCommSq sq).symm := by
  rw [F.isoMapOfCommSq_eq sq.flip (t ≫ r) sq.w.symm,
    F.isoMapOfCommSq_eq sq (t ≫ r) rfl,
    Iso.trans_symm, Iso.symm_symm_eq]

end

/-- Equational lemma for `Pseudofunctor.isoMapOfCommSq` when
both vertical maps of the square are the same and horizontal maps are identities. -/
lemma isoMapOfCommSq_horiz_id (f : X₁ ⟶ X₂) :
    F.isoMapOfCommSq (t := 𝟙 _) (l := f) (r := f) (b := 𝟙 _) ⟨by simp⟩ =
      whiskerRightIso (F.mapId X₁) (F.map f) ≪≫ λ_ _  ≪≫ (ρ_ _).symm ≪≫
        (whiskerLeftIso (F.map f) (F.mapId X₂)).symm := by
  ext
  rw [isoMapOfCommSq_eq _ _ f (by simp), mapComp'_comp_id, mapComp'_id_comp]
  simp

/-- Equational lemma for `Pseudofunctor.isoMapOfCommSq` when
both horizontal maps of the square are the same and vertical maps are identities. -/
lemma isoMapOfCommSq_vert_id (f : X₁ ⟶ X₂) :
    F.isoMapOfCommSq (t := f)  (l := 𝟙 _) (r := 𝟙 _) (b := f) ⟨by simp⟩ =
      whiskerLeftIso (F.map f) (F.mapId X₂) ≪≫ ρ_ _ ≪≫ (λ_ _).symm ≪≫
        (whiskerRightIso (F.mapId X₁) (F.map f)).symm := by
  ext
  rw [isoMapOfCommSq_eq _ _ f (by simp), mapComp'_comp_id, mapComp'_id_comp]
  simp

lemma isoMapOfCommSq_horiz_comp
    {t : X₁ ⟶ Y₁} {t' : Y₁ ⟶ Z₁} {l : X₁ ⟶ X₂} {m : Y₁ ⟶ Y₂} {r : Z₁ ⟶ Z₂}
    {b : X₂ ⟶ Y₂} {b' : Y₂ ⟶ Z₂} (sq : CommSq t l m b) (sq' : CommSq t' m r b')
    {t'' : X₁ ⟶ Z₁} {b'' : X₂ ⟶ Z₂} (ht : t ≫ t' = t'') (hb : b ≫ b' = b'') :
    F.isoMapOfCommSq (sq.horiz_comp' sq' ht hb) =
      whiskerRightIso (F.mapComp' t t' t'' (by rw [← ht])) (F.map r) ≪≫
      α_ _ _ _ ≪≫ whiskerLeftIso (F.map t) (F.isoMapOfCommSq sq') ≪≫
      (α_ _ _ _).symm ≪≫ whiskerRightIso (F.isoMapOfCommSq sq) (F.map b') ≪≫
      α_ _ _ _ ≪≫ whiskerLeftIso (F.map l)
        ((F.mapComp' b b' b'' (by rw [← hb])).symm) := by
  ext
  have w : t'' ≫ r = t ≫ t' ≫ r := by rw [reassoc_of% ht]
  rw [F.isoMapOfCommSq_eq ((sq.horiz_comp' sq' ht hb)) (t ≫ t' ≫ r) w,
    F.isoMapOfCommSq_eq sq' (t' ≫ r) rfl, F.isoMapOfCommSq_eq sq (t ≫ m) rfl]
  dsimp
  simp only [Bicategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  rw [← F.mapComp'_inv_comp_mapComp'_hom_assoc t _ _ _ (t' ≫ r) _ _ _ rfl,
    F.mapComp'_hom_comp_mapComp'_hom_whiskerRight_assoc _ _ _ _ _ _ _ hb
    (by rw [Category.assoc, ← sq'.w]),
    Iso.inv_hom_id_assoc, whiskerLeft_hom_inv, Category.comp_id,
    ← cancel_epi (F.mapComp' t'' r (t ≫ t' ≫ r) w).hom,
    F.mapComp'_hom_comp_mapComp'_hom_whiskerRight_assoc _ _ _ _ _ _ ht rfl w,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    whiskerLeft_hom_inv_assoc, Iso.hom_inv_id_assoc]

lemma isoMapOfCommSq_vert_comp
    {t : X₁ ⟶ Y₁} {m : X₂ ⟶ Y₂} {b : X₃ ⟶ Y₃}
    {l : X₁ ⟶ X₂} {l' : X₂ ⟶ X₃} {r : Y₁ ⟶ Y₂} {r' : Y₂ ⟶ Y₃}
    (sq : CommSq t l r m) (sq' : CommSq m l' r' b)
    {l'' : X₁ ⟶ X₃} {r'' : Y₁ ⟶ Y₃} (hl : l ≫ l' = l'') (hr : r ≫ r' = r'') :
    F.isoMapOfCommSq (sq.vert_comp' sq' hl hr) =
      whiskerLeftIso (F.map t) (F.mapComp' r r' r'' hr) ≪≫
        (α_ _ _ _).symm ≪≫ whiskerRightIso (F.isoMapOfCommSq sq) (F.map r') ≪≫
        α_ _ _ _ ≪≫ whiskerLeftIso (F.map l) (F.isoMapOfCommSq sq') ≪≫
        (α_ _ _ _).symm ≪≫ whiskerRightIso (F.mapComp' l l' l'' hl).symm (F.map b) := by
  rw [← Iso.symm_eq_iff, ← isoMapOfCommSq_flip,
    F.isoMapOfCommSq_horiz_comp sq.flip sq'.flip hl hr,
    F.isoMapOfCommSq_flip sq', F.isoMapOfCommSq_flip sq]
  ext
  dsimp
  simp only [Category.assoc]

end CommSq

end Pseudofunctor

end CategoryTheory
