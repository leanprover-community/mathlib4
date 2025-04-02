/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Sums.Basic
import Mathlib.CategoryTheory.Products.Basic

/-!
# Functors out of sums of categories.

This file records the universal property of sums of categories as an equivalence of
categories `Sum.functorEquiv : A ⊕ A' ⥤ B ≌ (A ⥤ B) × (A' ⥤ B)`, and characterizes its
precompositions with the left and right inclusion as corresponding to the projections on
the product side.

-/

namespace CategoryTheory

universe v u

variable (A : Type*) [Category A] (A' : Type*) [Category A']
  (B : Type u) [Category.{v} B]

namespace Sum

/-- The equivalence between functors from a sum and the product of the
 functor categories. -/
@[simps]
def functorEquiv : A ⊕ A' ⥤ B ≌ (A ⥤ B) × (A' ⥤ B) where
  functor :=
    { obj F := ⟨inl_ A A' ⋙ F, inr_ A A' ⋙ F⟩
      map η := ⟨whiskerLeft (inl_ A A') η, whiskerLeft (inr_ A A') η⟩ }
  inverse :=
    { obj F := Functor.sum' F.1 F.2
      map η := NatTrans.sum' η.1 η.2 }
  unitIso := NatIso.ofComponents <| fun F ↦ F.isoSum
  counitIso := NatIso.ofComponents <| fun F ↦
    (Functor.inlCompSum' _ _).prod (Functor.inrCompSum' _ _) ≪≫ prod.etaIso F

variable {A A' B}

@[simp]
lemma functorEquiv_unit_app_app_inl (X : A ⊕ A' ⥤ B) (a : A) :
    ((functorEquiv A A' B).unit.app X).app (.inl a) = 𝟙 (X.obj (.inl a)) :=
  rfl

@[simp]
lemma functorEquiv_unit_app_app_inr (X : A ⊕ A' ⥤ B) (a' : A') :
    ((functorEquiv A A' B).unit.app X).app (.inr a') = 𝟙 (X.obj (.inr a')) :=
  rfl

@[simp]
lemma functorEquiv_unitIso_inv_app_app_inl (X : A ⊕ A' ⥤ B) (a : A) :
    ((functorEquiv A A' B).unitIso.inv.app X).app (.inl a) = 𝟙 (X.obj (.inl a)) :=
  rfl

@[simp]
lemma functorEquiv_unitIso_inv_app_app_inr (X : A ⊕ A' ⥤ B) (a' : A') :
    ((functorEquiv A A' B).unitIso.inv.app X).app (.inr a') = 𝟙 (X.obj (.inr a')) :=
  rfl

/-- Composing the forward direction of `functorEquiv` with the first projection is the same as
 precomposition with `inl_ A A'`. -/
@[simps!]
def functorEquivFunctorCompFstIso :
    (functorEquiv A A' B).functor ⋙ Prod.fst (A ⥤ B) (A' ⥤ B) ≅
    (whiskeringLeft A (A ⊕ A') B).obj (inl_ A A') :=
 NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- Composing the forward direction of `functorEquiv` with the second projection is the same as
 precomposition with `inr_ A A'`. -/
@[simps!]
def functorEquivFunctorCompSndIso :
    (functorEquiv A A' B).functor ⋙ Prod.snd (A ⥤ B) (A' ⥤ B) ≅
    (whiskeringLeft A' (A ⊕ A') B).obj (inr_ A A') :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- Composing the backward direction of `functorEquiv` with precomposition with `inl_ A A'`.
 is naturally isomorphic to the first projection. -/
@[simps!]
def functorEquivInverseCompWhiskeringLeftInlIso :
    (functorEquiv A A' B).inverse ⋙ (whiskeringLeft A (A ⊕ A') B).obj (inl_ A A') ≅
    Prod.fst (A ⥤ B) (A' ⥤ B) :=
  NatIso.ofComponents (fun _ ↦ Functor.inlCompSum' _ _)

/-- Composing the backward direction of `functorEquiv` with the second projection is the same as
 precomposition with `inr_ A A'`. -/
@[simps!]
def functorEquivInverseCompWhiskeringLeftInrIso :
    (functorEquiv A A' B).inverse ⋙ (whiskeringLeft A' (A ⊕ A') B).obj (inr_ A A') ≅
    Prod.snd (A ⥤ B) (A' ⥤ B) :=
  NatIso.ofComponents (fun _ ↦ Functor.inrCompSum' _ _)

/-- A consequence of `functorEquiv`: we can construct a natural transformation of functors
`A ⊕ A' ⥤ B` from the data of natural transformations of their whiskering with `inl_` and `inr_`. -/
@[simps!]
def natTransOfWhiskerLeftInlInr {F G : A ⊕ A' ⥤ B}
    (η₁ : Sum.inl_ A A' ⋙ F ⟶ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ⟶ Sum.inr_ A A' ⋙ G) :
    F ⟶ G :=
  (Sum.functorEquiv A A' B).unit.app F ≫
    (Sum.functorEquiv A A' B).inverse.map ((η₁, η₂) :) ≫
      (Sum.functorEquiv A A' B).unitInv.app G

@[simp]
lemma natTransOfWhiskerLeftInlInr_id {F : A ⊕ A' ⥤ B} :
    natTransOfWhiskerLeftInlInr (𝟙 (Sum.inl_ A A' ⋙ F)) (𝟙 (Sum.inr_ A A' ⋙ F)) = 𝟙 F := by
  aesop_cat

@[simp]
lemma natTransOfWhiskerLeftInlInr_comp {F G H : A ⊕ A' ⥤ B}
    (η₁ : Sum.inl_ A A' ⋙ F ⟶ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ⟶ Sum.inr_ A A' ⋙ G)
    (ν₁ : Sum.inl_ A A' ⋙ G ⟶ Sum.inl_ A A' ⋙ H) (ν₂ : Sum.inr_ A A' ⋙ G ⟶ Sum.inr_ A A' ⋙ H) :
    natTransOfWhiskerLeftInlInr (η₁ ≫ ν₁) (η₂ ≫ ν₂) = natTransOfWhiskerLeftInlInr η₁ η₂ ≫
      natTransOfWhiskerLeftInlInr ν₁ ν₂ := by
  aesop_cat

/-- A consequence of `functorEquiv`: we can construct a natural isomorphism of functors
`A ⊕ A' ⥤ B` from the data of natural isomorphisms of their whiskering with `inl_` and `inr_`. -/
@[simps]
def natIsoOfWhiskerLeftInlInr {F G : A ⊕ A' ⥤ B}
    (η₁ : Sum.inl_ A A' ⋙ F ≅ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ≅ Sum.inr_ A A' ⋙ G) :
    F ≅ G where
  hom := natTransOfWhiskerLeftInlInr η₁.hom η₂.hom
  inv := natTransOfWhiskerLeftInlInr η₁.inv η₂.inv

lemma natIsoOfWhiskerLeftInlInr_eq {F G : A ⊕ A' ⥤ B}
    (η₁ : Sum.inl_ A A' ⋙ F ≅ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ≅ Sum.inr_ A A' ⋙ G) :
    natIsoOfWhiskerLeftInlInr η₁ η₂ =
    (Sum.functorEquiv A A' B).unitIso.app _ ≪≫
      (Sum.functorEquiv A A' B).inverse.mapIso (Iso.prod η₁ η₂) ≪≫
      (Sum.functorEquiv A A' B).unitIso.symm.app _ := by
  aesop_cat

end Sum

end CategoryTheory
