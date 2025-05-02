/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortComplexFour
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# ShortComplex₅

-/

namespace CategoryTheory

open Limits

variable (C : Type _) [Category C]

structure ShortComplex₅ [HasZeroMorphisms C] where
  {X₁ X₂ X₃ X₄ X₅ : C}
  f : X₁ ⟶ X₂
  g : X₂ ⟶ X₃
  h : X₃ ⟶ X₄
  i : X₄ ⟶ X₅
  zero₁ : f ≫ g = 0 := by aesop_cat
  zero₂ : g ≫ h = 0 := by aesop_cat
  zero₃ : h ≫ i = 0 := by aesop_cat

namespace ShortComplex₅

attribute [reassoc (attr := simp)] zero₁ zero₂ zero₃

section

variable {C}
variable [HasZeroMorphisms C]

@[ext]
structure Hom (S₁ S₂ : ShortComplex₅ C) where
  τ₁ : S₁.X₁ ⟶ S₂.X₁
  τ₂ : S₁.X₂ ⟶ S₂.X₂
  τ₃ : S₁.X₃ ⟶ S₂.X₃
  τ₄ : S₁.X₄ ⟶ S₂.X₄
  τ₅ : S₁.X₅ ⟶ S₂.X₅
  commf : τ₁ ≫ S₂.f = S₁.f ≫ τ₂ := by aesop_cat
  commg : τ₂ ≫ S₂.g = S₁.g ≫ τ₃ := by aesop_cat
  commh : τ₃ ≫ S₂.h = S₁.h ≫ τ₄ := by aesop_cat
  commi : τ₄ ≫ S₂.i = S₁.i ≫ τ₅ := by aesop_cat

attribute [reassoc] Hom.commf Hom.commg Hom.commh Hom.commi
attribute [local simp] Hom.commf Hom.commg Hom.commh Hom.commi
  Hom.commf_assoc Hom.commg_assoc Hom.commh_assoc Hom.commi_assoc

variable (S : ShortComplex₅ C) {S₁ S₂ S₃ : ShortComplex₅ C}

/-- The identity morphism of a short complex. -/
@[simps]
def Hom.id : Hom S S where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  τ₄ := 𝟙 _
  τ₅ := 𝟙 _

/-- The composition of morphisms of short complexes. -/
@[simps]
def Hom.comp (φ₁₂ : Hom S₁ S₂) (φ₂₃ : Hom S₂ S₃) : Hom S₁ S₃ where
  τ₁ := φ₁₂.τ₁ ≫ φ₂₃.τ₁
  τ₂ := φ₁₂.τ₂ ≫ φ₂₃.τ₂
  τ₃ := φ₁₂.τ₃ ≫ φ₂₃.τ₃
  τ₄ := φ₁₂.τ₄ ≫ φ₂₃.τ₄
  τ₅ := φ₁₂.τ₅ ≫ φ₂₃.τ₅

instance : Category (ShortComplex₅ C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
lemma hom_ext (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ = g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ = g.τ₃)
    (h₄ : f.τ₄ = g.τ₄) (h₅ : f.τ₅ = g.τ₅) : f = g :=
  Hom.ext h₁ h₂ h₃ h₄ h₅

/-- A constructor for morphisms in `ShortComplex₄ C` when the commutativity conditions
are not obvious. -/
@[simps]
def homMk {S₁ S₂ : ShortComplex₅ C} (τ₁ : S₁.X₁ ⟶ S₂.X₁) (τ₂ : S₁.X₂ ⟶ S₂.X₂)
    (τ₃ : S₁.X₃ ⟶ S₂.X₃) (τ₄ : S₁.X₄ ⟶ S₂.X₄) (τ₅ : S₁.X₅ ⟶ S₂.X₅)
    (commf : τ₁ ≫ S₂.f = S₁.f ≫ τ₂) (commg : τ₂ ≫ S₂.g = S₁.g ≫ τ₃)
    (commh : τ₃ ≫ S₂.h = S₁.h ≫ τ₄) (commi : τ₄ ≫ S₂.i = S₁.i ≫ τ₅):
  S₁ ⟶ S₂ := ⟨τ₁, τ₂, τ₃, τ₄, τ₅, commf, commg, commh, commi⟩

@[simp] lemma id_τ₁ : Hom.τ₁ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₂ : Hom.τ₂ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₃ : Hom.τ₃ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₄ : Hom.τ₄ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_τ₅ : Hom.τ₅ (𝟙 S) = 𝟙 _ := rfl
@[reassoc] lemma comp_τ₁ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₁ = φ₁₂.τ₁ ≫ φ₂₃.τ₁ := rfl
@[reassoc] lemma comp_τ₂ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₂ = φ₁₂.τ₂ ≫ φ₂₃.τ₂ := rfl
@[reassoc] lemma comp_τ₃ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₃ = φ₁₂.τ₃ ≫ φ₂₃.τ₃ := rfl
@[reassoc] lemma comp_τ₄ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₄ = φ₁₂.τ₄ ≫ φ₂₃.τ₄ := rfl
@[reassoc] lemma comp_τ₅ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₅ = φ₁₂.τ₅ ≫ φ₂₃.τ₅ := rfl

attribute [simp] comp_τ₁ comp_τ₂ comp_τ₃ comp_τ₄ comp_τ₅

instance : Zero (S₁ ⟶ S₂) := ⟨{ τ₁ := 0, τ₂ := 0, τ₃ := 0, τ₄ := 0, τ₅ := 0 }⟩

variable (S₁ S₂)

@[simp] lemma zero_τ₁ : Hom.τ₁ (0 : S₁ ⟶ S₂) = 0 := rfl
@[simp] lemma zero_τ₂ : Hom.τ₂ (0 : S₁ ⟶ S₂) = 0 := rfl
@[simp] lemma zero_τ₃ : Hom.τ₃ (0 : S₁ ⟶ S₂) = 0 := rfl
@[simp] lemma zero_τ₄ : Hom.τ₄ (0 : S₁ ⟶ S₂) = 0 := rfl
@[simp] lemma zero_τ₅ : Hom.τ₅ (0 : S₁ ⟶ S₂) = 0 := rfl

variable {S₁ S₂}

instance : HasZeroMorphisms (ShortComplex C) where

@[simps]
def shortComplex₁ : ShortComplex C :=
  ShortComplex.mk _ _ S.zero₁

@[simps]
def shortComplex₂ : ShortComplex C :=
  ShortComplex.mk _ _ S.zero₂

@[simps]
def shortComplex₃ : ShortComplex C :=
  ShortComplex.mk _ _ S.zero₃

@[simps]
def shortComplex₄Functor₁₂₃₄ : ShortComplex₅ C ⥤ ShortComplex₄ C where
  obj K := ShortComplex₄.mk K.f K.g K.h
  map φ :=
    { τ₁ := φ.τ₁
      τ₂ := φ.τ₂
      τ₃ := φ.τ₃
      τ₄ := φ.τ₄ }

@[simps]
def shortComplex₄Functor₂₃₄₅ : ShortComplex₅ C ⥤ ShortComplex₄ C where
  obj K := ShortComplex₄.mk K.g K.h K.i
  map φ :=
    { τ₁ := φ.τ₂
      τ₂ := φ.τ₃
      τ₃ := φ.τ₄
      τ₄ := φ.τ₅ }

structure Exact : Prop where
  exact₂ : S.shortComplex₁.Exact
  exact₃ : S.shortComplex₂.Exact
  exact₄ : S.shortComplex₃.Exact

namespace Exact

variable {S}

lemma exact₁₂₃₄ (hS : S.Exact) :
    (shortComplex₄Functor₁₂₃₄.obj S).Exact where
  exact₂ := hS.exact₂
  exact₃ := hS.exact₃

lemma exact₂₃₄₅ (hS : S.Exact) :
    (shortComplex₄Functor₂₃₄₅.obj S).Exact where
  exact₂ := hS.exact₃
  exact₃ := hS.exact₄

end Exact

end

end ShortComplex₅

end CategoryTheory
