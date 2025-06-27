/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ArrowFour
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Tactic.Linarith

/-!
# Arrow₅

-/

namespace CategoryTheory

open Limits

variable (C : Type _) [Category C]

structure Arrow₅ where
  {X₀ X₁ X₂ X₃ X₄ X₅ : C}
  f : X₀ ⟶ X₁
  g : X₁ ⟶ X₂
  h : X₂ ⟶ X₃
  i : X₃ ⟶ X₄
  j : X₄ ⟶ X₅

namespace Arrow₅

variable {C}

/-- Constructor for `Arrow₅`. -/
@[simps]
def mk' {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄) (j : X₄ ⟶ X₅) :
    Arrow₅ C where
  f := f
  g := g
  h := h
  i := i
  j := j

@[ext]
structure Hom (D₁ D₂ : Arrow₅ C) where
  τ₀ : D₁.X₀ ⟶ D₂.X₀
  τ₁ : D₁.X₁ ⟶ D₂.X₁
  τ₂ : D₁.X₂ ⟶ D₂.X₂
  τ₃ : D₁.X₃ ⟶ D₂.X₃
  τ₄ : D₁.X₄ ⟶ D₂.X₄
  τ₅ : D₁.X₅ ⟶ D₂.X₅
  commf : τ₀ ≫ D₂.f = D₁.f ≫ τ₁ := by aesop_cat
  commg : τ₁ ≫ D₂.g = D₁.g ≫ τ₂ := by aesop_cat
  commh : τ₂ ≫ D₂.h = D₁.h ≫ τ₃ := by aesop_cat
  commi : τ₃ ≫ D₂.i = D₁.i ≫ τ₄ := by aesop_cat
  commj : τ₄ ≫ D₂.j = D₁.j ≫ τ₅ := by aesop_cat

attribute [reassoc] Hom.commf Hom.commg Hom.commh Hom.commi Hom.commj
attribute [local simp] Hom.commf Hom.commg Hom.commh Hom.commi Hom.commj
  Hom.commf_assoc Hom.commg_assoc Hom.commh_assoc Hom.commi_assoc Hom.commj_assoc

@[simps]
def Hom.id (D : Arrow₅ C) : Hom D D where
  τ₀ := 𝟙 _
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  τ₄ := 𝟙 _
  τ₅ := 𝟙 _

/-- The composition of morphisms of short complexes. -/
@[simps]
def Hom.comp {D₁ D₂ D₃ : Arrow₅ C}
    (φ₁₂ : Hom D₁ D₂) (φ₂₃ : Hom D₂ D₃) : Hom D₁ D₃ where
  τ₀ := φ₁₂.τ₀ ≫ φ₂₃.τ₀
  τ₁ := φ₁₂.τ₁ ≫ φ₂₃.τ₁
  τ₂ := φ₁₂.τ₂ ≫ φ₂₃.τ₂
  τ₃ := φ₁₂.τ₃ ≫ φ₂₃.τ₃
  τ₄ := φ₁₂.τ₄ ≫ φ₂₃.τ₄
  τ₅ := φ₁₂.τ₅ ≫ φ₂₃.τ₅

instance : Category (Arrow₅ C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext] lemma hom_ext {D₁ D₂ : Arrow₅ C} (f₁ f₂ : D₁ ⟶ D₂)
    (h₀ : f₁.τ₀ = f₂.τ₀) (h₁ : f₁.τ₁ = f₂.τ₁) (h₂ : f₁.τ₂ = f₂.τ₂) (h₃ : f₁.τ₃ = f₂.τ₃)
    (h₄ : f₁.τ₄ = f₂.τ₄) (h₅ : f₁.τ₅ = f₂.τ₅) :
    f₁ = f₂ :=
  Hom.ext h₀ h₁ h₂ h₃ h₄ h₅

@[simp] lemma id_τ₀ (D : Arrow₅ C) : Arrow₅.Hom.τ₀ (𝟙 D) = 𝟙 _ := rfl
@[simp] lemma id_τ₁ (D : Arrow₅ C) : Arrow₅.Hom.τ₁ (𝟙 D) = 𝟙 _ := rfl
@[simp] lemma id_τ₂ (D : Arrow₅ C) : Arrow₅.Hom.τ₂ (𝟙 D) = 𝟙 _ := rfl
@[simp] lemma id_τ₃ (D : Arrow₅ C) : Arrow₅.Hom.τ₃ (𝟙 D) = 𝟙 _ := rfl
@[simp] lemma id_τ₄ (D : Arrow₅ C) : Arrow₅.Hom.τ₄ (𝟙 D) = 𝟙 _ := rfl
@[simp] lemma id_τ₅ (D : Arrow₅ C) : Arrow₅.Hom.τ₅ (𝟙 D) = 𝟙 _ := rfl

@[reassoc] lemma comp_τ₀ {D₁ D₂ D₃ : Arrow₅ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₀ = f.τ₀ ≫ g.τ₀ := rfl
@[reassoc] lemma comp_τ₁ {D₁ D₂ D₃ : Arrow₅ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₁ = f.τ₁ ≫ g.τ₁ := rfl
@[reassoc] lemma comp_τ₂ {D₁ D₂ D₃ : Arrow₅ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₂ = f.τ₂ ≫ g.τ₂ := rfl
@[reassoc] lemma comp_τ₃ {D₁ D₂ D₃ : Arrow₅ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₃ = f.τ₃ ≫ g.τ₃ := rfl
@[reassoc] lemma comp_τ₄ {D₁ D₂ D₃ : Arrow₅ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₄ = f.τ₄ ≫ g.τ₄ := rfl
@[reassoc] lemma comp_τ₅ {D₁ D₂ D₃ : Arrow₅ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₅ = f.τ₅ ≫ g.τ₅ := rfl
attribute [simp] comp_τ₀ comp_τ₁ comp_τ₂ comp_τ₃ comp_τ₄ comp_τ₅

@[simps]
def δ₀ : Arrow₅ C ⥤ Arrow₄ C where
  obj D := Arrow₄.mk D.g D.h D.i D.j
  map φ :=
    { τ₀ := φ.τ₁
      τ₁ := φ.τ₂
      τ₂ := φ.τ₃
      τ₃ := φ.τ₄
      τ₄ := φ.τ₅ }

@[simps]
def δ₁ : Arrow₅ C ⥤ Arrow₄ C where
  obj D := Arrow₄.mk (D.f ≫ D.g) D.h D.i D.j
  map φ :=
    { τ₀ := φ.τ₀
      τ₁ := φ.τ₂
      τ₂ := φ.τ₃
      τ₃ := φ.τ₄
      τ₄ := φ.τ₅ }

@[simps]
def δ₂ : Arrow₅ C ⥤ Arrow₄ C where
  obj D := Arrow₄.mk D.f (D.g ≫ D.h) D.i D.j
  map φ :=
    { τ₀ := φ.τ₀
      τ₁ := φ.τ₁
      τ₂ := φ.τ₃
      τ₃ := φ.τ₄
      τ₄ := φ.τ₅ }

@[simps]
def δ₃ : Arrow₅ C ⥤ Arrow₄ C where
  obj D := Arrow₄.mk D.f D.g (D.h ≫ D.i) D.j
  map φ :=
    { τ₀ := φ.τ₀
      τ₁ := φ.τ₁
      τ₂ := φ.τ₂
      τ₃ := φ.τ₄
      τ₄ := φ.τ₅ }

@[simps]
def δ₄ : Arrow₅ C ⥤ Arrow₄ C where
  obj D := Arrow₄.mk D.f D.g D.h (D.i ≫ D.j)
  map φ :=
    { τ₀ := φ.τ₀
      τ₁ := φ.τ₁
      τ₂ := φ.τ₂
      τ₃ := φ.τ₃
      τ₄ := φ.τ₅ }

@[simps]
def δ₅ : Arrow₅ C ⥤ Arrow₄ C where
  obj D := Arrow₄.mk D.f D.g D.h D.i
  map φ :=
    { τ₀ := φ.τ₀
      τ₁ := φ.τ₁
      τ₂ := φ.τ₂
      τ₃ := φ.τ₃
      τ₄ := φ.τ₄ }

@[simps]
def mkOfLE {ι : Type _} [Preorder ι] (a b c d e f : ι)
    (hab : a ≤ b := by linarith) (hbc : b ≤ c := by linarith) (hcd : c ≤ d := by linarith)
    (hde : d ≤ e := by linarith) (hef : e ≤ f := by linarith) :
    Arrow₅ ι := Arrow₅.mk (homOfLE hab) (homOfLE hbc) (homOfLE hcd) (homOfLE hde) (homOfLE hef)

@[simps]
def _root_.CategoryTheory.Functor.mapArrow₅
    {ι ι' : Type _} [Category ι] [Category ι'] (F : ι ⥤ ι') :
    Arrow₅ ι ⥤ Arrow₅ ι' where
  obj D := Arrow₅.mk (F.map D.f) (F.map D.g) (F.map D.h) (F.map D.i) (F.map D.j)
  map φ :=
    { τ₀ := F.map φ.τ₀
      τ₁ := F.map φ.τ₁
      τ₂ := F.map φ.τ₂
      τ₃ := F.map φ.τ₃
      τ₄ := F.map φ.τ₄
      τ₅ := F.map φ.τ₅
      commf := by
        dsimp
        simp only [← F.map_comp, Arrow₅.Hom.commf]
      commg := by
        dsimp
        simp only [← F.map_comp, Arrow₅.Hom.commg]
      commh := by
        dsimp
        simp only [← F.map_comp, Arrow₅.Hom.commh]
      commi := by
        dsimp
        simp only [← F.map_comp, Arrow₅.Hom.commi]
      commj := by
        dsimp
        simp only [← F.map_comp, Arrow₅.Hom.commj] }


end Arrow₅

end CategoryTheory
