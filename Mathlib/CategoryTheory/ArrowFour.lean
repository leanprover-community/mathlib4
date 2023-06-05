import Mathlib.CategoryTheory.ArrowThree
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Tactic.Linarith

namespace CategoryTheory

open Limits

variable (C : Type _) [Category C]

structure Arrow₄ :=
  {X₀ X₁ X₂ X₃ X₄ : C}
  f : X₀ ⟶ X₁
  g : X₁ ⟶ X₂
  h : X₂ ⟶ X₃
  i : X₃ ⟶ X₄

namespace Arrow₄

variable {C}

@[simps]
def mk' {X₀ X₁ X₂ X₃ X₄ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄) :
    Arrow₄ C where
  f := f
  g := g
  h := h
  i := i

@[ext]
structure Hom (D₁ D₂ : Arrow₄ C) where
  τ₀ : D₁.X₀ ⟶ D₂.X₀
  τ₁ : D₁.X₁ ⟶ D₂.X₁
  τ₂ : D₁.X₂ ⟶ D₂.X₂
  τ₃ : D₁.X₃ ⟶ D₂.X₃
  τ₄ : D₁.X₄ ⟶ D₂.X₄
  commf : τ₀ ≫ D₂.f = D₁.f ≫ τ₁ := by aesop_cat
  commg : τ₁ ≫ D₂.g = D₁.g ≫ τ₂ := by aesop_cat
  commh : τ₂ ≫ D₂.h = D₁.h ≫ τ₃ := by aesop_cat
  commi : τ₃ ≫ D₂.i = D₁.i ≫ τ₄ := by aesop_cat

attribute [reassoc] Hom.commf Hom.commg Hom.commh Hom.commi
attribute [local simp] Hom.commf Hom.commg Hom.commh Hom.commi
  Hom.commf_assoc Hom.commg_assoc Hom.commh_assoc Hom.commi_assoc

@[simps]
def Hom.id (D : Arrow₄ C) : Hom D D where
  τ₀ := 𝟙 _
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  τ₄ := 𝟙 _

/-- The composition of morphisms of short complexes. -/
@[simps]
def Hom.comp {D₁ D₂ D₃ : Arrow₄ C}
    (φ₁₂ : Hom D₁ D₂) (φ₂₃ : Hom D₂ D₃) : Hom D₁ D₃ where
  τ₀ := φ₁₂.τ₀ ≫ φ₂₃.τ₀
  τ₁ := φ₁₂.τ₁ ≫ φ₂₃.τ₁
  τ₂ := φ₁₂.τ₂ ≫ φ₂₃.τ₂
  τ₃ := φ₁₂.τ₃ ≫ φ₂₃.τ₃
  τ₄ := φ₁₂.τ₄ ≫ φ₂₃.τ₄

instance : Category (Arrow₄ C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext] lemma hom_ext {D₁ D₂ : Arrow₄ C} (f₁ f₂ : D₁ ⟶ D₂)
    (h₀ : f₁.τ₀ = f₂.τ₀) (h₁ : f₁.τ₁ = f₂.τ₁) (h₂ : f₁.τ₂ = f₂.τ₂) (h₃ : f₁.τ₃ = f₂.τ₃)
    (h₄ : f₁.τ₄ = f₂.τ₄) :
    f₁ = f₂ :=
  Hom.ext _ _ h₀ h₁ h₂ h₃ h₄

@[simp] lemma id_τ₀ (D : Arrow₄ C) : Arrow₄.Hom.τ₀ (𝟙 D) = 𝟙 _ := rfl
@[simp] lemma id_τ₁ (D : Arrow₄ C) : Arrow₄.Hom.τ₁ (𝟙 D) = 𝟙 _ := rfl
@[simp] lemma id_τ₂ (D : Arrow₄ C) : Arrow₄.Hom.τ₂ (𝟙 D) = 𝟙 _ := rfl
@[simp] lemma id_τ₃ (D : Arrow₄ C) : Arrow₄.Hom.τ₃ (𝟙 D) = 𝟙 _ := rfl
@[simp] lemma id_τ₄ (D : Arrow₄ C) : Arrow₄.Hom.τ₄ (𝟙 D) = 𝟙 _ := rfl

@[reassoc] lemma comp_τ₀ {D₁ D₂ D₃ : Arrow₄ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₀ = f.τ₀ ≫ g.τ₀ := rfl
@[reassoc] lemma comp_τ₁ {D₁ D₂ D₃ : Arrow₄ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₁ = f.τ₁ ≫ g.τ₁ := rfl
@[reassoc] lemma comp_τ₂ {D₁ D₂ D₃ : Arrow₄ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₂ = f.τ₂ ≫ g.τ₂ := rfl
@[reassoc] lemma comp_τ₃ {D₁ D₂ D₃ : Arrow₄ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₃ = f.τ₃ ≫ g.τ₃ := rfl
@[reassoc] lemma comp_τ₄ {D₁ D₂ D₃ : Arrow₄ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₄ = f.τ₄ ≫ g.τ₄ := rfl
attribute [simp] comp_τ₀ comp_τ₁ comp_τ₂ comp_τ₃ comp_τ₄

@[simps]
def δ₀ : Arrow₄ C ⥤ Arrow₃ C where
  obj D := Arrow₃.mk D.g D.h D.i
  map φ :=
    { τ₀ := φ.τ₁
      τ₁ := φ.τ₂
      τ₂ := φ.τ₃
      τ₃ := φ.τ₄ }

@[simps]
def δ₁ : Arrow₄ C ⥤ Arrow₃ C where
  obj D := Arrow₃.mk (D.f ≫ D.g) D.h D.i
  map φ :=
    { τ₀ := φ.τ₀
      τ₁ := φ.τ₂
      τ₂ := φ.τ₃
      τ₃ := φ.τ₄ }

@[simps]
def δ₂ : Arrow₄ C ⥤ Arrow₃ C where
  obj D := Arrow₃.mk D.f (D.g ≫ D.h) D.i
  map φ :=
    { τ₀ := φ.τ₀
      τ₁ := φ.τ₁
      τ₂ := φ.τ₃
      τ₃ := φ.τ₄ }

@[simps]
def δ₃ : Arrow₄ C ⥤ Arrow₃ C where
  obj D := Arrow₃.mk D.f D.g (D.h ≫ D.i)
  map φ :=
    { τ₀ := φ.τ₀
      τ₁ := φ.τ₁
      τ₂ := φ.τ₂
      τ₃ := φ.τ₄ }

@[simps]
def δ₄ : Arrow₄ C ⥤ Arrow₃ C where
  obj D := Arrow₃.mk D.f D.g D.h
  map φ :=
    { τ₀ := φ.τ₀
      τ₁ := φ.τ₁
      τ₂ := φ.τ₂
      τ₃ := φ.τ₃ }

end Arrow₄

end CategoryTheory
