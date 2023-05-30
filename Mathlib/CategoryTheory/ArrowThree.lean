import Mathlib.CategoryTheory.ArrowTwo
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Tactic.Linarith

namespace CategoryTheory

open Limits

variable (C : Type _) [Category C]

structure Arrow₃ :=
  {X₀ X₁ X₂ X₃ : C}
  f : X₀ ⟶ X₁
  g : X₁ ⟶ X₂
  h : X₂ ⟶ X₃

namespace Arrow₃

variable {C}

@[simps]
def mk' {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) : Arrow₃ C where
  f := f
  g := g
  h := h

@[ext]
structure Hom (D₁ D₂ : Arrow₃ C) where
  τ₀ : D₁.X₀ ⟶ D₂.X₀
  τ₁ : D₁.X₁ ⟶ D₂.X₁
  τ₂ : D₁.X₂ ⟶ D₂.X₂
  τ₃ : D₁.X₃ ⟶ D₂.X₃
  commf : τ₀ ≫ D₂.f = D₁.f ≫ τ₁ := by aesop_cat
  commg : τ₁ ≫ D₂.g = D₁.g ≫ τ₂ := by aesop_cat
  commh : τ₂ ≫ D₂.h = D₁.h ≫ τ₃ := by aesop_cat

attribute [reassoc] Hom.commf Hom.commg Hom.commh
attribute [local simp] Hom.commf Hom.commg Hom.commh
  Hom.commf_assoc Hom.commg_assoc Hom.commh_assoc

@[simps]
def Hom.id (D : Arrow₃ C) : Hom D D where
  τ₀ := 𝟙 _
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _

/-- The composition of morphisms of short complexes. -/
@[simps]
def Hom.comp {D₁ D₂ D₃ : Arrow₃ C}
    (φ₁₂ : Hom D₁ D₂) (φ₂₃ : Hom D₂ D₃) : Hom D₁ D₃ where
  τ₀ := φ₁₂.τ₀ ≫ φ₂₃.τ₀
  τ₁ := φ₁₂.τ₁ ≫ φ₂₃.τ₁
  τ₂ := φ₁₂.τ₂ ≫ φ₂₃.τ₂
  τ₃ := φ₁₂.τ₃ ≫ φ₂₃.τ₃

instance : Category (Arrow₃ C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext] lemma hom_ext {D₁ D₂ : Arrow₃ C} (f₁ f₂ : D₁ ⟶ D₂)
    (h₀ : f₁.τ₀ = f₂.τ₀) (h₁ : f₁.τ₁ = f₂.τ₁) (h₂ : f₁.τ₂ = f₂.τ₂) (h₃ : f₁.τ₃ = f₂.τ₃) :
    f₁ = f₂ :=
  Hom.ext _ _ h₀ h₁ h₂ h₃

@[simp] lemma id_τ₀ (D : Arrow₃ C) : Arrow₃.Hom.τ₀ (𝟙 D) = 𝟙 _ := rfl
@[simp] lemma id_τ₁ (D : Arrow₃ C) : Arrow₃.Hom.τ₁ (𝟙 D) = 𝟙 _ := rfl
@[simp] lemma id_τ₂ (D : Arrow₃ C) : Arrow₃.Hom.τ₂ (𝟙 D) = 𝟙 _ := rfl
@[simp] lemma id_τ₃ (D : Arrow₃ C) : Arrow₃.Hom.τ₃ (𝟙 D) = 𝟙 _ := rfl

@[reassoc] lemma comp_τ₀ {D₁ D₂ D₃ : Arrow₃ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₀ = f.τ₀ ≫ g.τ₀ := rfl
@[reassoc] lemma comp_τ₁ {D₁ D₂ D₃ : Arrow₃ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₁ = f.τ₁ ≫ g.τ₁ := rfl
@[reassoc] lemma comp_τ₂ {D₁ D₂ D₃ : Arrow₃ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₂ = f.τ₂ ≫ g.τ₂ := rfl
@[reassoc] lemma comp_τ₃ {D₁ D₂ D₃ : Arrow₃ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₃ = f.τ₃ ≫ g.τ₃ := rfl
attribute [simp] comp_τ₀ comp_τ₁ comp_τ₂ comp_τ₃

@[simps]
def δ₀ : Arrow₃ C ⥤ Arrow₂ C where
  obj D := Arrow₂.mk D.g D.h
  map φ :=
    { τ₀ := φ.τ₁
      τ₁ := φ.τ₂
      τ₂ := φ.τ₃ }

@[simps]
def δ₁ : Arrow₃ C ⥤ Arrow₂ C where
  obj D := Arrow₂.mk (D.f ≫ D.g) D.h
  map φ :=
    { τ₀ := φ.τ₀
      τ₁ := φ.τ₂
      τ₂ := φ.τ₃ }

@[simps]
def δ₂ : Arrow₃ C ⥤ Arrow₂ C where
  obj D := Arrow₂.mk D.f (D.g ≫ D.h)
  map φ :=
    { τ₀ := φ.τ₀
      τ₁ := φ.τ₁
      τ₂ := φ.τ₃ }

@[simps]
def δ₃ : Arrow₃ C ⥤ Arrow₂ C where
  obj D := Arrow₂.mk D.f D.g
  map φ :=
    { τ₀ := φ.τ₀
      τ₁ := φ.τ₁
      τ₂ := φ.τ₂ }

@[simps]
def δ₃Toδ₂ : (δ₃ : Arrow₃ C ⥤ _) ⟶ δ₂ where
  app D :=
    { τ₀ := 𝟙 _
      τ₁ := 𝟙 _
      τ₂ := D.h }

@[simps]
def δ₂Toδ₁ : (δ₂ : Arrow₃ C ⥤ _) ⟶ δ₁ where
  app D :=
    { τ₀ := 𝟙 _
      τ₁ := D.g
      τ₂ := 𝟙 _ }

@[simps]
def δ₁Toδ₀ : (δ₁ : Arrow₃ C ⥤ _) ⟶ δ₀ where
  app D :=
    { τ₀ := D.f
      τ₁ := 𝟙 _
      τ₂ := 𝟙 _ }

@[simps!]
def δ₃Toδ₀ := (δ₃Toδ₂ : (δ₃ : Arrow₃ C ⥤ _) ⟶ _) ≫ δ₂Toδ₁ ≫ δ₁Toδ₀

@[simps]
def fMor : Arrow₃ C ⥤ Arrow C where
  obj D := Arrow.mk D.f
  map φ :=
    { left := φ.τ₀
      right := φ.τ₁ }

@[simps]
def gMor : Arrow₃ C ⥤ Arrow C where
  obj D := Arrow.mk D.g
  map φ :=
    { left := φ.τ₁
      right := φ.τ₂ }

@[simps]
def hMor : Arrow₃ C ⥤ Arrow C where
  obj D := Arrow.mk D.h
  map φ :=
    { left := φ.τ₂
      right := φ.τ₃ }

@[simp]
lemma δ₂_map_δ₃Toδ₂_app (D : Arrow₃ C) : Arrow₂.δ₂.map (Arrow₃.δ₃Toδ₂.app D) = 𝟙 _ := by aesop_cat


lemma δ₀_map_δ₃Toδ₂_app_eq_δ₂Toδ₁_app_δ₀_obj (D : Arrow₃ C) :
    Arrow₂.δ₀.map (Arrow₃.δ₃Toδ₂.app D) = Arrow₂.δ₂Toδ₁.app (Arrow₃.δ₀.obj D) := by aesop_cat

@[simp]
lemma δ₀_map_δ₁Toδ₀_app (D : Arrow₃ C) :
  Arrow₂.δ₀.map (Arrow₃.δ₁Toδ₀.app D) = 𝟙 _ := by aesop_cat

@[simps]
def δ₂δ₂Toδ₃δ₁ : (Arrow₃.δ₂ : Arrow₃ C ⥤ _) ⋙ Arrow₂.δ₂ ⟶ Arrow₃.δ₃ ⋙ Arrow₂.δ₁ where
  app D :=
    { left := 𝟙 _
      right := D.g }

@[simps]
def δ₃δ₁Toδ₂δ₁ : (Arrow₃.δ₃ : Arrow₃ C ⥤ _) ⋙ Arrow₂.δ₁ ⟶ Arrow₃.δ₂ ⋙ Arrow₂.δ₁ where
  app D :=
    { left := 𝟙 _
      right := D.h }

@[simps]
def δ₃δ₁Toδ₂δ₀ : (Arrow₃.δ₃ : Arrow₃ C ⥤ _) ⋙ Arrow₂.δ₁ ⟶ Arrow₃.δ₂ ⋙ Arrow₂.δ₀ where
  app D :=
    { left := D.f
      right := D.h }

@[simps]
def δ₃δ₁Toδ₀δ₁ : (Arrow₃.δ₃ : Arrow₃ C ⥤ _) ⋙ Arrow₂.δ₁ ⟶ Arrow₃.δ₀ ⋙ Arrow₂.δ₁ where
  app D :=
    { left := D.f
      right := D.h }

@[simps]
def δ₃δ₁Toδ₀δ₂ : (Arrow₃.δ₃ : Arrow₃ C ⥤ _) ⋙ Arrow₂.δ₁ ⟶ Arrow₃.δ₀ ⋙ Arrow₂.δ₂ where
  app D :=
    { left := D.f
      right := 𝟙 _ }

@[simps]
def δ₃δ₀Toδ₀δ₁ : (Arrow₃.δ₃ : Arrow₃ C ⥤ _) ⋙ Arrow₂.δ₀ ⟶ Arrow₃.δ₀ ⋙ Arrow₂.δ₁ where
  app D :=
    { left := 𝟙 _
      right := D.h }

variable (C)

noncomputable def ιArrow [HasInitial C] [HasTerminal C] : Arrow C ⥤ Arrow₃ C where
  obj D := Arrow₃.mk (initial.to _) D.hom (terminal.from _)
  map {D₁ D₂} φ :=
    { τ₀ := 𝟙 _
      τ₁ := φ.left
      τ₂ := φ.right
      τ₃ := 𝟙 _ }

@[simps]
def mkOfLE {ι : Type _} [Preorder ι] (a b c d : ι)
    (hab : a ≤ b := by linarith) (hbc : b ≤ c := by linarith) (hcd : c ≤ d := by linarith) :
  Arrow₃ ι := Arrow₃.mk (homOfLE hab) (homOfLE hbc) (homOfLE hcd)

@[simps]
def _root_.CategoryTheory.Functor.mapArrow₃ {ι ι' : Type _} [Category ι] [Category ι'] (F : ι ⥤ ι') :
    Arrow₃ ι ⥤ Arrow₃ ι' where
  obj D := Arrow₃.mk (F.map D.f) (F.map D.g) (F.map D.h)
  map φ :=
    { τ₀ := F.map φ.τ₀
      τ₁ := F.map φ.τ₁
      τ₂ := F.map φ.τ₂
      τ₃ := F.map φ.τ₃
      commf := by
        dsimp
        simp only [← F.map_comp, Arrow₃.Hom.commf]
      commg := by
        dsimp
        simp only [← F.map_comp, Arrow₃.Hom.commg]
      commh := by
        dsimp
        simp only [← F.map_comp, Arrow₃.Hom.commh] }

end Arrow₃

end CategoryTheory
