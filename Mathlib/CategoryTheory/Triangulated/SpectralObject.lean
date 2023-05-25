import Mathlib.CategoryTheory.Triangulated.Triangulated

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory

variable (C : Type _) [Category C]

structure Arrow₂ :=
  {X₀ X₁ X₂ : C}
  f : X₀ ⟶ X₁
  g : X₁ ⟶ X₂

namespace Arrow₂

variable {C}

@[simps]
def mk' {X₀ X₁ X₂ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) : Arrow₂ C where
  f := f
  g := g

@[ext]
structure Hom (D₁ D₂ : Arrow₂ C) where
  τ₀ : D₁.X₀ ⟶ D₂.X₀
  τ₁ : D₁.X₁ ⟶ D₂.X₁
  τ₂ : D₁.X₂ ⟶ D₂.X₂
  commf : τ₀ ≫ D₂.f = D₁.f ≫ τ₁ := by aesop_cat
  commg : τ₁ ≫ D₂.g = D₁.g ≫ τ₂ := by aesop_cat

attribute [reassoc] Hom.commf Hom.commg
attribute [local simp] Hom.commf Hom.commg Hom.commf_assoc Hom.commg_assoc

@[simps]
def Hom.id (D : Arrow₂ C) : Hom D D where
  τ₀ := 𝟙 _
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _

/-- The composition of morphisms of short complexes. -/
@[simps]
def Hom.comp {D₁ D₂ D₃ : Arrow₂ C}
    (φ₁₂ : Hom D₁ D₂) (φ₂₃ : Hom D₂ D₃) : Hom D₁ D₃ where
  τ₀ := φ₁₂.τ₀ ≫ φ₂₃.τ₀
  τ₁ := φ₁₂.τ₁ ≫ φ₂₃.τ₁
  τ₂ := φ₁₂.τ₂ ≫ φ₂₃.τ₂

instance : Category (Arrow₂ C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simps]
def δ₀ : Arrow₂ C ⥤ Arrow C where
  obj D := Arrow.mk D.g
  map φ :=
    { left := φ.τ₁
      right := φ.τ₂ }

@[simps]
def δ₁ : Arrow₂ C ⥤ Arrow C where
  obj D := Arrow.mk (D.f ≫ D.g)
  map φ :=
    { left := φ.τ₀
      right := φ.τ₂ }

@[simps]
def δ₂ : Arrow₂ C ⥤ Arrow C where
  obj D := Arrow.mk D.f
  map φ :=
    { left := φ.τ₀
      right := φ.τ₁ }

def δ₂Toδ₁ : (δ₂ : Arrow₂ C ⥤ _) ⟶ δ₁ where
  app D :=
    { left := 𝟙 _
      right := D.g }

def δ₁Toδ₀ : (δ₁ : Arrow₂ C ⥤ _) ⟶ δ₀ where
  app D :=
    { left := D.f
      right := 𝟙 _ }

end Arrow₂

variable (C ι : Type _) [Category C] [Category ι] [HasZeroObject C]
  [HasShift C ℤ] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [Preorder ι]

namespace Triangulated

structure SpectralObject where
  ω₁ : Arrow ι ⥤ C
  δ : Arrow₂.δ₀ ⋙ ω₁ ⟶ Arrow₂.δ₂ ⋙ ω₁ ⋙ shiftFunctor C (1 : ℤ)
  distinguished (D : Arrow₂ ι) :
    Triangle.mk (ω₁.map (Arrow₂.δ₂Toδ₁.app D))
      (ω₁.map (Arrow₂.δ₁Toδ₀.app D)) (δ.app D) ∈ distTriang C

namespace SpectralObject

variable {C ι}
variable (X : SpectralObject C ι)

def ω₂ : Arrow₂ ι ⥤ Triangle C where
  obj D := Triangle.mk (X.ω₁.map (Arrow₂.δ₂Toδ₁.app D)) (X.ω₁.map (Arrow₂.δ₁Toδ₀.app D)) (X.δ.app D)
  map f :=
    { hom₁ := X.ω₁.map (Arrow₂.δ₂.map f)
      hom₂ := X.ω₁.map (Arrow₂.δ₁.map f)
      hom₃ := X.ω₁.map (Arrow₂.δ₀.map f)
      comm₁ := by
        dsimp
        simp only [← Functor.map_comp, NatTrans.naturality]
      comm₂ := by
        dsimp
        simp only [← Functor.map_comp, NatTrans.naturality]
      comm₃ := (X.δ.naturality f).symm }

end SpectralObject

end Triangulated

end CategoryTheory
