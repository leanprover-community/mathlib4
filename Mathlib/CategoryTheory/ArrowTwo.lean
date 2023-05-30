import Mathlib.CategoryTheory.Arrow

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

@[ext] lemma hom_ext {D₁ D₂ : Arrow₂ C} (f₁ f₂ : D₁ ⟶ D₂)
    (h₀ : f₁.τ₀ = f₂.τ₀) (h₁ : f₁.τ₁ = f₂.τ₁) (h₂ : f₁.τ₂ = f₂.τ₂) : f₁ = f₂ :=
  Hom.ext _ _ h₀ h₁ h₂

@[simp] lemma τ₀_id (D : Arrow₂ C) : Hom.τ₀ (𝟙 D) = 𝟙 _ := rfl
@[simp] lemma τ₁_id (D : Arrow₂ C) : Hom.τ₁ (𝟙 D) = 𝟙 _ := rfl
@[simp] lemma τ₂_id (D : Arrow₂ C) : Hom.τ₂ (𝟙 D) = 𝟙 _ := rfl

@[reassoc]
lemma τ₀_comp {D₁ D₂ D₃ : Arrow₂ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₀ = f.τ₀ ≫ g.τ₀ := rfl

@[reassoc]
lemma τ₁_comp {D₁ D₂ D₃ : Arrow₂ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₁ = f.τ₁ ≫ g.τ₁ := rfl

@[reassoc]
lemma τ₂_comp {D₁ D₂ D₃ : Arrow₂ C} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).τ₂ = f.τ₂ ≫ g.τ₂ := rfl

attribute [simp] τ₀_comp τ₁_comp τ₂_comp

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

@[simps]
def δ₂Toδ₁ : (δ₂ : Arrow₂ C ⥤ _) ⟶ δ₁ where
  app D :=
    { left := 𝟙 _
      right := D.g }

@[simps]
def δ₁Toδ₀ : (δ₁ : Arrow₂ C ⥤ _) ⟶ δ₀ where
  app D :=
    { left := D.f
      right := 𝟙 _ }

end Arrow₂

end CategoryTheory
