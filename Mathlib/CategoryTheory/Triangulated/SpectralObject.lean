/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ComposableArrows.One
import Mathlib.CategoryTheory.ComposableArrows.Two
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Spectral objects in triangulated categories



## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

namespace CategoryTheory

open Category Limits Pretriangulated ComposableArrows

variable (C ι : Type*) [Category C] [Category ι] [HasZeroObject C]
  [HasShift C ℤ] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type _} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Triangulated

structure SpectralObject where
  ω₁ : ComposableArrows ι 1 ⥤ C
  δ' : functorArrows ι 1 2 2 ⋙ ω₁ ⟶ functorArrows ι 0 1 2 ⋙ ω₁ ⋙ shiftFunctor C (1 : ℤ)
  distinguished' (D : ComposableArrows ι 2) :
    Triangle.mk (ω₁.map ((mapFunctorArrows ι 0 1 0 2 2).app D))
      (ω₁.map ((mapFunctorArrows ι 0 2 1 2 2).app D)) (δ'.app D) ∈ distTriang C

namespace SpectralObject

variable {C ι}
variable (X : SpectralObject C ι)

def ω₂ : ComposableArrows ι 2 ⥤ Triangle C := by
  sorry

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

def δ : X.ω₁.obj (mk₁ g) ⟶ (X.ω₁.obj (mk₁ f))⟦(1 : ℤ)⟧ :=
  X.δ'.app (mk₂ f g)

@[reassoc]
lemma δ_naturality {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
    (α : mk₁ f ⟶ mk₁ f') (β : mk₁ g ⟶ mk₁ g') (hαβ : α.app 1 = β.app 0):
    X.ω₁.map β ≫ X.δ f' g' = X.δ f g ≫ (X.ω₁.map α)⟦(1 : ℤ)⟧' := by
  let φ : mk₂ f g ⟶ mk₂ f' g' := homMk₂ (α.app 0) (α.app 1) (β.app 1) (naturality' α 0 1)
    (by simpa only [hαβ] using naturality' β 0 1)
  have h := X.δ'.naturality φ
  dsimp at h
  simp only [φ, hαβ] at h
  convert h <;> aesop_cat

@[simps!]
def triangle : Triangle C :=
  Triangle.mk (X.ω₁.map (twoδ₂Toδ₁ f g _ rfl))
    (X.ω₁.map (twoδ₁Toδ₀ f g _ rfl)) (X.δ f g)

lemma triangle_distinguished : X.triangle f g ∈ distTriang C :=
  X.distinguished' (mk₂ f g)

variable {f g} in
noncomputable def mapTriangle
    {i' j' k' : ι} {f' : i' ⟶ j'} {g' : j' ⟶ k'} (φ : mk₂ f g ⟶ mk₂ f' g') :
    X.triangle f g ⟶ X.triangle f' g' where
  hom₁ := X.ω₁.map ((functorArrows ι 0 1 2).map φ)
  hom₂ := X.ω₁.map ((functorArrows ι 0 2 2).map φ)
  hom₃ := X.ω₁.map ((functorArrows ι 1 2 2).map φ)
  comm₁ := by
    dsimp
    simp only [← X.ω₁.map_comp]
    congr 1
    ext
    · simp
    · exact naturality' φ 1 2
  comm₂ := by
    dsimp
    simp only [← X.ω₁.map_comp]
    congr 1
    ext
    · exact naturality' φ 0 1
    · simp
  comm₃ := (X.δ_naturality _ _ _ _ _ _ (by simp)).symm

end

noncomputable def mapTriangulatedFunctor (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    SpectralObject D ι where
  ω₁ := X.ω₁ ⋙ F
  δ' := Functor.whiskerRight X.δ' F ≫
      Functor.whiskerLeft (functorArrows ι 0 1 2 ⋙ X.ω₁) (F.commShiftIso (1 : ℤ)).hom
  distinguished' D := sorry--F.map_distinguished _ (X.distinguished' D)

end SpectralObject

end Triangulated

end CategoryTheory
