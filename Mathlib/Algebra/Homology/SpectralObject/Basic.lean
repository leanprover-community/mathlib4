/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.ComposableArrows.One
public import Mathlib.CategoryTheory.ComposableArrows.Two

/-!
# Spectral objects in abelian categories

In this file, we introduce the category `SpectralObject C ι` of spectral
objects in an abelian category `C` indexed by the category `ι`.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Abelian

variable (C ι : Type*) [Category C] [Category ι] [Abelian C]

open ComposableArrows

/-- A spectral object in an abelian category category `C` indexed by a category ``
consists of a functor `H : ComposableArrows ι 1 ⥤ C`, and a
functorial long exact sequence
`⋯ ⟶ (H n₀).obj (mk₁ f) ⟶ (H n₀).obj (mk₁ (f ≫ g)) ⟶ (H n₀).obj (mk₁ g) ⟶ (H n₁).obj (mk₁ f) ⟶ ⋯`
when `n₀ + 1 = n₁` and `f` and `g` are composable morphisms in `ι`. (This will be
shortened as `H^n₀(f) ⟶ H^n₀(f ≫ g) ⟶ H^n₀(g) ⟶ H^n₁(f)` in the documentation.) -/
structure SpectralObject where
  /-- A sequence of functors from `ComposableArrows ι 1` to the abelian category.
  The image of `mk₁ f` will be referred to as `H^n(f)` in the documentation. -/
  H (n : ℤ) : ComposableArrows ι 1 ⥤ C
  /-- The connecting homomorphism of the spectral object. (Use `δ` instead.) -/
  δ' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    functorArrows ι 1 2 2 ⋙ H n₀ ⟶ functorArrows ι 0 1 2 ⋙ H n₁
  exact₁' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2) :
    (mk₂ ((δ' n₀ n₁ h).app D) ((H n₁).map ((mapFunctorArrows ι 0 1 0 2 2).app D))).Exact
  exact₂' (n : ℤ) (D : ComposableArrows ι 2) :
    (mk₂ ((H n).map ((mapFunctorArrows ι 0 1 0 2 2).app D))
      ((H n).map ((mapFunctorArrows ι 0 2 1 2 2).app D))).Exact
  exact₃' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2) :
    (mk₂ ((H n₀).map ((mapFunctorArrows ι 0 2 1 2 2).app D)) ((δ' n₀ n₁ h).app D)).Exact

namespace SpectralObject

variable {C ι} (X : SpectralObject C ι)

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

/-- The connecting homomorphism of the spectral object. -/
def δ : (X.H n₀).obj (mk₁ g) ⟶ (X.H n₁).obj (mk₁ f) :=
  (X.δ' n₀ n₁ hn₁).app (mk₂ f g)

@[reassoc]
lemma δ_naturality {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
    (α : mk₁ f ⟶ mk₁ f') (β : mk₁ g ⟶ mk₁ g') (hαβ : α.app 1 = β.app 0 := by cat_disch) :
    (X.H n₀).map β ≫ X.δ n₀ n₁ hn₁ f' g' = X.δ n₀ n₁ hn₁ f g ≫ (X.H n₁).map α := by
  have h := (X.δ' n₀ n₁ hn₁).naturality
    (homMk₂ (α.app 0) (α.app 1) (β.app 1) (naturality' α 0 1)
      (by simpa only [hαβ] using naturality' β 0 1) : mk₂ f g ⟶ mk₂ f' g')
  dsimp at h
  convert h <;> cat_disch

end

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  (fg : i ⟶ k) (h : f ≫ g = fg)

@[reassoc (attr := simp)]
lemma zero₁ :
    X.δ n₀ n₁ hn₁ f g ≫ (X.H n₁).map (twoδ₂Toδ₁ f g fg h) = 0 := by
  subst h
  exact (X.exact₁' n₀ n₁ hn₁ (mk₂ f g)).zero 0

@[reassoc (attr := simp)]
lemma zero₂ (fg : i ⟶ k) (h : f ≫ g = fg) :
    (X.H n₀).map (twoδ₂Toδ₁ f g fg h) ≫ (X.H n₀).map (twoδ₁Toδ₀ f g fg h) = 0 := by
  subst h
  exact (X.exact₂' n₀ (mk₂ f g)).zero 0

@[reassoc (attr := simp)]
lemma zero₃ :
    (X.H n₀).map (twoδ₁Toδ₀ f g fg h) ≫ X.δ n₀ n₁ hn₁ f g = 0 := by
  subst h
  exact (X.exact₃' n₀ n₁ hn₁ (mk₂ f g)).zero 0

/-- The (exact) short complex `H^n₀(g) ⟶ H^n₁(f) ⟶ H^n₁(fg)` of a
spectral object, when `f ≫ g = fg` and `n₀ + 1 = n₁`. -/
@[simps]
def sc₁ : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₁ n₀ n₁ hn₁ f g fg h)

/-- The (exact) short complex `H^n₀(f) ⟶ H^n₀(fg) ⟶ H^n₀(g)` of a
spectral object, when `f ≫ g = fg`. -/
@[simps]
def sc₂ : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₂ n₀ f g fg h)

/-- The (exact) short complex `H^n₀(fg) ⟶ H^n₀(g) ⟶ H^n₁(f)`
of a spectral object, when `f ≫ g = fg` and `n₀ + 1 = n₁`. -/
@[simps]
def sc₃ : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₃ n₀ n₁ hn₁ f g fg h)

lemma exact₁ : (X.sc₁ n₀ n₁ hn₁ f g fg h).Exact := by
  subst h
  exact (X.exact₁' n₀ n₁ hn₁ (mk₂ f g)).exact 0

lemma exact₂ : (X.sc₂ n₀ f g fg h).Exact := by
  subst h
  exact (X.exact₂' n₀ (mk₂ f g)).exact 0

lemma exact₃ : (X.sc₃ n₀ n₁ hn₁ f g fg h).Exact := by
  subst h
  exact ((X.exact₃' n₀ n₁ hn₁ (mk₂ f g))).exact 0

/-- The (exact) sequence
`H^n₀(f) ⟶ H^n₀(fg) ⟶ H^n₀(g) ⟶ H^n₁(f) ⟶ H^n₁(fg) ⟶ H^n₁(g)`
of a spectral object, when `f ≫ g = fg` and `n₀ + 1 = n₁`. -/
abbrev composableArrows₅ : ComposableArrows C 5 :=
  mk₅ ((X.H n₀).map (twoδ₂Toδ₁ f g fg h)) ((X.H n₀).map (twoδ₁Toδ₀ f g fg h))
    (X.δ n₀ n₁ hn₁ f g) ((X.H n₁).map (twoδ₂Toδ₁ f g fg h))
    ((X.H n₁).map (twoδ₁Toδ₀ f g fg h))

lemma composableArrows₅_exact :
    (X.composableArrows₅ n₀ n₁ hn₁ f g fg h).Exact :=
  exact_of_δ₀ (X.exact₂ n₀ _ _ _ h).exact_toComposableArrows
    (exact_of_δ₀ (X.exact₃ n₀ n₁ hn₁ _ _ _ h).exact_toComposableArrows
      (exact_of_δ₀ (X.exact₁ n₀ n₁ hn₁ _ _ _ h).exact_toComposableArrows
        ((X.exact₂ n₁ _ _ _ h).exact_toComposableArrows)))

end

@[reassoc (attr := simp)]
lemma δ_δ (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    {i j k l : ι} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l) :
    X.δ n₀ n₁ hn₁ g h ≫ X.δ n₁ n₂ hn₂ f g = 0 := by
  have eq := X.δ_naturality n₁ n₂ hn₂ f g f (g ≫ h) (𝟙 _) (twoδ₂Toδ₁ g h _ rfl)
  rw [Functor.map_id, comp_id] at eq
  rw [← eq, X.zero₁_assoc n₀ n₁ hn₁ g h _ rfl, zero_comp]

/-- The type of morphisms between spectral objects in abelian categories. -/
@[ext]
structure Hom (X' : SpectralObject C ι) where
  /-- The natural transformation that is part of a morphism between spectral objects. -/
  hom (n : ℤ) : X.H n ⟶ X'.H n
  comm (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) :
    X.δ n₀ n₁ hn₁ f g ≫ (hom n₁).app (mk₁ f) =
    (hom n₀).app (mk₁ g) ≫ X'.δ n₀ n₁ hn₁ f g := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

@[simps]
instance : Category (SpectralObject C ι) where
  Hom := Hom
  id X := { hom _ := 𝟙 _ }
  comp f g := { hom n := f.hom n ≫ g.hom n }

attribute [simp] id_hom
attribute [reassoc, simp] comp_hom

end SpectralObject

end Abelian

end CategoryTheory
