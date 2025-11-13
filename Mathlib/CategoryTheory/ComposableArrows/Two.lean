/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# API for compositions of two arrows

Given morphisms `f : i ⟶ j`, `g : j ⟶ k`, and `fg : i ⟶ k` such that `f ≫ g = fg`
(which may arise from a term in `ComposableArrows C 2`), we define
maps `twoδ₂Toδ₁ : mk₁ f ⟶ mk₁ fg` and `twoδ₁Toδ₀ : mk₁ fg ⟶ mk₁ g` in
the category `ComposableArrows C 1`.

-/

universe v u

namespace CategoryTheory

namespace ComposableArrows

variable {C : Type u} [Category.{v} C]
  {i j k : C} (f : i ⟶ j) (g : j ⟶ k) (fg : i ⟶ k) (h : f ≫ g = fg)

/-- The morphism `mk₁ f ⟶ mk₁ fg` when `f ≫ g = fg` for some morphism `g`. -/
def twoδ₂Toδ₁ :
    mk₁ f ⟶ mk₁ fg :=
  homMk₁ (𝟙 _) g (by simpa using h)

@[simp]
lemma twoδ₂Toδ₁_app_zero :
    (twoδ₂Toδ₁ f g fg h).app 0 = 𝟙 _ := rfl

@[simp]
lemma twoδ₂Toδ₁_app_one :
    (twoδ₂Toδ₁ f g fg h).app 1 = g := rfl

/-- The morphism `mk₁ fg ⟶ mk₁ g` when `f ≫ g = fg` for some morphism `f`. -/
def twoδ₁Toδ₀ :
    mk₁ fg ⟶ mk₁ g :=
  homMk₁ f (𝟙 _) (by simpa using h.symm)

@[simp]
lemma twoδ₁Toδ₀_app_zero :
    (twoδ₁Toδ₀ f g fg h).app 0 = f := rfl

@[simp]
lemma twoδ₁Toδ₀_app_one :
    (twoδ₁Toδ₀ f g fg h).app 1 = 𝟙 _ := rfl

end ComposableArrows

end CategoryTheory
