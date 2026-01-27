/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# API for compositions of three arrows

Given morphisms `f₁ : i ⟶ j`, `f₂ : j ⟶ k`, `f₃ : k ⟶ l`, and their
compositions `f₁₂ : i ⟶ k` and `f₂₃ : j ⟶ l`, we define
maps `ComposableArrows.threeδ₃Toδ₂ : mk₂ f₁ f₂ ⟶ mk₂ f₁ f₂₃`,
`threeδ₂Toδ₁ : mk₂ f₁ f₂₃ ⟶ mk₂ f₁₂ f₃`, and `threeδ₁Toδ₀ : mk₂ f₁₂ f₃ ⟶ mk₂ f₂ f₃`.
The names are justified by the fact that `ComposableArrow.mk₃ f₁ f₂ f₃`
can be thought of as a `3`-simplex in the simplicial set `nerve C`,
and its faces (numbered from `0` to `3`) are respectively
`mk₂ f₂ f₃`, `mk₂ f₁₂ f₃`, `mk₂ f₁ f₂₃`, `mk₂ f₁ f₂`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace ComposableArrows

section

variable {C : Type u} [Category.{v} C]
  {i j k l : C} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (f₂₃ : j ⟶ l)

/-- The morphism `mk₂ f₁ f₂ ⟶ mk₂ f₁ f₂₃` when `f₂ ≫ f₃ = f₂₃`. -/
def threeδ₃Toδ₂ (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch) :
    mk₂ f₁ f₂ ⟶ mk₂ f₁ f₂₃ :=
  homMk₂ (𝟙 _) (𝟙 _) f₃

/-- The morphism `mk₂ f₁ f₂₃ ⟶ mk₂ f₁₂ f₃` when `f₁ ≫ f₂ = f₁₂` and `f₂ ≫ f₃ = f₂₃`. -/
def threeδ₂Toδ₁ (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch) (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch) :
    mk₂ f₁ f₂₃ ⟶ mk₂ f₁₂ f₃ :=
  homMk₂ (𝟙 _) f₂ (𝟙 _)

/-- The morphism `mk₂ f₁₂ f₃ ⟶ mk₂ f₂ f₃` when `f₁ ≫ f₂ = f₁₂`. -/
def threeδ₁Toδ₀ (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch) :
    mk₂ f₁₂ f₃ ⟶ mk₂ f₂ f₃ :=
  homMk₂ f₁ (𝟙 _) (𝟙 _)

variable (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)

@[simp]
lemma threeδ₃Toδ₂_app_zero :
    (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃).app 0 = 𝟙 _ := rfl

@[simp]
lemma threeδ₃Toδ₂_app_one :
    (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃).app 1 = 𝟙 _ := rfl

@[simp]
lemma threeδ₃Toδ₂_app_two :
    (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃).app 2 = f₃ := rfl

@[simp]
lemma threeδ₂Toδ₁_app_zero :
    (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃).app 0 = 𝟙 _ := rfl

@[simp]
lemma threeδ₂Toδ₁_app_one :
    (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃).app 1 = f₂ := rfl

@[simp]
lemma threeδ₂Toδ₁_app_two :
    (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃).app 2 = 𝟙 _ := rfl

@[simp]
lemma threeδ₁Toδ₀_app_zero :
    (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂).app 0 = f₁ := rfl

@[simp]
lemma threeδ₁Toδ₀_app_one :
    (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂).app 1 = (𝟙 _) := rfl

@[simp]
lemma threeδ₁Toδ₀_app_two :
    (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂).app 2 = (𝟙 _) := rfl

end

section

variable {ι : Type*} [Preorder ι]
    (i₀ i₁ i₂ i₃ : ι) (hi₀₁ : i₀ ≤ i₁) (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃)

/-- Variant of `threeδ₃Toδ₂` for preorders. -/
abbrev threeδ₃Toδ₂' :
    mk₂ (homOfLE hi₀₁) (homOfLE hi₁₂) ⟶
      mk₂ (homOfLE hi₀₁) (homOfLE (hi₁₂.trans hi₂₃)) :=
  threeδ₃Toδ₂ _ _ (homOfLE hi₂₃) _ rfl

/-- Variant of `threeδ₂Toδ₁` for preorders. -/
abbrev threeδ₂Toδ₁' :
    mk₂ (homOfLE hi₀₁) (homOfLE (hi₁₂.trans hi₂₃)) ⟶
      mk₂ (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE hi₂₃) :=
  threeδ₂Toδ₁ _ (homOfLE hi₁₂) _ _ _ rfl rfl

/-- Variant of `threeδ₁Toδ₀` for preorders. -/
abbrev threeδ₁Toδ₀' :
    mk₂ (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE hi₂₃) ⟶
      mk₂ (homOfLE hi₁₂) (homOfLE hi₂₃) :=
  threeδ₁Toδ₀ (homOfLE hi₀₁) _ _ _ rfl

end

end ComposableArrows

end CategoryTheory
