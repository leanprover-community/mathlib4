import Mathlib.CategoryTheory.Monoidal.Mon_

open CategoryTheory MonoidalCategory
open scoped Mon_Class

variable {C : Type*} [Category C] [MonoidalCategory C] {M N : C} [Mon_Class M] [Mon_Class N]

example : η ▷ M ≫ μ = (λ_ M).hom := by simp only [mon_tauto]
example : M ◁ η ≫ μ = (ρ_ M).hom := by simp only [mon_tauto]
example : μ ▷ M ≫ μ = (α_ M M M).hom ≫ M ◁ μ ≫ μ := by simp only [mon_tauto]
example : M ◁ μ ≫ μ = (α_ M M M).inv ≫ μ ▷ M ≫ μ := by simp only [mon_tauto]

variable [BraidedCategory C] [IsCommMon M] [IsCommMon N]

example : (β_ M M).hom ≫ μ = μ := by simp only [mon_tauto]
example : (β_ M M).inv ≫ μ = μ := by simp only [mon_tauto]
example : tensorμ M M M M ≫ (μ ⊗ₘ μ) ≫ μ = (μ ⊗ₘ μ) ≫ μ := by simp only [mon_tauto]
example : tensorδ M M M M ≫ (μ ⊗ₘ μ) ≫ μ = (μ ⊗ₘ μ) ≫ μ := by simp only [mon_tauto]
