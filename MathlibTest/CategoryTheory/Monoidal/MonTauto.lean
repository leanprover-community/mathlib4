import Mathlib.CategoryTheory.Monoidal.Mon_

open CategoryTheory MonoidalCategory
open scoped MonObj

variable {C : Type*} [Category C] [MonoidalCategory C] {M N : C} [MonObj M] [MonObj N]

example : η ▷ M ≫ μ = (λ_ M).hom := by simp only [mon_tauto]
example : M ◁ η ≫ μ = (ρ_ M).hom := by simp only [mon_tauto]
example : μ ▷ M ≫ μ = (α_ M M M).hom ≫ M ◁ μ ≫ μ := by simp only [mon_tauto]
example : M ◁ μ ≫ μ = (α_ M M M).inv ≫ μ ▷ M ≫ μ := by simp only [mon_tauto]

example : M ◁ M ◁ ((ρ_ (M ⊗ M)).inv ≫ (M ⊗ M) ◁ η) ≫
    (α_ _ _ _).inv ≫ (M ⊗ M) ◁ (μ ▷ M) ≫ μ ▷ (M ⊗ M) ≫ M ◁ μ ≫ μ =
    (α_ _ _ _).inv ≫ (μ ⊗ₘ μ) ≫ μ := by
  simp only [mon_tauto]

example : (α_ (𝟙_ C) M M).hom ▷ M ≫ (α_ (𝟙_ C) (M ⊗ M) M).hom ≫ (𝟙_ C) ◁ (α_ M M M).hom ≫
    (λ_ _).hom ≫ M ◁ μ ≫ μ =
    (α_ ((𝟙_ C) ⊗ M) M M).hom ≫ (α_ (𝟙_ C) M (M ⊗ M)).hom ≫ (λ_ _).hom ≫ M ◁ μ ≫ μ := by
  simp only [mon_tauto]

example : (α_ M (𝟙_ _) (M ⊗ M)).hom ≫ M ◁ (λ_ (M ⊗ M)).hom ≫ M ◁ μ ≫ μ =
    (ρ_ M).hom ▷ (M ⊗ M) ≫ M ◁ μ ≫ μ := by
  simp only [mon_tauto]

example : M ◁ (λ_ (M ⊗ M)).inv ≫ (α_ M (𝟙_ _) (M ⊗ M)).inv ≫
    (ρ_ M).hom ▷ (M ⊗ M) ≫ _ ◁ μ ≫ μ = _ ◁ μ ≫ μ := by
  simp only [mon_tauto]

variable [BraidedCategory C] [IsCommMon M] [IsCommMon N]

example : (β_ M M).hom ≫ μ = μ := by simp only [mon_tauto]
example : (β_ M M).inv ≫ μ = μ := by simp only [mon_tauto]
example : tensorμ M M M M ≫ (μ ⊗ₘ μ) ≫ μ = (μ ⊗ₘ μ) ≫ μ := by simp only [mon_tauto]
example : tensorδ M M M M ≫ (μ ⊗ₘ μ) ≫ μ = (μ ⊗ₘ μ) ≫ μ := by simp only [mon_tauto]
