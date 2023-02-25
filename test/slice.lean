import Mathlib.Tactic.Slice

open CategoryTheory

variable (C : Type) [Category C] (X Y Z W U : C)
variable (f₁ f₂ : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (l : W ⟶ U)

example (h₁ : f₁ = f₂) : f₁ ≫ g ≫ h ≫ l = ((f₂ ≫ g) ≫ h) ≫ l := by
  conv =>
    lhs
    slice 1 4
  conv =>
    lhs
    slice 1 1
    rw [h₁]

example (h₁ : f₁ = f₂) : f₁ ≫ g ≫ h ≫ l = ((f₂ ≫ g) ≫ h) ≫ l := by
  slice_lhs 1 1 => rw [h₁]

example (h₁ : f₁ = f₂) : ((f₂ ≫ g) ≫ h) ≫ l = f₁ ≫ g ≫ h ≫ l := by
  slice_rhs 1 1 => rw [h₁]
