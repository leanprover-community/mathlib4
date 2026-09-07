module
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

open CategoryTheory Mathlib.Tactic BicategoryLike
open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)

example (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) :
    f ⊗≫ g = f ≫ (α_ _ _ _).inv ≫ g := by
  monoidal

example (f : Z ⟶ W) : (X ⊗ Y) ◁ f = (α_ _ _ _).hom ≫ X ◁ Y ◁ f ≫ (α_ _ _ _).inv := by
  monoidal

example : f ≫ g = f ≫ g := by
  monoidal

example : (f ⊗ₘ g) ▷ X = (α_ _ _ _).hom ≫ (f ⊗ₘ g ▷ X) ≫ (α_ _ _ _).inv := by
  monoidal

example {V₁ V₂ V₃ : C} (R : ∀ V₁ V₂ : C, V₁ ⊗ V₂ ⟶ V₂ ⊗ V₁) :
    R V₁ V₂ ▷ V₃ ⊗≫ V₂ ◁ R V₁ V₃ =
      R V₁ V₂ ▷ V₃ ≫ (α_ _ _ _).hom ⊗≫ 𝟙 _ ≫ V₂ ◁ R V₁ V₃ := by
  monoidal

/-- error: expression contains metavariables:
x ⊗ y ⊗ ?_ -/
#guard_msgs in
set_option pp.mvars false in
example {x y z w : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⊗ y ⊗ w ⟶ y ⊗ z ⊗ w)
    (η : f ⊗ₘ (g ▷ w) = h) :
    (f ⊗ₘ g) ▷ w = 𝟙 _ ⊗≫ h ⊗≫ 𝟙 _ := by
  calc
    (f ⊗ₘ g) ▷ w = 𝟙 _ ⊗≫ (f ⊗ₘ g ▷ _) ⊗≫ 𝟙 _ := by monoidal
      _ = 𝟙 _ ⊗≫ h ⊗≫ 𝟙 _ := by rw [η]
