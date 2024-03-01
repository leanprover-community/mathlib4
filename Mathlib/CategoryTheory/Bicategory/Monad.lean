import Mathlib.CategoryTheory.Bicategory.Basic

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

structure Monad (b : B) where
  t (a : B) : a ⟶ a
  μ (a : B) : t a ≫ t a ⟶ t a
  η (a : B) : 𝟙 a ⟶ t a
  assoc : ∀ (a : B), μ a ▷ t a ≫ μ a = (α_ _ _ _).hom ≫ t a ◁ μ a ≫ μ a := by aesop_cat
  left_unit : ∀ (a : B), η a ▷ t a ≫ μ a = (λ_ (t a)).hom := by aesop_cat
  right_unit : ∀ (a : B), t a ◁ η a ≫ μ a = (ρ_ (t a)).hom := by aesop_cat

end Bicategory

end CategoryTheory
