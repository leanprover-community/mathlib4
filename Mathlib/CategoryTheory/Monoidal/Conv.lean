/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# The convolution monoid.

When `M : Comon_ C` and `N : Mon_ C`, the morphisms `M.X ⟶ N.X` form a monoid (in Type).
-/

universe v₁ u₁
namespace CategoryTheory
open MonoidalCategory
open Mon_Class Comon_Class
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/--
The morphisms in `C` between the underlying objects of a pair of bimonoids in `C` naturally has a
(set-theoretic) monoid structure. -/
def Conv (M N : C) : Type v₁ := M ⟶ N

namespace Conv

variable {M : C} {N : C} [Comon_Class M] [Mon_Class N]

instance : One (Conv M N) where
  one := ε[M] ≫ η[N]

theorem one_eq : (1 : Conv M N) = ε[M] ≫ η[N] := rfl

instance : Mul (Conv M N) where
  mul := fun f g => Δ[M] ≫ f ▷ M ≫ N ◁ g ≫ μ[N]

theorem mul_eq (f g : Conv M N) : f * g = Δ[M] ≫ f ▷ M ≫ N ◁ g ≫ μ[N] := rfl

instance : Monoid (Conv M N) where
  one_mul f := by simp [one_eq, mul_eq, ← whisker_exchange_assoc]
  mul_one f := by simp [one_eq, mul_eq, ← whisker_exchange_assoc]
  mul_assoc f g h := by
    simp only [mul_eq]
    simp only [comp_whiskerRight, whisker_assoc, Category.assoc,
      MonoidalCategory.whiskerLeft_comp]
    slice_lhs 7 8 =>
      rw [← whisker_exchange]
    slice_rhs 2 3 =>
      rw [← whisker_exchange]
    slice_rhs 1 2 =>
      rw [comul_assoc]
    slice_rhs 3 4 =>
      rw [← associator_naturality_left]
    slice_lhs 6 7 =>
      rw [← associator_inv_naturality_right]
    slice_lhs 8 9 =>
      rw [Mon_Class.mul_assoc]
    simp

end Conv

end CategoryTheory
