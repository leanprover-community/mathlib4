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
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/--
The morphisms in `C` between the underlying objects of a pair of bimonoids in `C` naturally has a
(set-theoretic) monoid structure. -/
def Conv (M : Comon_ C) (N : Mon_ C) : Type v₁ := M.X ⟶ N.X

namespace Conv

variable {M : Comon_ C} {N : Mon_ C}

instance : One (Conv M N) where
  one := M.counit ≫ N.one

theorem one_eq : (1 : Conv M N) = M.counit ≫ N.one := rfl

instance : Mul (Conv M N) where
  mul := fun f g => M.comul ≫ f ▷ M.X ≫ N.X ◁ g ≫ N.mul

theorem mul_eq (f g : Conv M N) : f * g = M.comul ≫ f ▷ M.X ≫ N.X ◁ g ≫ N.mul := rfl

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
      rw [M.comul_assoc]
    slice_rhs 3 4 =>
      rw [← associator_naturality_left]
    slice_lhs 6 7 =>
      rw [← associator_inv_naturality_right]
    slice_lhs 8 9 =>
      rw [N.mul_assoc]
    simp

end Conv

end CategoryTheory
