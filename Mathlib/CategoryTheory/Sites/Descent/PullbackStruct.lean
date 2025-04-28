/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Chosen pullbacks

-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Limits

structure ChosenPullback {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) where
  pullback : C
  p₁ : pullback ⟶ X₁
  p₂ : pullback ⟶ X₂
  isPullback : IsPullback p₁ p₂ f₁ f₂

end Limits

end CategoryTheory
