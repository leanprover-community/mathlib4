/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Monad.Basic
import Mathlib.CategoryTheory.Bicategory.Adjunction
/-!
# Adjunctions and (co)monads in a bicategory

-/

namespace CategoryTheory

namespace Bicategory

universe w v u u₁

show_panel_widgets [local ProofWidgets.GoalTypePanel]

variable {B : Type u} [Bicategory.{w, v} B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}

/-- An adjunction `f ⊣ g` in a bicategory `B` gives rise to a monad in `B`. -/
def toMonad (adj : f ⊣ g) : Monad (f ≫ g) where
  mul := 𝟙 _ ⊗≫ f ◁ adj.counit ▷ g ⊗≫ 𝟙 _
  unit := adj.unit
  assoc := by
    calc
      _ = 𝟙 _ ⊗≫ f ◁ (adj.counit ▷ (g ≫ f) ≫ 𝟙 _ ◁ adj.counit) ▷ g ⊗≫ 𝟙 _ := by
        simp [bicategoricalComp]; coherence
      _ = 𝟙 _ ⊗≫ f ◁ ((g ≫ f) ◁ adj.counit ⊗≫ adj.counit ▷ (𝟙 _)) ▷ g ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; simp [bicategoricalComp]
      _ = _ := by
        simp [bicategoricalComp]; coherence
  left_unit := by
    calc
      _ = 𝟙 _ ⊗≫ (leftZigzag adj.unit adj.counit) ▷ g ⊗≫ 𝟙 _ := by
        rw [leftZigzag]
        simp [bicategoricalComp]
      _ = _ := by
        rw [adj.left_triangle]
        simp [bicategoricalComp]
  right_unit := by
    calc
      _ = 𝟙 _ ⊗≫ f ◁ (rightZigzag adj.unit adj.counit) ⊗≫ 𝟙 _ := by
        rw [rightZigzag]
        simp [bicategoricalComp]
      _ = _ := by
        rw [adj.right_triangle]
        simp [bicategoricalComp]


end Bicategory

end CategoryTheory
