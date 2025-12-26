/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism
public import Mathlib.CategoryTheory.Monad.Adjunction


/-! # The monads and comonads associated to the pullback and pushforward adjunctions

- `mapPullbackMonad_η_app` shows that the unit of the `mapPullbackMonad` is a relative graph map.
-/


@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Adjunction MonoidalCategory ChosenPullbacksAlong


variable {C : Type u₁} [Category.{v₁} C]
variable {I J : C} (g : I ⟶ J) [ChosenPullbacksAlong g]

abbrev mapPullbackMonad : Monad (Over I) := mapPullbackAdj g |>.toMonad

theorem mapPullbackMonad_η :
    (mapPullbackMonad g).η = (mapPullbackAdj g |>.unit) := by
  rfl

end CategoryTheory
