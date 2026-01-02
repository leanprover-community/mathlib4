/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism
public import Mathlib.CategoryTheory.Monad.Adjunction


/-! # The monads and comonads associated to the pullback and pushforward adjunctions


-/


@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Adjunction MonoidalCategory ChosenPullbacksAlong ExponentiableMorphism


#check Over.pullback

variable {C : Type u₁} [Category.{v₁} C]
variable {I J : C} (g : I ⟶ J)

#check Over.pullback

abbrev mapPullbackMonad [ChosenPullbacksAlong g] : Monad (Over I) := mapPullbackAdj g |>.toMonad

abbrev pullbackPushforwardMonad [ChosenPullbacksAlong g] [ExponentiableMorphism g] :
    Monad (Over J) := pullbackAdjPushforward g |>.toMonad

-- without appealing to the comonadicity theorem we show that the functor
-- `Over.map g : Over I ⥤ Over J` is comonadic.

instance [ChosenPullbacksAlong g] : ComonadicLeftAdjoint (Over.map g) where
  R := pullback g
  adj := mapPullbackAdj g
  eqv := sorry


end CategoryTheory
