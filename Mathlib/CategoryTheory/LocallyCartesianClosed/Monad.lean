/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monad.Algebra


/-! # The monads and comonads associated to the pullback and pushforward adjunctions


-/


@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Adjunction MonoidalCategory ChosenPullbacksAlong ExponentiableMorphism Monad

#check Over.pullback

variable {C : Type u₁} [Category.{v₁} C]
variable {I J : C} (g : I ⟶ J)

#check Over.pullback

abbrev mapPullbackMonad [ChosenPullbacksAlong g] : Monad (Over I) :=
  mapPullbackAdj g |>.toMonad

abbrev mapPullbackComonad [ChosenPullbacksAlong g] : Comonad (Over J) :=
  mapPullbackAdj g |>.toComonad

abbrev pullbackPushforwardMonad [ChosenPullbacksAlong g] [ExponentiableMorphism g] :
    Monad (Over J) := pullbackAdjPushforward g |>.toMonad

-- without appealing to the comonadicity theorem we show that the functor
-- `Over.map g : Over I ⥤ Over J` is comonadic.

@[simps]
def mapPullbackMonadComparisonInverse [ChosenPullbacksAlong g] :
    (mapPullbackComonad g).Coalgebra ⥤ Over I where
  obj c := Over.mk (Y := c.A.left) (c.a.left ≫ (snd c.A.hom g))
  map {c c'} f := Over.homMk f.f.left
    (by rw [Over.mk_hom, ← Category.assoc, ← Over.comp_left, ← f.h, Over.comp_left]; cat_disch)

@[simps!]
def mapPullbackMonadComparisonEquivalence [ChosenPullbacksAlong g] :
    Over I ≌  (mapPullbackComonad g).Coalgebra where
  functor := Comonad.comparison (mapPullbackAdj g)
  inverse := mapPullbackMonadComparisonInverse g
  unitIso := {
    hom.app X := Over.homMk (𝟙 X.left) (by simp)
    inv.app X := Over.homMk (𝟙 X.left) (by simp)
  }
  counitIso := {
    hom.app c := by simp; sorry
    inv.app c := sorry
  }
  functor_unitIso_comp := sorry


instance [ChosenPullbacksAlong g] : ComonadicLeftAdjoint (Over.map g) where
  R := pullback g
  adj := mapPullbackAdj g
  eqv := Equivalence.isEquivalence_functor (mapPullbackMonadComparisonEquivalence g)


end CategoryTheory
