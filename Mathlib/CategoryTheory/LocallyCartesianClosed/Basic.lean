/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour and Emily Riehl
-/

import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Adjunction.Over

/-!
# Locally cartesian closed categories

There are several equivalent definitions of locally
cartesian closed categories.

1. A locally cartesian closed category is a category C such that all
the slices `Over I` are cartesian closed categories.

2. Equivalently, a locally cartesian closed category `C` is a category with pullbacks such that
each base change functor has a right adjoint, called the pushforward functor.

In this file we prove the equivalence of these conditions.

We also show that a locally cartesian closed category with a terminal object is cartesian closed.

-/

noncomputable section

namespace CategoryTheory

open CategoryTheory Category Limits Functor Adjunction Over

universe v u

variable {C : Type u} [Category.{v} C]

/-- A morphism `f : I ⟶ J` is exponentiable if the pullback functor `Over J ⥤ Over I`
has right adjoint. -/
class ExponentiableMorphism [HasPullbacks C] {I J : C} (f : I ⟶ J) where
  /-- The pushforward functor -/
  pushforward : Over I ⥤ Over J
  /-- The pushforward functor is right adjoint to the pullback functor -/
  adj : Over.pullback f ⊣ pushforward := by infer_instance

namespace ExponentiableMorphism




end ExponentiableMorphism















attribute [local instance] monoidalOfChosenFiniteProducts



section

variable (C : Type u) [Category.{v} C]

attribute [local instance] hasFiniteWidePullbacks_of_hasFiniteLimits
attribute [local instance] ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

class LCC (C : Type u) [Category.{v} C] [HasFiniteWidePullbacks C] where
  over_cc : Π (I : C), CartesianClosed (Over I)
  pushforward {X Y : C} (f : X ⟶ Y) : Over X ⥤ Over Y
  adj {X Y : C} (f : X ⟶ Y) : Over.pullback f ⊣ pushforward f := by infer_instance




end




end CategoryTheory
