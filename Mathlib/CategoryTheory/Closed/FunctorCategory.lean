/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
/-!
# Functors into a complete monoidal closed category form a monoidal closed category.

-/

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
variable {I : Type u₂} [Category.{v₂} I]
  [∀ (F : Discrete I ⥤ C), (Discrete.functor id).HasRightKanExtension F]
  -- This implies the above:
  -- [HasLimitsOfSize.{u₂, max u₂ v₂} C]

example : (Discrete I ⥤ C) ⥤ (I ⥤ C) := Functor.ran (Discrete.functor id)




end CategoryTheory.Functor
