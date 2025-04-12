/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Monoidal.Mod_

/-!
# Additional results about module objects in cartesian monoidal categories
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

variable  {C : Type u₁} [Category.{v₁} C]  [ChosenFiniteProducts C]

/-- Every object is a module over a monoid object via the trivial action. -/
@[simps]
def Mod_.trivialAction (A : Mon_ C) (X : C) : Mod_ A where
  X := X
  act := ChosenFiniteProducts.snd A.X X

/-- Every object is a module over a monoid object via the trivial action. -/
def Mon_Class.trivialAction (M : C) [Mon_Class M] (S : C) : Mod_Class_ M S where
  smul := ChosenFiniteProducts.snd M S
