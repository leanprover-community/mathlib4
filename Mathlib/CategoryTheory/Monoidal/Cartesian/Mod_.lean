/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Mod_

/-!
# Additional results about module objects in cartesian monoidal categories
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local simp] leftUnitor_hom

/-- Every object is a module over a monoid object via the trivial action. -/
@[simps]
def Mod_.trivialAction (M : Mon_ C) (X : C) : Mod_ M where
  X := X
  smul := snd M.X X

/-- Every object is a module over a monoid object via the trivial action. -/
@[reducible] def Mod_Class.trivialAction (M : C) [Mon_Class M] (X : C) : Mod_Class M X where
  smul := snd M X
