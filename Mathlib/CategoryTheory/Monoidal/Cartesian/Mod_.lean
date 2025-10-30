/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Mod_

/-!
# Additional results about module objects in Cartesian monoidal categories
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local simp] leftUnitor_hom

/-- Every object is a module over a monoid object via the trivial action. -/
@[reducible] def ModObj.trivialAction (M : C) [MonObj M] (X : C) :
    ModObj M X where
  smul := snd M X

@[deprecated (since := "2025-09-14")] alias Mod_Class.trivialAction := ModObj.trivialAction

attribute [local instance] ModObj.trivialAction in
/-- Every object is a module over a monoid object via the trivial action. -/
@[simps]
def Mod_.trivialAction (M : Mon C) (X : C) : Mod_ C M.X where
  X := X

end CategoryTheory
