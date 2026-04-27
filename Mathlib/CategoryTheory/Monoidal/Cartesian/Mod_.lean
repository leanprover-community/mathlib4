/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod_

/-!
# Additional results about module objects in Cartesian monoidal categories
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local simp] leftUnitor_hom

/-- Every object is a module over a monoid object via the trivial action. -/
@[reducible] def ModObj.trivialAction (M : C) [MonObj M] (X : C) :
    ModObj M X where
  smul := snd M X

attribute [local instance] ModObj.trivialAction in
/-- Every object is a module over a monoid object via the trivial action. -/
@[simps]
def Mod.trivialAction (M : Mon C) (X : C) : Mod C M.X where
  X := X

@[deprecated (since := "2026-04-21")]
alias Mod_.trivialAction := Mod.trivialAction

end CategoryTheory
