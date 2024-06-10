/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.Transfer

/-!
# The category of sheaves of modules is abelian

-/

universe v v' u u'

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

namespace SheafOfModules

variable (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGroupCat.{v}]
  [J.WEqualsLocallyBijective AddCommGroupCat.{v}]

noncomputable instance : Abelian (SheafOfModules.{v} R) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.val)
  exact abelianOfAdjunction _ _ (asIso (adj.counit)) adj

end SheafOfModules
