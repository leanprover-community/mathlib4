/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module algebra.category.Group.subobject
! leanprover-community/mathlib commit 29b834dfbba4ed1b7950628bbf5e69ab98c15b4c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.GroupCat.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Subobject

/-!
# The category of abelian groups is well-powered
-/


open CategoryTheory

universe u

namespace AddCommGroupCat

instance wellPowered_addCommGroupCat : WellPowered AddCommGroupCat.{u} :=
  wellPowered_of_equiv (forget₂ (ModuleCat.{u} ℤ) AddCommGroupCat.{u}).asEquivalence
set_option linter.uppercaseLean3 false in
#align AddCommGroup.well_powered_AddCommGroup AddCommGroupCat.wellPowered_addCommGroupCat

end AddCommGroupCat
