/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Subobject

#align_import algebra.category.Group.subobject from "leanprover-community/mathlib"@"29b834dfbba4ed1b7950628bbf5e69ab98c15b4c"

/-!
# The category of abelian groups is well-powered
-/


open CategoryTheory

universe u

namespace AddCommGrp

instance wellPowered_addCommGrp : WellPowered AddCommGrp.{u} :=
  wellPowered_of_equiv (forget₂ (ModuleCat.{u} ℤ) AddCommGrp.{u}).asEquivalence
set_option linter.uppercaseLean3 false in
#align AddCommGroup.well_powered_AddCommGroup AddCommGrp.wellPowered_addCommGrp

end AddCommGrp
