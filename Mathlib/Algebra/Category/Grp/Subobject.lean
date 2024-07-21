/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Subobject

/-!
# The category of abelian groups is well-powered
-/


open CategoryTheory

universe u

namespace AddCommGrp

instance wellPowered_addCommGrp : WellPowered AddCommGrp.{u} :=
  wellPowered_of_equiv (forget₂ (ModuleCat.{u} ℤ) AddCommGrp.{u}).asEquivalence

end AddCommGrp
