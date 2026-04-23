/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Subobject.WellPowered
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike

/-!
# The category of abelian groups is well-powered
-/

@[expose] public section


open CategoryTheory

universe u

namespace AddCommGrpCat

instance wellPowered_addCommGrp : WellPowered.{u} AddCommGrpCat.{u} :=
  wellPowered_of_equiv.{u} (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence

end AddCommGrpCat
