/-
Copyright (c) 2024 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Emily Riehl, Nick Ward
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.Quasicategory.StrictSegal
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# The nerve of a category is a quasicategory

In `AlgebraicTopology.Quasicategory.StrictSegal`, we show that any
strict Segal simplicial set is a quasicategory.
In `AlgebraicTopology.SimplicialSet.StrictSegal`, we show that the nerve of a
category satisfies the strict Segal condition.

In this file, we prove as a direct consequence that the nerve of a category is
a quasicategory.
-/

@[expose] public section

universe v u

open SSet

namespace CategoryTheory.Nerve

/-- By virtue of satisfying the `StrictSegal` condition, the nerve of a
category is a `Quasicategory`. -/
instance quasicategory {C : Type u} [Category.{v} C] : Quasicategory (nerve C) := inferInstance

end CategoryTheory.Nerve
