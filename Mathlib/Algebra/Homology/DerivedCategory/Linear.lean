/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Linear
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Shift.Linear
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
# The derived category of a linear abelian category is linear

-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated ZeroObject Preadditive

universe t w v u

variable (R : Type t) [Ring R] (C : Type u) [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory.{w} C]

namespace DerivedCategory

noncomputable instance : Linear R (DerivedCategory C) :=
  Localization.linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C)
    (HomotopyCategory.quasiIso C _)

instance : Functor.Linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C) :=
  Localization.functor_linear _ _ _

instance : Functor.Linear R (DerivedCategory.Q : _ ⥤ DerivedCategory C) :=
  Functor.linear_of_iso _ (quotientCompQhIso C)

instance (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Linear R :=
  Shift.linear_of_localization R Qh (HomotopyCategory.subcategoryAcyclic C).trW _

instance (n : ℤ) : Functor.Linear R (DerivedCategory.singleFunctor C n) :=
  inferInstanceAs (Functor.Linear R (HomotopyCategory.singleFunctor C n ⋙ Qh))

end DerivedCategory
