/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.Types.Monomorphisms
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
# Monomorphisms of simplicial sets

In this file, we show that the class of monomorphisms in `SSet` is stable
under coproducts, pushouts, filtered colimits and transfinite compositions.

-/

@[expose] public section

universe v' u' u

open CategoryTheory Limits MorphismProperty

namespace SSet

instance [HasCoproducts.{v'} (Type u)] :
    IsStableUnderCoproducts.{v'} (monomorphisms SSet.{u}) :=
  inferInstanceAs (IsStableUnderCoproducts.{v'} (monomorphisms (_ ⥤ _)))

instance : (monomorphisms SSet).IsStableUnderCobaseChange := by
  change (monomorphisms (_ ⥤ _)).IsStableUnderCobaseChange
  rw [← functorCategory_monomorphisms]
  infer_instance

instance : MorphismProperty.IsStableUnderFilteredColimits.{u, u} (monomorphisms SSet.{u}) where
  isStableUnderColimitsOfShape J _ _ := by
    change (monomorphisms (_ ⥤ _)).IsStableUnderColimitsOfShape J
    rw [← functorCategory_monomorphisms]
    infer_instance

example (K : Type u) [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K] :
    (monomorphisms SSet.{u}).IsStableUnderTransfiniteCompositionOfShape K := by
  infer_instance

end SSet
