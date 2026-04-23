/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf, Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Functors
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.Condensed.Epi
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
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
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!

# The functor from compact Hausdorff spaces to condensed sets preserves effective epimorphisms
-/

@[expose] public section

open CategoryTheory CompHausLike

universe u

instance : compHausToCondensed.PreservesEpimorphisms where
  preserves f hf := by
    rw [CondensedSet.epi_iff_locallySurjective_on_compHaus]
    intro S g
    refine ⟨pullback f g.down, pullback.snd _ _, fun y ↦ ?_, ⟨pullback.fst _ _⟩,
      ULift.ext _ _ <| pullback.condition _ _⟩
    rw [CompHaus.epi_iff_surjective] at hf
    obtain ⟨x, hx⟩ := hf (g.down.hom y)
    exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩

instance : IsRegularEpiCategory CondensedSet.{u} :=
  inferInstanceAs <| IsRegularEpiCategory (Sheaf _ _)

example : compHausToCondensed.PreservesEffectiveEpis := inferInstance
