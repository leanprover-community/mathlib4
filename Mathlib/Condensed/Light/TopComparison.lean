/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Light.Basic
public import Mathlib.Condensed.TopComparison
public import Mathlib.Topology.Category.LightProfinite.Limits
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
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
import Mathlib.Topology.Category.LightProfinite.EffectiveEpi
import Mathlib.Topology.MetricSpace.Bounded

/-!

# The functor from topological spaces to light condensed sets

We define the functor `topCatToLightCondSet : TopCat.{u} ⥤ LightCondSet.{u}`.

-/

public section

universe u

open CategoryTheory

/--
Associate to a `u`-small topological space the corresponding light condensed set, given by
`yonedaPresheaf`.
-/
noncomputable abbrev TopCat.toLightCondSet (X : TopCat.{u}) : LightCondSet.{u} :=
  toSheafCompHausLike.{u} _ X (fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)

/--
`TopCat.toLightCondSet` yields a functor from `TopCat.{u}` to `LightCondSet.{u}`.
-/
noncomputable abbrev topCatToLightCondSet : TopCat.{u} ⥤ LightCondSet.{u} :=
  topCatToSheafCompHausLike.{u} _ (fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)
