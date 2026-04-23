/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Module
public import Mathlib.CategoryTheory.Sites.Coherent.Comparison
public import Mathlib.Topology.Category.CompHaus.EffectiveEpi
public import Mathlib.Topology.Category.CompHaus.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
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

# Limits in categories of condensed objects

This file adds some instances for limits in condensed sets and condensed modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits

instance : HasLimits CondensedSet.{u} := by
  change HasLimits (Sheaf _ _)
  infer_instance

instance : HasLimitsOfSize.{u, u + 1} CondensedSet.{u} :=
  hasLimitsOfSizeShrink.{u, u + 1, u + 1, u} _

variable (R : Type (u + 1)) [Ring R]

instance : HasLimits (CondensedMod.{u} R) :=
  inferInstanceAs (HasLimits (Sheaf _ _))

instance : HasColimits (CondensedMod.{u} R) :=
  inferInstanceAs (HasColimits (Sheaf _ _))

instance : HasLimitsOfSize.{u, u + 1} (CondensedMod.{u} R) :=
  hasLimitsOfSizeShrink.{u, u + 1, u + 1, u} _

instance {A J : Type*} [Category* A] [Category* J] [HasColimitsOfShape J A]
    [HasWeakSheafify (coherentTopology CompHaus.{u}) A] :
    HasColimitsOfShape J (Condensed.{u} A) :=
  inferInstanceAs (HasColimitsOfShape J (Sheaf _ _))

instance {A J : Type*} [Category* A] [Category* J] [HasLimitsOfShape J A] :
    HasLimitsOfShape J (Condensed.{u} A) :=
  inferInstanceAs (HasLimitsOfShape J (Sheaf _ _))

instance {A : Type*} [Category* A] [HasFiniteLimits A] : HasFiniteLimits (Condensed.{u} A) :=
  inferInstanceAs (HasFiniteLimits (Sheaf _ _))

instance {A : Type*} [Category* A] [HasFiniteColimits A]
    [HasWeakSheafify (coherentTopology CompHaus.{u}) A] : HasFiniteColimits (Condensed.{u} A) :=
  inferInstanceAs (HasFiniteColimits (Sheaf _ _))
