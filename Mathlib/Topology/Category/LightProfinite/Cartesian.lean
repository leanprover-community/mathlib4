/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.CompHausLike.Cartesian
public import Mathlib.Topology.Category.LightProfinite.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Cartesian monoidal structure on `LightProfinite`

This file defines the cartesian monoidal structure on `LightProfinite` given by the type-theoretic
product.

-/

public section

universe u

open CategoryTheory Limits CompHausLike

namespace LightProfinite

instance : CartesianMonoidalCategory LightProfinite.{u} :=
  cartesianMonoidalCategory

end LightProfinite
