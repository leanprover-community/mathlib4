/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Topology.Instances.ENat
import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Topology.Order.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Topology lemma for `ENat.toENNReal`

This file shows `ENat.toENNReal` is a closed embedding.
-/

public section

namespace ENat

@[continuity]
theorem continuous_toENNReal : Continuous toENNReal := by
  refine OrderTopology.continuous_iff.mpr fun a ↦ ⟨?_, ?_⟩
  · simpa using isOpen_Ioi
  · simpa using isOpen_Iio

theorem isClosedEmbedding_toENNReal : Topology.IsClosedEmbedding toENNReal :=
  continuous_toENNReal.isClosedEmbedding toENNReal_strictMono.injective

end ENat
