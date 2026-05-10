/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Algebra.Order.Floor.Extended

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
  · have : toENNReal ⁻¹' Set.Iio a = Set.Iio ⌈a⌉ₑ := by ext; simp
    simpa using isOpen_Iio

theorem isClosedEmbedding_toENNReal : Topology.IsClosedEmbedding toENNReal :=
  continuous_toENNReal.isClosedEmbedding toENNReal_strictMono.injective

end ENat
