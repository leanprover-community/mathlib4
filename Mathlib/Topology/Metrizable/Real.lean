/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.Real

/-!
# `ENNReal` is metrizable
-/

namespace ENNReal

open NNReal TopologicalSpace

instance : MetrizableSpace ENNReal :=
  orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.metrizableSpace

end ENNReal
