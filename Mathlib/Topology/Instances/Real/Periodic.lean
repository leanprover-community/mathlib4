/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Topological properties of periodic functions on ℝ
-/

public section

open Set Bornology

namespace Function

variable {α : Type*}

/-- A continuous, periodic function has compact range. -/
theorem Periodic.compact_of_continuous [TopologicalSpace α] {f : ℝ → α} {c : ℝ} (hp : Periodic f c)
    (hc : c ≠ 0) (hf : Continuous f) : IsCompact (range f) := by
  rw [← hp.image_uIcc hc 0]
  exact isCompact_uIcc.image hf

/-- A continuous, periodic function is bounded. -/
theorem Periodic.isBounded_of_continuous [PseudoMetricSpace α] {f : ℝ → α} {c : ℝ}
    (hp : Periodic f c) (hc : c ≠ 0) (hf : Continuous f) : IsBounded (range f) :=
  (hp.compact_of_continuous hc hf).isBounded

end Function
