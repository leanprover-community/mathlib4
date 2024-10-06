/-
Copyright (c) 2024 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import Mathlib.Topology.Instances.Nat

/-!
# Topology on the positive natural numbers

The structure of a metric space on `ℕ+` is introduced in this file, induced from `ℝ`.
-/

noncomputable section

open Metric

namespace PNat

instance : MetricSpace ℕ+ := inferInstanceAs (MetricSpace { n : ℕ // 0 < n })

theorem dist_eq (x y : ℕ+) : dist x y = |(↑x : ℝ) - ↑y| := rfl

@[simp, norm_cast]
theorem dist_coe (x y : ℕ+) : dist (↑x : ℕ) (↑y : ℕ) = dist x y := rfl

theorem uniformEmbedding_coe : UniformEmbedding ((↑) : ℕ+ → ℕ) := uniformEmbedding_subtype_val

instance : DiscreteTopology ℕ+ := inferInstanceAs (DiscreteTopology { n : ℕ // 0 < n })

instance : ProperSpace ℕ+ where
  isCompact_closedBall n r := by
    change IsCompact (((↑) : ℕ+ → ℕ) ⁻¹' closedBall (↑n : ℕ) r)
    rw [Nat.closedBall_eq_Icc]
    exact ((Set.finite_Icc _ _).preimage PNat.coe_injective.injOn).isCompact

instance : NoncompactSpace ℕ+ :=
  noncompactSpace_of_neBot <| by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

end PNat
