/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.NNRat.Order
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Nat

/-!
# Topology on the rational numbers

The structure of a metric space on `ℚ` is introduced in this file, induced from `ℝ`.
-/

open Filter Metric Set Topology

namespace Rat

instance : MetricSpace ℚ :=
  MetricSpace.induced (↑) Rat.cast_injective Real.metricSpace

theorem dist_eq (x y : ℚ) : dist x y = |(x : ℝ) - y| := rfl

@[norm_cast, simp]
theorem dist_cast (x y : ℚ) : dist (x : ℝ) y = dist x y :=
  rfl

theorem uniformContinuous_coe_real : UniformContinuous ((↑) : ℚ → ℝ) :=
  uniformContinuous_comap

theorem isUniformEmbedding_coe_real : IsUniformEmbedding ((↑) : ℚ → ℝ) :=
  isUniformEmbedding_comap Rat.cast_injective

theorem isDenseEmbedding_coe_real : IsDenseEmbedding ((↑) : ℚ → ℝ) :=
  isUniformEmbedding_coe_real.isDenseEmbedding Rat.denseRange_cast

theorem isEmbedding_coe_real : IsEmbedding ((↑) : ℚ → ℝ) :=
  isDenseEmbedding_coe_real.isEmbedding

theorem continuous_coe_real : Continuous ((↑) : ℚ → ℝ) :=
  uniformContinuous_coe_real.continuous

end Rat

@[norm_cast, simp]
theorem Nat.dist_cast_rat (x y : ℕ) : dist (x : ℚ) y = dist x y := by
  rw [← Nat.dist_cast_real, ← Rat.dist_cast]; congr

theorem Nat.isUniformEmbedding_coe_rat : IsUniformEmbedding ((↑) : ℕ → ℚ) :=
  isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one <| by simpa using Nat.pairwise_one_le_dist

theorem Nat.isClosedEmbedding_coe_rat : IsClosedEmbedding ((↑) : ℕ → ℚ) :=
  isClosedEmbedding_of_pairwise_le_dist zero_lt_one <| by simpa using Nat.pairwise_one_le_dist

@[norm_cast, simp]
theorem Int.dist_cast_rat (x y : ℤ) : dist (x : ℚ) y = dist x y := by
  rw [← Int.dist_cast_real, ← Rat.dist_cast]; congr

theorem Int.isUniformEmbedding_coe_rat : IsUniformEmbedding ((↑) : ℤ → ℚ) :=
  isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one <| by simpa using Int.pairwise_one_le_dist

theorem Int.isClosedEmbedding_coe_rat : IsClosedEmbedding ((↑) : ℤ → ℚ) :=
  isClosedEmbedding_of_pairwise_le_dist zero_lt_one <| by simpa using Int.pairwise_one_le_dist

namespace Rat

instance : NoncompactSpace ℚ := Int.isClosedEmbedding_coe_rat.noncompactSpace

theorem uniformContinuous_add : UniformContinuous fun p : ℚ × ℚ => p.1 + p.2 :=
  Rat.isUniformEmbedding_coe_real.isUniformInducing.uniformContinuous_iff.2 <| by
    simp only [Function.comp_def, Rat.cast_add]
    exact Real.uniformContinuous_add.comp
      (Rat.uniformContinuous_coe_real.prodMap Rat.uniformContinuous_coe_real)

theorem uniformContinuous_neg : UniformContinuous (@Neg.neg ℚ _) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun _ _ h => by simpa only [abs_sub_comm, dist_eq, cast_neg, neg_sub_neg] using h⟩

instance : IsUniformAddGroup ℚ :=
  IsUniformAddGroup.mk' Rat.uniformContinuous_add Rat.uniformContinuous_neg

instance : IsTopologicalAddGroup ℚ := inferInstance

instance : OrderTopology ℚ := induced_orderTopology _ Rat.cast_lt exists_rat_btwn

theorem uniformContinuous_abs : UniformContinuous (abs : ℚ → ℚ) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε, ε0, fun _ _ h =>
      lt_of_le_of_lt (by simpa [Rat.dist_eq] using abs_abs_sub_abs_le_abs_sub _ _) h⟩

instance : IsTopologicalRing ℚ := inferInstance

nonrec theorem totallyBounded_Icc (a b : ℚ) : TotallyBounded (Icc a b) := by
  simpa only [preimage_cast_Icc]
    using totallyBounded_preimage Rat.isUniformEmbedding_coe_real.isUniformInducing
      (totallyBounded_Icc (a : ℝ) b)

end Rat

namespace NNRat

instance : MetricSpace ℚ≥0 :=
  Subtype.metricSpace

set_option linter.style.commandStart false in
@[simp ←, push_cast]
lemma dist_eq (p q : ℚ≥0) : dist p q = dist (p : ℚ) (q : ℚ) := rfl

set_option linter.style.commandStart false in
@[simp ←, push_cast]
lemma nndist_eq (p q : ℚ≥0) : nndist p q = nndist (p : ℚ) (q : ℚ) := rfl

instance : IsTopologicalSemiring ℚ≥0 where
  toContinuousAdd := continuousAdd_induced Nonneg.coeRingHom
  toContinuousMul := continuousMul_induced Nonneg.coeRingHom

instance : ContinuousSub ℚ≥0 :=
  ⟨((continuous_subtype_val.fst'.sub continuous_subtype_val.snd').max
      continuous_const).subtype_mk _⟩

instance : OrderTopology ℚ≥0 := orderTopology_of_ordConnected (t := Set.Ici 0)
instance : ContinuousInv₀ ℚ≥0 := inferInstance

end NNRat
