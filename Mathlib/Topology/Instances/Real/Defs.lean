/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Int

/-!
# Topological properties of ℝ
-/

assert_not_exists UniformContinuousConstSMul UniformOnFun

noncomputable section

open Filter Int Metric Set TopologicalSpace Bornology
open scoped Topology Uniformity Interval

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

instance : NoncompactSpace ℝ := Int.isClosedEmbedding_coe_real.noncompactSpace

theorem Real.uniformContinuous_add : UniformContinuous fun p : ℝ × ℝ => p.1 + p.2 :=
  Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abs ε0
    ⟨δ, δ0, fun _ _ h =>
      let ⟨h₁, h₂⟩ := max_lt_iff.1 h
      Hδ h₁ h₂⟩

theorem Real.uniformContinuous_neg : UniformContinuous (@Neg.neg ℝ _) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun _ _ h => by simpa only [abs_sub_comm, Real.dist_eq, neg_sub_neg] using h⟩

-- short-circuit type class inference
instance : IsTopologicalAddGroup ℝ := by infer_instance
instance : IsTopologicalRing ℝ := inferInstance
instance : TopologicalDivisionRing ℝ := inferInstance

instance : ProperSpace ℝ where
  isCompact_closedBall x r := by
    rw [Real.closedBall_eq_Icc]
    apply isCompact_Icc

instance : SecondCountableTopology ℝ := secondCountable_of_proper

instance Real.instCompleteSpace : CompleteSpace ℝ := by
  apply complete_of_cauchySeq_tendsto
  intro u hu
  let c : CauSeq ℝ abs := ⟨u, Metric.cauchySeq_iff'.1 hu⟩
  refine ⟨c.lim, fun s h => ?_⟩
  rcases Metric.mem_nhds_iff.1 h with ⟨ε, ε0, hε⟩
  have := c.equiv_lim ε ε0
  simp only [mem_map, mem_atTop_sets, mem_setOf_eq]
  exact this.imp fun N hN n hn => hε (hN n hn)
