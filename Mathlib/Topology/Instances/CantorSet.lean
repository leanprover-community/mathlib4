/-
Copyright (c) 2024 Jana Göken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artur Szafarczyk, Suraj Krishna M S, JB Stiegler, Isabelle Dubois,
Tomáš Jakl, Lorenzo Zanichelli, Alina Yan, Emilie Uthaiwat, Jana Göken
under guidance of Filippo A. E. Nuccio
-/
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Instances.Real

/-!
# Ternary Cantor Set
This file contains the definition of the Cantor ternary set
as well as some first properties, which will be updated later.

## Main Definitions
We give a definition for the ternary Cantor set in this file, which
is `cantorSet`.
-/

/-- We define the preCantorSet as the preimages under the iterations of some functions. -/
def preCantorSet : ℕ → Set ℝ
  | 0 => Set.Icc 0 1
  | Nat.succ n => (· / 3) '' preCantorSet n ∪ (fun x ↦ (2 + x) / 3)  '' preCantorSet n

/-- We define the Cantor set as the limit of all preCantorSets. -/
def cantorSet := iInf preCantorSet



/-!
## Simple Properties
-/

/-- The ternary Cantor set inherits the metric and in particular the topology from the reals. -/
instance cantorSet.metricSpace : MetricSpace cantorSet := Subtype.metricSpace


lemma quarters_mem_preCantorSet (n : ℕ) : 1/4 ∈ preCantorSet n ∧ 3/4 ∈ preCantorSet n := by
  induction n with
  | zero =>
    simp only [preCantorSet, Set.mem_Icc, inv_nonneg, Nat.ofNat_nonneg, true_and]
    refine ⟨⟨?_, ?_ ⟩,?_,?_⟩ <;> linarith

  | succ n ih =>
    apply And.intro
    · -- goal: 1 / 4 ∈ preCantorSet n
      exact Or.inl ⟨3/4, ih.2, by simp only; linarith ⟩

    · -- goal: 3 / 4 ∈ preCantorSet n
      exact Or.inr ⟨1/4, ih.1, by simp only; linarith ⟩

lemma quarter_mem_preCantorSet (n : ℕ) : 1/4 ∈ preCantorSet n := (quarters_mem_preCantorSet n).1

theorem quarter_mem_cantorSet : 1/4 ∈ cantorSet := by
  simp only [cantorSet,iInf, Set.sInf_eq_sInter, Set.sInter_range, Set.mem_iInter]
  exact quarter_mem_preCantorSet

lemma zero_mem_preCantorSet (n : ℕ) : 0 ∈ preCantorSet n := by
  induction n with
  | zero =>
    simp [preCantorSet]
  | succ n ih =>
    exact Or.inl ⟨0, ih, by simp only [zero_div]⟩

theorem zero_mem_cantorSet : 0 ∈ cantorSet := by
  simp only [cantorSet, iInf, Set.sInf_eq_sInter, Set.sInter_range, Set.mem_iInter]
  exact zero_mem_preCantorSet


/-- The ternary Cantor set is a subset of [0,1]. -/
lemma cantorSet_subset_unitInterval : cantorSet ⊆ Set.Icc 0 1 := by
  intro x hx
  simp only [cantorSet, Set.iInf_eq_iInter, Set.mem_iInter] at hx
  exact hx 0

/-- The ternary Cantor set is closed. -/
lemma isClosed_cantorSet : IsClosed cantorSet  := by
  let f := Homeomorph.mulLeft₀ (1/3:ℝ) (by norm_num)
  let g :=  (Homeomorph.addLeft (2:ℝ)).trans f
  apply isClosed_iInter
  intro n
  induction n with
  | zero =>
    exact isClosed_Icc
  | succ n ih =>
    refine IsClosed.union ?_ ?_
    · refine (ClosedEmbedding.closed_iff_image_closed ?succ.refine_1.hf).mp ih
      convert f.closedEmbedding using 2
      simp [f, div_eq_inv_mul]
    · refine (ClosedEmbedding.closed_iff_image_closed ?succ.refine_2.hf).mp ih
      convert  g.closedEmbedding using 2
      simp [g, f, div_eq_inv_mul]


/-- The ternary Cantor set is compact. -/
lemma isCompact_cantorSet : IsCompact cantorSet :=
  isCompact_Icc.of_isClosed_subset isClosed_cantorSet cantorSet_subset_unitInterval
