/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Instances.Real
import Mathlib.LinearAlgebra.Finrank
import Mathlib.Analysis.Convolution
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.SetTheory.Cardinal.CountableCover
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Data.Real.Cardinality
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# this is a test file

But the header is still correctly formatted to appease the linter
-/

set_option autoImplicit false

open LinearMap Set

open BigOperators Classical Convex Pointwise Filter

universe u v

open Filter Set

open scoped Cardinal Topology

lemma segment_inter_eq_endpoint_of_linearIndependent
    {E : Type _} [AddCommGroup E] [Module ℝ E] (x y : E) (h : LinearIndependent ℝ ![x, y])
    (s t : ℝ) (hs : s ≠ t) : [x -[ℝ]- t • y] ∩ [x -[ℝ]- s • y] ⊆ {x} := by
  intro z ⟨hzt, hzs⟩
  rw [segment_eq_image, mem_image] at hzt hzs
  rcases hzt with ⟨p, ⟨p0, p1⟩, rfl⟩
  rcases hzs with ⟨q, ⟨q0, q1⟩, H⟩
  simp only [smul_smul] at H
  obtain rfl : q = p := by simpa using (h.eq_of_pair H).1
  rcases q0.eq_or_gt with rfl|hq0'
  · simp
  · have A : s = t := by simpa [mul_eq_mul_left_iff, hq0'.ne'] using (h.eq_of_pair H).2
    exact (hs A).elim

lemma Cardinal.one_lt_two : (1 : Cardinal) < 2 := sorry

theorem glouglou {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : 2 ≤ Module.rank ℝ E) (x : E) (hx : x ≠ 0) :
    ∃ y, LinearIndependent ℝ ![x, y] := by
  have A : Submodule.span ℝ ({x}) ≠ ⊤ := by
    intro H
    have A : LinearIndependent ℝ ![x] := linearIndependent_unique ![x] hx
    have : Module.rank ℝ (⊤ : Submodule ℝ E) = 1 := by
      rw [← H]
      rw [rank_span_set (R := ℝ) (M := E) (s := {x})]
      · simp
      · apply linearIndependent_unique
        exact hx
    rw [← rank_top ℝ E, this] at h
    exact lt_irrefl _ (h.trans_lt Cardinal.one_lt_two)
  obtain ⟨y, hy⟩ : ∃ y, y ∉ Submodule.span ℝ ({x}) := by
    contrapose! A
    exact Submodule.eq_top_iff'.2 A



#exit


theorem glouglou {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : 2 ≤ Module.rank ℝ E) (x : E) (hx : x ≠ 0) :
    ∃ y, LinearIndependent ℝ ![x, y] := by
  have A : LinearIndependent ℝ ![x] := by
    exact linearIndependent_unique ![x] hx
  let B := Basis.sumExtend A



theorem glouglou1 {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] (s : Set E) (hs : s.Countable) : Dense sᶜ :=
  hs.dense_compl

theorem glouglou {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : 2 ≤ Module.rank ℝ E) (s : Set E) (hs : s.Countable) :
    IsPathConnected sᶜ := by
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_two.trans_le h)
  -- the set `sᶜ` is dense, therefore nonempty. Pick `x ∈ sᶜ`. We have to show that any
  -- `y ∈ sᶜ` can be joined to `x`.
  obtain ⟨x, hx⟩ : sᶜ.Nonempty := hs.dense_compl.nonempty
  refine ⟨x, hx, ?_⟩
  intro y hy
  rcases eq_or_ne x y with rfl|hxy
  · exact JoinedIn.refl hx
  have : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have : ∃ z, LinearIndependent ℝ ![y - x, z] := by
    exact?
