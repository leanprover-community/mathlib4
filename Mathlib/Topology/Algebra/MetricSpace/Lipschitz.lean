/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz continuous functions

This file develops Lipschitz continuous functions further with some results that depend on algebra.
-/

@[expose] public section

assert_not_exists Module.Basis Ideal

open Filter Set NNReal Metric

variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}

lemma LipschitzWith.cauchySeq_comp {f : α → β} (hf : LipschitzWith K f) {u : ℕ → α}
    (hu : CauchySeq u) :
    CauchySeq (f ∘ u) := by
  rcases cauchySeq_iff_le_tendsto_0.1 hu with ⟨b, b_nonneg, hb, blim⟩
  refine cauchySeq_iff_le_tendsto_0.2 ⟨fun n ↦ K * b n, ?_, ?_, ?_⟩
  · exact fun n ↦ mul_nonneg (by positivity) (b_nonneg n)
  · exact fun n m N hn hm ↦ hf.dist_le_mul_of_le (hb n m N hn hm)
  · rw [← mul_zero (K : ℝ)]
    exact blim.const_mul _

lemma LipschitzOnWith.cauchySeq_comp {s : Set α} {f : α → β} (hf : LipschitzOnWith K f s)
    {u : ℕ → α} (hu : CauchySeq u) (h'u : range u ⊆ s) :
    CauchySeq (f ∘ u) := by
  rcases cauchySeq_iff_le_tendsto_0.1 hu with ⟨b, b_nonneg, hb, blim⟩
  refine cauchySeq_iff_le_tendsto_0.2 ⟨fun n ↦ K * b n, ?_, ?_, ?_⟩
  · exact fun n ↦ mul_nonneg (by positivity) (b_nonneg n)
  · intro n m N hn hm
    have A n : u n ∈ s := h'u (mem_range_self _)
    apply (hf.dist_le_mul _ (A n) _ (A m)).trans
    exact mul_le_mul_of_nonneg_left (hb n m N hn hm) K.2
  · rw [← mul_zero (K : ℝ)]
    exact blim.const_mul _

/-- If a function is locally Lipschitz around a point, then it is continuous at this point. -/
theorem continuousAt_of_locally_lipschitz {f : α → β} {x : α} {r : ℝ} (hr : 0 < r) (K : ℝ)
    (h : ∀ y, dist y x < r → dist (f y) (f x) ≤ K * dist y x) : ContinuousAt f x := by
  -- We use `h` to squeeze `dist (f y) (f x)` between `0` and `K * dist y x`
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    (mem_of_superset (ball_mem_nhds _ hr) h) ?_)
  -- Then show that `K * dist y x` tends to zero as `y → x`
  refine (continuous_const.mul (continuous_id.dist continuous_const)).tendsto' _ _ ?_
  simp

/-- If `f` is locally Lipschitz on a compact set `s`, it is Lipschitz on `s`. -/
lemma LocallyLipschitzOn.exists_lipschitzOnWith_of_compact {f : α → β} {s : Set α}
    (hs : IsCompact s) (hf : LocallyLipschitzOn s f) : ∃ K, LipschitzOnWith K f s := by
  /- `f` being locally Lipschitz on `s` means that it is continuous and that it is Lipschitz on a
  ball of some radius `ε x hx` within `s` with Lipschitz bound `K x hx` around every `x ∈ s`. -/
  have hf' := hf.continuousOn
  replace hf : ∀ x ∈ s, ∃ ε > 0, ∃ K, LipschitzOnWith K f (ball x ε ∩ s) := fun x hx ↦ by
    let ⟨K, t, ht, hf⟩ := hf hx
    let ⟨ε, hε, hε'⟩ := Metric.mem_nhdsWithin_iff.1 ht
    exact ⟨ε, hε, K, hf.mono hε'⟩
  choose ε hε K hf using hf
  /- We also have constants `K' x hx` for all `x ∈ s` such that `edist (f x) (f y) ≤ K' * edist x y`
  for all `y ∈ s` outside of `ball x (ε x hx)`, by continuity of
  `fun y ↦ dist (f x) (f y) / dist x y` on the compact set `s.diff (ball x (ε x hx))`. -/
  have (x) (hx : x ∈ s) : ∃ K' : ℝ≥0, ∀ y ∈ s.diff (ball x (ε x hx)),
      edist (f x) (f y) ≤ K' * edist x y := by
    let ⟨K', hK'⟩ := (hs.diff isOpen_ball).bddAbove_image
      (f := fun y ↦ dist (f x) (f y) / dist x y) <| .div (.mono (by fun_prop) s.diff_subset)
        (by fun_prop) fun y hy ↦ ((hε x hx).trans_le <| not_lt.1 <| dist_comm x y ▸ hy.2).ne'
    refine ⟨⟨K' ⊔ 0, le_sup_right⟩, fun y hy ↦ ?_⟩
    simp_rw [edist_nndist, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    refine (div_le_iff₀ ?_).1 ?_
    · exact NNReal.coe_pos.1 <| coe_nndist x y ▸
        ((hε x hx).trans_le <| not_lt.1 <| dist_comm x y ▸ hy.2)
    · simp [← NNReal.coe_le_coe, (mem_upperBounds.1 hK') _ <| mem_image_of_mem _ hy]
  choose K' hK' using this
  /- By compactness of `s`, there exists some finite set `t` such that the balls of radius
  `ε x hx / 2` around all `x ∈ t` cover `s`. -/
  obtain ⟨t, ht⟩ := hs.elim_nhdsWithin_subcover' (fun x hx ↦ s ∩ ball x (ε x hx / 2))
    (fun x hx ↦ inter_mem_nhdsWithin s <| ball_mem_nhds x <| half_pos <| hε x hx)
  /- For every `z ∈ t` we can show that `f` satisfies the Lipschitz condition with bound
  `K z hz + 2 * K' z hz` for all points `x ∈ s ∩ ball z (ε z hz / 2)` and `y ∈ s`, so `f` is
  Lipschitz on `s` with the supremum of these bounds over all `z ∈ t` as its bound. -/
  use t.sup fun i ↦ K _ i.2 + 2 * K' _ i.2
  intro x hx y hy
  let ⟨z, hz, hx'⟩ := mem_iUnion₂.1 <| ht hx
  by_cases hy' : y ∈ ball z.1 (ε _ z.2)
  · /- For `y ∈ ball z (ε z hz)` this follows from `f` being Lipschitz with bound `K z hz`
    on `ball z (ε z hz)`. -/
    refine (hf _ z.2 ⟨hx'.2.trans <| half_lt_self <| hε _ z.2, hx⟩ ⟨hy', hy⟩).trans <|
      mul_le_mul_of_nonneg_right ?_ <| zero_le _
    exact ENNReal.coe_le_coe.2 <| t.le_sup_of_le hz <| le_self_add
  · /- For `y ∉ ball z (ε z hz)` this follows by using the triangle inequality, bounding
    the distances from `f z` to `f x` and `f y` using the bounds `K z hz` and `K' z hz`, and then
    using the triangle inequality again for `edist z y ≤ edist x z + edist x y ≤ 2 * edist x y`. -/
    refine (edist_triangle_left _ _ (f z)).trans ?_
    refine .trans ?_ <| mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.2 <| t.le_sup hz) (zero_le _)
    refine (add_le_add (hf _ z.2 ⟨mem_ball_self <| hε _ z.2, z.2⟩ ⟨hx'.2.trans <| half_lt_self <|
      hε _ z.2, hx⟩) <| hK' _ z.2 _ ⟨hy, hy'⟩).trans ?_
    refine (add_le_add_right (mul_le_mul_of_nonneg_left (edist_triangle_left z.1 y x)
      (zero_le _)) _).trans ?_
    simp_rw [edist_dist, ENNReal.coe_nnreal_eq]
    rw [← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_add, ← ENNReal.ofReal_mul,
      ← ENNReal.ofReal_add, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat,
      mul_add, ← add_assoc, dist_comm, ← add_mul]
    · have h : dist x z ≤ dist x y := by
        linarith [mem_ball.1 hx'.2, (not_lt (α := ℝ)).1 hy', dist_triangle_left y z x]
      gcongr
      exact (add_le_add_left (mul_le_mul_of_nonneg_left h (by positivity)) _).trans (by linarith)
    all_goals positivity
