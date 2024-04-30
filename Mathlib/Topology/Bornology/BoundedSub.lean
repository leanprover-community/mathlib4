/-
Copyright (c) 2024 Kalle Kytölä
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Topology.ContinuousFunction.Bounded

variable {R : Type*}

lemma bounded_sub_iff_isBounded_image_sub [PseudoMetricSpace R] [Sub R] (s t : Set R) :
    (∃ κ, ∀ x₁ ∈ s, ∀ x₂ ∈ s, ∀ y₁ ∈ t, ∀ y₂ ∈ t, dist (x₁ - y₁) (x₂ - y₂) ≤ κ)
      ↔ (Bornology.IsBounded ((fun p ↦ p.fst - p.snd) '' s ×ˢ t)) := by
  rw [Metric.isBounded_iff]
  constructor <;> intro h
  · rcases h with ⟨c, hc⟩
    use c
    intro z ⟨p, ⟨p_mem_st, hpz⟩⟩ w ⟨q, ⟨q_mem_st, hqw⟩⟩
    simp only [Set.mem_prod] at p_mem_st q_mem_st
    simpa [hqw, hpz] using hc p.1 p_mem_st.1 q.1 q_mem_st.1 p.2 p_mem_st.2 q.2 q_mem_st.2
  · rcases h with ⟨c, hc⟩
    use c
    intro x₁ x₁_in_s x₂ x₂_in_s y₁ y₁_in_t y₂ y₂_in_t
    exact hc ⟨⟨x₁, y₁⟩, by aesop⟩ ⟨⟨x₂, y₂⟩, by aesop⟩

open Pointwise

class BoundedSub (R : Type*) [Bornology R] [Sub R] where
  isBounded_sub : ∀ {s t : Set R},
    Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s - t)

lemma isBounded_sub {R : Type*} [Bornology R] [Sub R] [BoundedSub R] {s t : Set R}
    (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t):
    Bornology.IsBounded (s - t) := BoundedSub.isBounded_sub hs ht

lemma sub_bounded_of_bounded_of_bounded {X : Type*} [PseudoMetricSpace R] [Sub R] [BoundedSub R]
    {f g : X → R} (f_bdd : ∃ C, ∀ x y, dist (f x) (f y) ≤ C)
    (g_bdd : ∃ C, ∀ x y, dist (g x) (g y) ≤ C) :
    ∃ C, ∀ x y, dist ((f - g) x) ((f - g) y) ≤ C := by
  obtain ⟨Cf, hf⟩ := f_bdd
  obtain ⟨Cg, hg⟩ := g_bdd
  have key := isBounded_sub (Metric.isBounded_range_iff.mpr ⟨Cf, hf⟩)
                            (Metric.isBounded_range_iff.mpr ⟨Cg, hg⟩)
  rw [Metric.isBounded_iff] at key
  obtain ⟨C, hC⟩ := key
  use C
  intro x y
  exact hC (Set.sub_mem_sub (Set.mem_range_self (f := f) x) (Set.mem_range_self (f := g) x))
           (Set.sub_mem_sub (Set.mem_range_self (f := f) y) (Set.mem_range_self (f := g) y))

lemma SeminormedAddCommGroup.lipschitzWith_sub [SeminormedAddCommGroup R] :
    LipschitzWith 2 (fun (p : R × R) ↦ p.1 - p.2) := by
  convert LipschitzWith.prod_fst.sub LipschitzWith.prod_snd
  norm_num

open scoped NNReal

lemma NNReal.closedBall_zero_eq_Icc' (c : ℝ≥0) :
    Metric.closedBall (0 : ℝ≥0) c.toReal = Set.Icc 0 c := by ext x; simp

lemma NNReal.closedBall_zero_eq_Icc {c : ℝ} (c_nn : 0 ≤ c) :
    Metric.closedBall (0 : ℝ≥0) c = Set.Icc 0 c.toNNReal := by
  convert NNReal.closedBall_zero_eq_Icc' ⟨c, c_nn⟩
  simp [Real.toNNReal, c_nn]

lemma NNReal.ball_zero_eq_Ico' (c : ℝ≥0) :
    Metric.ball (0 : ℝ≥0) c.toReal = Set.Ico 0 c := by ext x; simp

lemma NNReal.ball_zero_eq_Ico (c : ℝ) :
    Metric.ball (0 : ℝ≥0) c = Set.Ico 0 c.toNNReal := by
  by_cases c_pos : 0 < c
  · convert NNReal.ball_zero_eq_Ico' ⟨c, c_pos.le⟩
    simp [Real.toNNReal, c_pos.le]
  simp [not_lt.mp c_pos]

noncomputable instance : BoundedSub ℝ≥0 where
  isBounded_sub := by
    intro s t hs _
    obtain ⟨c, hc⟩ := (Metric.isBounded_iff_subset_ball 0).mp hs
    apply (Metric.isBounded_iff_subset_ball 0).mpr
    use c
    intro z hz
    obtain ⟨a, a_in_s, b, _, z_eq⟩ := Set.mem_sub.mp hz
    have key := hc a_in_s
    simp [NNReal.ball_zero_eq_Ico, ←z_eq] at *
    exact tsub_lt_of_lt key

open scoped BoundedContinuousFunction NNReal

instance instSub' {X R : Type*} [TopologicalSpace X] [PseudoMetricSpace R]
    [Sub R] [BoundedSub R] [ContinuousSub R] :
    Sub (X →ᵇ R) where
  sub f g :=
    { toFun := fun x ↦ (f x - g x),
      map_bounded' := sub_bounded_of_bounded_of_bounded f.map_bounded' g.map_bounded' }
