/-
Copyright (c) 2024 Kalle Kytölä
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Bounded operations

This file introduces type classes for bornologically bounded operations. Together with type classes
which guarantee continuous operations, these enable to equip bounded continuous functions with the
respective operations, in particular.

## Main definitions

* `BoundedSub R`: a class guaranteeing boundedness of subtraction.

TODO:
* Add bounded multiplication. (So that, e.g., multiplication works in `X →ᵇ ℝ≥0`.)

-/

section bounded_sub

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

/-- A typeclass saying that `p : R × R ↦ r.1 - r.2` maps any pair of bounded sets to a bounded set.
This property automatically holds for seminormed additive groups, but it also holds, e.g.,
for `ℝ≥0`. -/
class BoundedSub (R : Type*) [Bornology R] [Sub R] : Prop where
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

instance [SeminormedAddCommGroup R] : BoundedSub R where
  isBounded_sub := by
    intro s t hs ht
    rw [Metric.isBounded_iff] at hs ht ⊢
    obtain ⟨Cf, hf⟩ := hs
    obtain ⟨Cg, hg⟩ := ht
    use Cf + Cg
    intro z hz w hw
    rw [Set.mem_sub] at hz hw
    obtain ⟨x₁, hx₁, y₁, hy₁, z_eq⟩ := hz
    obtain ⟨x₂, hx₂, y₂, hy₂, w_eq⟩ := hw
    rw [← w_eq, ← z_eq, dist_eq_norm]
    calc  ‖x₁ - y₁ - (x₂ - y₂)‖
     _  = ‖x₁ - x₂ + (y₂ - y₁)‖ := by
        congr
        rw [sub_sub_sub_comm, sub_eq_add_neg, neg_sub]
     _  ≤ ‖x₁ - x₂‖ + ‖y₂ - y₁‖ := norm_add_le _ _
     _  ≤ Cf + Cg               :=
        add_le_add (mem_closedBall_iff_norm.mp (hf hx₁ hx₂))
                   (mem_closedBall_iff_norm.mp (hg hy₂ hy₁))

section NNReal

open scoped NNReal

noncomputable instance : BoundedSub ℝ≥0 where
  isBounded_sub := by
    intro s t hs _
    obtain ⟨c, hc⟩ := (Metric.isBounded_iff_subset_ball 0).mp hs
    apply (Metric.isBounded_iff_subset_ball 0).mpr
    use c
    intro z hz
    obtain ⟨a, a_in_s, b, _, z_eq⟩ := Set.mem_sub.mp hz
    have key := hc a_in_s
    simp only [NNReal.ball_zero_eq_Ico, ← z_eq, Set.mem_Ico, zero_le, true_and, gt_iff_lt] at *
    exact tsub_lt_of_lt key

end NNReal

end bounded_sub
