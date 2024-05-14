/-
Copyright (c) 2024 Kalle Kytölä
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Bounded operations

This file introduces type classes for bornologically bounded operations.

In particular, when combined with type classes which guarantee continuity of the same operations,
we can equip bounded continuous functions with the corresponding operations.

## Main definitions

* `BoundedSub R`: a class guaranteeing boundedness of subtraction.

TODO:
* Add bounded multiplication. (So that, e.g., multiplication works in `X →ᵇ ℝ≥0`.)

-/

section bounded_sub
/-!
### Bounded subtraction
-/

open Pointwise

/-- A typeclass saying that `(p : R × R) ↦ p.1 - p.2` maps any pair of bounded sets to a bounded
set. This property automatically holds for seminormed additive groups, but it also holds, e.g.,
for `ℝ≥0`. -/
class BoundedSub (R : Type*) [Bornology R] [Sub R] : Prop where
  isBounded_sub : ∀ {s t : Set R},
    Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s - t)

variable {R : Type*}

lemma isBounded_sub [Bornology R] [Sub R] [BoundedSub R] {s t : Set R}
    (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) :
    Bornology.IsBounded (s - t) := BoundedSub.isBounded_sub hs ht

lemma sub_bounded_of_bounded_of_bounded {X : Type*} [PseudoMetricSpace R] [Sub R] [BoundedSub R]
    {f g : X → R} (f_bdd : ∃ C, ∀ x y, dist (f x) (f y) ≤ C)
    (g_bdd : ∃ C, ∀ x y, dist (g x) (g y) ≤ C) :
    ∃ C, ∀ x y, dist ((f - g) x) ((f - g) y) ≤ C := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp <|
    isBounded_sub (Metric.isBounded_range_iff.mpr f_bdd) (Metric.isBounded_range_iff.mpr g_bdd)
  use C
  intro x y
  exact hC (Set.sub_mem_sub (Set.mem_range_self (f := f) x) (Set.mem_range_self (f := g) x))
           (Set.sub_mem_sub (Set.mem_range_self (f := f) y) (Set.mem_range_self (f := g) y))

end bounded_sub

section SeminormedAddCommGroup
/-!
### Bounded operations in seminormed additive commutative groups
-/

variable {R : Type*} [SeminormedAddCommGroup R]

lemma SeminormedAddCommGroup.lipschitzWith_sub :
    LipschitzWith 2 (fun (p : R × R) ↦ p.1 - p.2) := by
  convert LipschitzWith.prod_fst.sub LipschitzWith.prod_snd
  norm_num

instance : BoundedSub R where
  isBounded_sub := by
    intro s t hs ht
    rw [Metric.isBounded_iff] at hs ht ⊢
    obtain ⟨Cf, hf⟩ := hs
    obtain ⟨Cg, hg⟩ := ht
    use Cf + Cg
    intro z hz w hw
    obtain ⟨x₁, hx₁, y₁, hy₁, z_eq⟩ := Set.mem_sub.mp hz
    obtain ⟨x₂, hx₂, y₂, hy₂, w_eq⟩ := Set.mem_sub.mp hw
    rw [← w_eq, ← z_eq, dist_eq_norm]
    calc  ‖x₁ - y₁ - (x₂ - y₂)‖
     _  = ‖x₁ - x₂ + (y₂ - y₁)‖     := by
        rw [sub_sub_sub_comm, sub_eq_add_neg, neg_sub]
     _  ≤ ‖x₁ - x₂‖ + ‖y₂ - y₁‖     := norm_add_le _ _
     _  ≤ Cf + Cg                   :=
        add_le_add (mem_closedBall_iff_norm.mp (hf hx₁ hx₂))
                   (mem_closedBall_iff_norm.mp (hg hy₂ hy₁))

end SeminormedAddCommGroup

section NNReal
/-!
### Bounded operations in ℝ≥0
-/

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
