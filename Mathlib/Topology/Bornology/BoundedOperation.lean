/-
Copyright (c) 2024 Kalle Kytölä
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Bounded operations

This file introduces type classes for bornologically bounded operations.

In particular, when combined with type classes which guarantee continuity of the same operations,
we can equip bounded continuous functions with the corresponding operations.

## Main definitions

* `BoundedSub R`: a class guaranteeing boundedness of subtraction.
* `BoundedMul R`: a class guaranteeing boundedness of multiplication.

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


section bounded_mul
/-!
### Bounded multiplication
-/

open Pointwise

/-- A typeclass saying that `(p : R × R) ↦ p.1 * p.2` maps any pair of bounded sets to a bounded
set. This property automatically holds for non-unital seminormed rings, but it also holds, e.g.,
for `ℝ≥0`. -/
class BoundedMul (R : Type*) [Bornology R] [Mul R] : Prop where
  isBounded_mul : ∀ {s t : Set R},
    Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s * t)

variable {R : Type*}

lemma isBounded_mul [Bornology R] [Mul R] [BoundedMul R] {s t : Set R}
    (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) :
    Bornology.IsBounded (s * t) := BoundedMul.isBounded_mul hs ht

lemma mul_bounded_of_bounded_of_bounded {X : Type*} [PseudoMetricSpace R] [Mul R] [BoundedMul R]
    {f g : X → R} (f_bdd : ∃ C, ∀ x y, dist (f x) (f y) ≤ C)
    (g_bdd : ∃ C, ∀ x y, dist (g x) (g y) ≤ C) :
    ∃ C, ∀ x y, dist ((f * g) x) ((f * g) y) ≤ C := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp <|
    isBounded_mul (Metric.isBounded_range_iff.mpr f_bdd) (Metric.isBounded_range_iff.mpr g_bdd)
  use C
  intro x y
  exact hC (Set.mul_mem_mul (Set.mem_range_self (f := f) x) (Set.mem_range_self (f := g) x))
           (Set.mul_mem_mul (Set.mem_range_self (f := f) y) (Set.mem_range_self (f := g) y))

end bounded_mul

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

section NonUnitalSeminormedRing
/-!
### Bounded operations in non-unital seminormed rings
-/

variable {R : Type*} [NonUnitalSeminormedRing R]

instance : BoundedMul R where
  isBounded_mul := by
    intro s t hs ht
    obtain ⟨Af, hAf⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hs
    obtain ⟨Ag, hAg⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp ht
    rw [Metric.isBounded_iff] at hs ht ⊢
    use 2 * Af * Ag
    intro z hz w hw
    obtain ⟨x₁, hx₁, y₁, hy₁, z_eq⟩ := Set.mem_mul.mp hz
    obtain ⟨x₂, hx₂, y₂, hy₂, w_eq⟩ := Set.mem_mul.mp hw
    rw [← w_eq, ← z_eq, dist_eq_norm]
    by_cases absurd_Af : Af < 0
    · simpa [Metric.closedBall_eq_empty.mpr absurd_Af] using hAf hx₁
    simp only [not_lt] at absurd_Af
    have obs₁ : ‖x₁ * y₁‖ ≤ Af * Ag := by
      apply (norm_mul_le _ _).trans (mul_le_mul _ _ (norm_nonneg _) absurd_Af)
      · exact mem_closedBall_zero_iff.mp (hAf hx₁)
      · exact mem_closedBall_zero_iff.mp (hAg hy₁)
    have obs₂ : ‖x₂ * y₂‖ ≤ Af * Ag := by
      apply (norm_mul_le _ _).trans (mul_le_mul _ _ (norm_nonneg _) absurd_Af)
      · exact mem_closedBall_zero_iff.mp (hAf hx₂)
      · exact mem_closedBall_zero_iff.mp (hAg hy₂)
    calc ‖x₁ * y₁ - x₂ * y₂‖
     _ ≤ ‖x₁ * y₁‖ + ‖x₂ * y₂‖        := norm_sub_le _ _
     _ ≤ Af * Ag + Af * Ag            := add_le_add obs₁ obs₂
     _ = 2 * Af * Ag                  := by simp [← two_mul, mul_assoc]

end NonUnitalSeminormedRing

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

instance : BoundedMul ℝ≥0 where
  isBounded_mul := by
    intro s t hs ht
    obtain ⟨Af, hAf⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hs
    obtain ⟨Ag, hAg⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp ht
    rw [Metric.isBounded_iff]
    use 2 * Af * Ag
    intro z hz w hw
    obtain ⟨x₁, hx₁, y₁, hy₁, z_eq⟩ := Set.mem_mul.mp hz
    obtain ⟨x₂, hx₂, y₂, hy₂, w_eq⟩ := Set.mem_mul.mp hw
    rw [← w_eq, ← z_eq]
    by_cases absurd_Af : Af < 0
    · simpa [Metric.closedBall_eq_empty.mpr absurd_Af] using hAf hx₁
    simp only [not_lt] at absurd_Af
    have obs₁ : dist (x₁ * y₁) 0 ≤ Af * Ag := by
      have x_mem_ball := hAf hx₁
      have y_mem_ball := hAg hy₁
      simp only [Metric.mem_closedBall, NNReal.dist_eq, NNReal.coe_zero, sub_zero, NNReal.abs_eq,
                 NNReal.coe_mul, ge_iff_le, abs_mul] at x_mem_ball y_mem_ball ⊢
      apply mul_le_mul (by simpa using x_mem_ball) (by simpa using y_mem_ball) ?_ absurd_Af
      simp only [NNReal.zero_le_coe]
    have obs₂ : dist 0 (x₂ * y₂) ≤ Af * Ag := by
      have x_mem_ball := hAf hx₂
      have y_mem_ball := hAg hy₂
      simp only [Metric.mem_closedBall, NNReal.dist_eq, NNReal.coe_zero, sub_zero, NNReal.abs_eq,
                 NNReal.coe_mul, zero_sub, abs_neg, abs_mul, ge_iff_le] at x_mem_ball y_mem_ball ⊢
      apply mul_le_mul (by simpa using x_mem_ball) (by simpa using y_mem_ball) ?_ absurd_Af
      simp only [NNReal.zero_le_coe]
    calc dist (x₁ * y₁) (x₂ * y₂)
     _ ≤ dist (x₁ * y₁) 0 + dist 0 (x₂ * y₂)    := dist_triangle _ _ _
     _ ≤ Af * Ag + Af * Ag                      := add_le_add obs₁ obs₂
     _ = 2 * Af * Ag                            := by simp [← two_mul, mul_assoc]

end NNReal
