/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Analysis.Normed.Group.Lemmas
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Bounded operations

This file introduces type classes for bornologically bounded operations.

In particular, when combined with type classes which guarantee continuity of the same operations,
we can equip bounded continuous functions with the corresponding operations.

## Main definitions

* `BoundedAdd R`: a class guaranteeing boundedness of addition.
* `BoundedSub R`: a class guaranteeing boundedness of subtraction.
* `BoundedMul R`: a class guaranteeing boundedness of multiplication.

-/

open scoped NNReal

section bounded_add
/-!
### Bounded addition
-/

open Pointwise

/-- A typeclass saying that `(p : R × R) ↦ p.1 + p.2` maps any product of bounded sets to a bounded
set. This property follows from `LipschitzAdd`, and thus automatically holds, e.g., for seminormed
additive groups. -/
class BoundedAdd (R : Type*) [Bornology R] [Add R] : Prop where
  isBounded_add : ∀ {s t : Set R},
    Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s + t)

variable {R : Type*}

lemma isBounded_add [Bornology R] [Add R] [BoundedAdd R] {s t : Set R}
    (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) :
    Bornology.IsBounded (s + t) := BoundedAdd.isBounded_add hs ht

lemma add_bounded_of_bounded_of_bounded {X : Type*} [PseudoMetricSpace R] [Add R] [BoundedAdd R]
    {f g : X → R} (f_bdd : ∃ C, ∀ x y, dist (f x) (f y) ≤ C)
    (g_bdd : ∃ C, ∀ x y, dist (g x) (g y) ≤ C) :
    ∃ C, ∀ x y, dist ((f + g) x) ((f + g) y) ≤ C := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp <|
    isBounded_add (Metric.isBounded_range_iff.mpr f_bdd) (Metric.isBounded_range_iff.mpr g_bdd)
  use C
  intro x y
  exact hC (Set.add_mem_add (Set.mem_range_self (f := f) x) (Set.mem_range_self (f := g) x))
           (Set.add_mem_add (Set.mem_range_self (f := f) y) (Set.mem_range_self (f := g) y))

instance [PseudoMetricSpace R] [AddMonoid R] [LipschitzAdd R] : BoundedAdd R where
  isBounded_add {s t} s_bdd t_bdd := by
    have bdd : Bornology.IsBounded (s ×ˢ t) := Bornology.IsBounded.prod s_bdd t_bdd
    obtain ⟨C, add_lip⟩ := ‹LipschitzAdd R›.lipschitz_add
    convert add_lip.isBounded_image bdd
    ext p
    simp only [Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · intro ⟨a, a_in_s, b, b_in_t, eq_p⟩
      exact ⟨a, b, ⟨a_in_s, b_in_t⟩, eq_p⟩
    · intro ⟨a, b, ⟨a_in_s, b_in_t⟩, eq_p⟩
      simpa [← eq_p] using Set.add_mem_add a_in_s b_in_t

end bounded_add


section bounded_sub
/-!
### Bounded subtraction
-/

open Pointwise

/-- A typeclass saying that `(p : R × R) ↦ p.1 - p.2` maps any product of bounded sets to a bounded
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

lemma boundedSub_of_lipschitzWith_sub [PseudoMetricSpace R] [Sub R] {K : NNReal}
    (lip : LipschitzWith K (fun (p : R × R) ↦ p.1 - p.2)) :
    BoundedSub R where
  isBounded_sub {s t} s_bdd t_bdd := by
    have bdd : Bornology.IsBounded (s ×ˢ t) := Bornology.IsBounded.prod s_bdd t_bdd
    convert lip.isBounded_image bdd
    ext p
    simp only [Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · intro ⟨a, a_in_s, b, b_in_t, eq_p⟩
      exact ⟨a, b, ⟨a_in_s, b_in_t⟩, eq_p⟩
    · intro ⟨a, b, ⟨a_in_s, b_in_t⟩, eq_p⟩
      simpa [← eq_p] using Set.sub_mem_sub a_in_s b_in_t

end bounded_sub


section bounded_mul
/-!
### Bounded multiplication
-/

open Pointwise Set

/-- A typeclass saying that `(p : R × R) ↦ p.1 * p.2` maps any product of bounded sets to a bounded
set. This property automatically holds for non-unital seminormed rings, but it also holds, e.g.,
for `ℝ≥0`. -/
class BoundedMul (R : Type*) [Bornology R] [Mul R] : Prop where
  isBounded_mul : ∀ {s t : Set R},
    Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s * t)

variable {R : Type*}

lemma isBounded_mul [Bornology R] [Mul R] [BoundedMul R] {s t : Set R}
    (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) :
    Bornology.IsBounded (s * t) := BoundedMul.isBounded_mul hs ht

lemma isBounded_pow {R : Type*} [Bornology R] [Monoid R] [BoundedMul R] {s : Set R}
    (s_bdd : Bornology.IsBounded s) (n : ℕ) :
    Bornology.IsBounded ((fun x ↦ x ^ n) '' s) := by
  induction' n with n hn
  · by_cases s_empty : s = ∅
    · simp [s_empty]
    simp_rw [← nonempty_iff_ne_empty] at s_empty
    simp [s_empty]
  · have obs : ((fun x ↦ x ^ (n + 1)) '' s) ⊆ ((fun x ↦ x ^ n) '' s) * s := by
      intro x hx
      simp only [mem_image] at hx
      obtain ⟨y, y_in_s, ypow_eq_x⟩ := hx
      rw [← ypow_eq_x, pow_succ y n]
      apply Set.mul_mem_mul _ y_in_s
      use y
    exact (isBounded_mul hn s_bdd).subset obs

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

instance : BoundedSub R := boundedSub_of_lipschitzWith_sub SeminormedAddCommGroup.lipschitzWith_sub

end SeminormedAddCommGroup

section NonUnitalSeminormedRing
/-!
### Bounded operations in non-unital seminormed rings
-/

variable {R : Type*} [NonUnitalSeminormedRing R]

instance : BoundedMul R where
  isBounded_mul {s t} hs ht := by
    obtain ⟨Af, hAf⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hs
    obtain ⟨Ag, hAg⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp ht
    rw [Metric.isBounded_iff] at hs ht ⊢
    use 2 * Af * Ag
    intro z hz w hw
    obtain ⟨x₁, hx₁, y₁, hy₁, z_eq⟩ := Set.mem_mul.mp hz
    obtain ⟨x₂, hx₂, y₂, hy₂, w_eq⟩ := Set.mem_mul.mp hw
    rw [← w_eq, ← z_eq, dist_eq_norm]
    have hAf' : 0 ≤ Af := Metric.nonempty_closedBall.mp ⟨_, hAf hx₁⟩
    have aux : ∀ {x y}, x ∈ s → y ∈ t → ‖x * y‖ ≤ Af * Ag := by
      intro x y x_in_s y_in_t
      apply (norm_mul_le _ _).trans (mul_le_mul _ _ (norm_nonneg _) hAf')
      · exact mem_closedBall_zero_iff.mp (hAf x_in_s)
      · exact mem_closedBall_zero_iff.mp (hAg y_in_t)
    calc ‖x₁ * y₁ - x₂ * y₂‖
     _ ≤ ‖x₁ * y₁‖ + ‖x₂ * y₂‖        := norm_sub_le _ _
     _ ≤ Af * Ag + Af * Ag            := add_le_add (aux hx₁ hy₁) (aux hx₂ hy₂)
     _ = 2 * Af * Ag                  := by simp [← two_mul, mul_assoc]

end NonUnitalSeminormedRing

section NNReal
/-!
### Bounded operations in ℝ≥0
-/

instance : BoundedSub ℝ≥0 := boundedSub_of_lipschitzWith_sub NNReal.lipschitzWith_sub

open Metric in
instance : BoundedMul ℝ≥0 where
  isBounded_mul {s t} hs ht := by
    obtain ⟨Af, hAf⟩ := (isBounded_iff_subset_closedBall 0).mp hs
    obtain ⟨Ag, hAg⟩ := (isBounded_iff_subset_closedBall 0).mp ht
    have key : IsCompact (closedBall (0 : ℝ≥0) Af ×ˢ closedBall (0 : ℝ≥0) Ag) :=
      IsCompact.prod (isCompact_closedBall _ _) (isCompact_closedBall _ _)
    apply Bornology.IsBounded.subset (key.image continuous_mul).isBounded
    intro _ ⟨x, x_in_s, y, y_in_t, xy_eq⟩
    exact ⟨⟨x, y⟩, by simpa only [Set.mem_prod] using ⟨⟨hAf x_in_s, hAg y_in_t⟩, xy_eq⟩⟩

end NNReal
