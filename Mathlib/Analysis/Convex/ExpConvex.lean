/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib

/-!
# Exponentially convex functions

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

variable {f : ℝ → ℝ} {s : Set ℝ} {x y : ℝ}

def IsExpConvexOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ (I : Finset ℝ) (ξ : ℝ → ℝ) (_ : ∀ i ∈ I, ∀ j ∈ I, i + j ∈ s),
    0 ≤ ∑ i ∈ I, ∑ j ∈ I, ξ i * f (i + j) * ξ j

lemma IsExpConvexOn.midpoint_convex (hf : IsExpConvexOn f s) (hx : x ∈ s) (hy : y ∈ s)
    (h : (2 : ℝ)⁻¹ * x + (2 : ℝ)⁻¹ * y ∈ s) :
    f ((2 : ℝ)⁻¹ * x + (2 : ℝ)⁻¹ * y) ≤ (2 : ℝ)⁻¹ * f x + (2 : ℝ)⁻¹ * f y := by
  by_cases hxy : x = y
  · simp only [hxy, smul_eq_mul]
    rw [← mul_add, ← two_mul, ← mul_assoc, inv_mul_cancel₀ two_pos.ne', one_mul,
      ← mul_add, ← two_mul, ← mul_assoc, inv_mul_cancel₀ two_pos.ne', one_mul]
  classical
  have h := hf {(2 : ℝ)⁻¹ * x, (2 : ℝ)⁻¹ * y} (fun z ↦ if z = (2 : ℝ)⁻¹ * x then 1 else -1) ?_
  swap
  · intros i hi j hj
    simp only [smul_eq_mul, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> rw [hi, hj]
    · rwa [← mul_add, ← two_mul, ← mul_assoc, inv_mul_cancel₀ two_pos.ne', one_mul]
    · exact h
    · rwa [add_comm]
    · rwa [← mul_add, ← two_mul, ← mul_assoc, inv_mul_cancel₀ two_pos.ne', one_mul]
  simp only [ite_mul, one_mul, neg_mul, mul_ite, mul_one, mul_neg] at h
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton, Finset.sum_singleton,
    Finset.sum_insert, Finset.sum_singleton] at h
  rotate_left
  · simp [hxy]
  · simp [hxy]
  · simp [hxy]
  simp only [↓reduceIte, mul_eq_mul_left_iff, inv_eq_zero, OfNat.ofNat_ne_zero, or_false,
    Ne.symm hxy, ↓reduceIte, neg_neg] at h
  simp_rw [← mul_add, ← two_mul, ← mul_assoc] at h ⊢
  rw [inv_mul_cancel₀ two_pos.ne', one_mul, one_mul, add_comm y] at h
  linarith

lemma IsExpConvexOn.convexOn (hf : IsExpConvexOn f s) (hs : Convex ℝ s) : ConvexOn ℝ s f := by
  have h x y (hx : x ∈ s) (hy : y ∈ s) :
      f ((2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • y) ≤ (2 : ℝ)⁻¹ • f x + (2 : ℝ)⁻¹ • f y := by
    simp only [smul_eq_mul]
    refine hf.midpoint_convex hx hy ?_
    refine hs hx hy (inv_pos.mpr two_pos).le (inv_pos.mpr two_pos).le ?_
    norm_num
  -- how can I get convexity from midpoint convexity?
  sorry
