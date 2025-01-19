/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Defs

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

variable {α : Type*} {f : α → ℝ} {s : Set α} {x y : α}

def IsExpConvexOn [Add α] (f : α → ℝ) (s : Set α) : Prop :=
  ∀ (I : Finset α) (ξ : α → ℝ) (_ : ∀ i ∈ I, ∀ j ∈ I, i + j ∈ s),
    0 ≤ ∑ i ∈ I, ∑ j ∈ I, ξ i * f (i + j) * ξ j

lemma todo [AddCommMonoid α] [Module ℝ α] (hf : IsExpConvexOn f s) (hx : x ∈ s) (hy : y ∈ s)
    (h : (2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • y ∈ s) :
    f ((2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • y) ≤ (2 : ℝ)⁻¹ • f x + (2 : ℝ)⁻¹ • f y := by
  by_cases hxy : x = y
  · simp only [hxy, smul_eq_mul]
    sorry
  classical
  have h := hf {(2 : ℝ)⁻¹ • x, (2 : ℝ)⁻¹ • y} (fun _ ↦ 1) ?_
  swap
  · sorry
  simp only [one_mul, mul_one] at h
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton, Finset.sum_singleton,
    Finset.sum_insert, Finset.sum_singleton] at h
  rotate_left
  · simp only [Finset.mem_singleton]
    sorry
  · simp only [Finset.mem_singleton]
    sorry
  · simp only [Finset.mem_singleton]
    sorry
  sorry
