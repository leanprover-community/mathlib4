/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang
-/
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Stongly convex functions from ℝⁿ to ℝ

In this file, we define the strongly convex functions and prove the basic properties
of a strongly convex function.
We prove the equivalent definitions for a strongly convex functions.
We prove the tighter bound for a strongly bound comparing with a general convex function.
We prove that if a strongly convex function admits a feasible global minima,
then the minima is unique.

## TODO

Add derivative information for a strongly convex functions, and prove some relevant properties.
Connect with L_smooth property and prove more theorems.
-/

variable {n : Type _} [Fintype n]

/-
Function f (x) is m - strongly convex iff
  f (x) - m * ‖x‖ ^ 2 / 2 is a convex function
-/

def Strongly_convex_on (s : Set (EuclideanSpace ℝ n)) (f : (EuclideanSpace ℝ n) → ℝ) : Prop :=
∃ (m : ℝ), m > 0 ∧ ConvexOn ℝ s (fun x ↦ f x - m / 2 * ‖x‖ ^ 2)

variable (s : Set (EuclideanSpace ℝ n)) {f : (EuclideanSpace ℝ n) → ℝ}

lemma equiv_lemma {x y : (EuclideanSpace ℝ n)} {o : ℝ} (h₁ : o > 0) (h₂ : o < 1):
o * (f x - m / 2 * ‖x‖ ^ 2) + (1 - o) * (f y - m / 2 * ‖y‖ ^ 2) + m / 2 * ‖o • x + (1 - o) • y‖ ^ 2 =
o * f x + (1 - o) * f y - m / 2 * o * (1 - o) * ‖x - y‖ ^ 2 :=
  calc o * (f x - m / 2 * ‖x‖ ^ 2) + (1 - o) * (f y - m / 2 * ‖y‖ ^ 2) + m / 2 * ‖o • x + (1 - o) • y‖ ^ 2
       _ = o * f x + (1 - o) * f y - m / 2 * o * (1 - o) * (‖x‖ ^ 2 - 2 * inner x y + ‖y‖^2) := by
          simp only [Real.rpow_two]
          rw [norm_add_sq_real (o • x), norm_smul, norm_smul, real_inner_smul_left, inner_smul_right]
          simp; rw [abs_of_pos (by linarith), abs_of_pos (by linarith), mul_pow, mul_pow]
          ring_nf;
       _ = o * f x + (1 - o) * f y - m / 2 * o * (1 - o) * ‖x - y‖ ^ 2 := by
          simp only [Real.rpow_two]; rw [← norm_sub_sq_real]

theorem Strongly_Convex_Bound (strongly_convex: Strongly_convex_on s f):
∃ (m : ℝ), m > 0 ∧ ∀ (x : EuclideanSpace ℝ n), x ∈ s
→ ∀ (y:EuclideanSpace ℝ n) , y ∈ s → ∀ (θ : ℝ), θ > 0 → θ < 1 →
f (θ • x + (1 - θ) • y) ≤ θ * f x + (1 - θ) * f y - m / 2 * θ * (1 - θ) * ‖x - y‖ ^ 2 := by
  rcases strongly_convex with ⟨m, hm, hh⟩
  use m
  constructor; exact hm
  intro x hx y hy o hg hl
  rcases hh with ⟨_, hconvex⟩
  specialize @hconvex x hx y hy o (1 - o) (by linarith) (by linarith) (by ring)
  simp only [smul_eq_mul, tsub_le_iff_right] at hconvex
  rw [equiv_lemma hg (by linarith)] at hconvex
  exact hconvex

theorem Strongly_Convex_Def (hs : Convex ℝ s) (hfun : ∃ (m : ℝ), m > 0 ∧ ∀ (x :EuclideanSpace ℝ n),
    x ∈ s → ∀ (y:EuclideanSpace ℝ n) , y ∈ s → ∀ (θ : ℝ), θ > 0 → θ < 1
      → f (θ • x + (1 - θ) • y) ≤ θ * f x + (1 - θ) * f y - m / 2 * θ * (1 - θ) * ‖x - y‖ ^ 2) :
Strongly_convex_on s f := by
  rcases hfun with ⟨m, hm, hfun⟩
  use m; constructor
  · exact hm
  constructor
  · exact hs
  intro x hx y hy o p ho hp hop
  dsimp
  by_cases h: o = 0
  · rw [h, zero_add] at hop
    rw [h, hop, zero_smul, zero_mul, one_smul, zero_add, zero_add, one_mul]
  by_cases h': o = 1
  · rw [h', add_comm, ← eq_sub_iff_add_eq, sub_self] at hop
    rw [h', hop, zero_smul, zero_mul, one_smul, add_zero, add_zero, one_mul]
  have hog: o > 0 := Ne.lt_of_le (id (Ne.symm h)) ho
  have hol: o < 1 := Ne.lt_of_le h' (by linarith)
  rw [add_comm, ← eq_sub_iff_add_eq] at hop
  rw [hop, sub_le_iff_le_add, equiv_lemma hog (by linarith)]
  exact hfun x hx y hy o hog hol

/-
  m - strongly convex function ↔ ∀ x, y in domain s, ∀ θ ∈ (0, 1),
    f (θ • x + (1 - θ) • y) ≤ θ * f x + (1 - θ) * f y - m / 2 * θ * (1 - θ) * ‖x - y‖ ^ 2
-/
theorem Strongly_Convex_Iff (hs : Convex ℝ s):
  Strongly_convex_on s f ↔ ∃ (m : ℝ), m > 0 ∧ ∀ (x :EuclideanSpace ℝ n),
    x ∈ s → ∀ (y:EuclideanSpace ℝ n) , y ∈ s → ∀ (θ : ℝ), θ > 0 → θ < 1
      → f (θ • x + (1 - θ) • y) ≤ θ * f x + (1 - θ) * f y - m / 2 * θ * (1 - θ) * ‖x - y‖ ^ 2 := by
  constructor
  · intro h
    exact Strongly_Convex_Bound s h
  · intro h'
    exact Strongly_Convex_Def s hs h'

lemma Strongly_convex_is_convex (hsc: Strongly_convex_on s f):
ConvexOn ℝ s f := by
  have hsc': Strongly_convex_on s f := hsc
  rcases hsc with ⟨m, _, ⟨hs, _⟩⟩
  constructor; exact hs
  intro x hx y hy o p ho hp hop
  by_cases h : o = 0
  · rw [h, zero_add] at hop
    rw [h, zero_smul, zero_add, zero_smul, zero_add, hop, one_smul, one_smul]
  · by_cases h₁ : o = 1
    · rw [h₁, add_right_eq_self ] at hop
      rw [h₁, hop, zero_smul, add_zero, zero_smul, add_zero, one_smul, one_smul]
    · push_neg at h; push_neg at h₁
      have hhp: p = 1 - o := Eq.symm (sub_eq_of_eq_add' (id (Eq.symm hop)))
      rw [hhp]; simp; rw [hhp] at hp;
      have hog: o > 0 := Ne.lt_of_le (id (Ne.symm h)) ho
      have hol: o < 1 := Ne.lt_of_le h₁ (by linarith)
      rcases Strongly_Convex_Bound s hsc' with ⟨m,hm,hfun⟩
      specialize hfun x hx y hy o hog hol
      have h₂ : m / 2 * o * (1 - o) * ‖x - y‖ ^ 2 ≥ 0 := by
        apply mul_nonneg
        · show 0 ≤ m / 2 * o * (1 - o)
          apply mul_nonneg _ (by linarith)
          · apply mul_nonneg _ (by linarith)
            exact div_nonneg (by linarith) (by norm_num)
        · rw [Real.rpow_two]; exact sq_nonneg ‖x - y‖
      linarith

-- If a strongly convex function admits a global minima, then it is unique.
theorem Strongly_Convex_Unique_Minima {xm xm': EuclideanSpace ℝ n} (hsc: Strongly_convex_on s f)
(min: IsMinOn f s xm) (min' : IsMinOn f s xm') (hxm : xm ∈ s) (hxm' : xm' ∈ s): xm = xm' := by
  by_contra h
  push_neg at h
  have hsc' : Strongly_convex_on s f := hsc
  rw [Strongly_convex_on] at hsc'
  rcases hsc' with ⟨_, _, ⟨hs, _⟩⟩
  have : f xm =  f xm' := by
    apply le_antisymm
    exact min hxm'
    exact min' hxm
  rcases Strongly_Convex_Bound s hsc with ⟨m, hm, hfun⟩
  specialize hfun xm hxm xm' hxm' (1 / 2) (by norm_num) (by norm_num)
  rw [this, ← add_mul, add_sub, add_comm (1 / 2), ← add_sub, sub_self, add_zero, one_mul] at hfun
  have hl : f (((1 : ℝ) / 2) • xm + ((1 : ℝ) - 1 / 2) • xm') < f xm' := by
    have h₂ : m / 2 * (1 / 2) * (1 - 1 / 2) * ‖xm - xm'‖ ^ 2 > 0 := by
      apply mul_pos
      · show 0 < m / 2 * (1 / 2) * (1 - 1 / 2)
        apply mul_pos _ (by linarith)
        · apply mul_pos _ (by linarith)
          exact div_pos (by linarith) (by norm_num)
      · simp only [Real.rpow_two]
        apply pow_two_pos_of_ne_zero
        rw [norm_ne_zero_iff,sub_ne_zero]
        exact h
    linarith
  have hg : f xm' ≤ f (((1 : ℝ) / 2) • xm + ((1 : ℝ) - 1 / 2) • xm') := by
    have : ((1 : ℝ) / 2) • xm + ((1 : ℝ) - 1 / 2) • xm' ∈ s := by
      rw [convex_iff_forall_pos] at hs
      exact @hs xm hxm xm' hxm' (1 / 2) (1 - 1 / 2) (by norm_num) (by norm_num) (by ring)
    apply min' this
  linarith
