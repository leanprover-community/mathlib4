/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Stongly convex functions from InnerProductSpace E to ℝ

In this file, we define strongly convex functions and prove the basic properties
of a strongly convex function.
We prove the equivalent definitions for a strongly convex functions.
We prove the tighter bound for a strongly bound comparing with a general convex function.
We prove that if a strongly convex function admits a feasible global minima,
then the minima is unique.

## TODO

Add derivative information for a strongly convex functions, and prove some relevant properties.
Connect with L_smooth property and prove more theorems.
-/

variable {n : Type _} [Fintype n]  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Function f (x) is m - strongly convex iff
  f (x) - m * ‖x‖ ^ 2 / 2 is a convex function -/
def StronglyConvexOn (s : Set E) (m : ℝ) (f : E → ℝ) : Prop :=
 m > 0 ∧ ConvexOn ℝ s (fun x ↦ f x - m / 2 * ‖x‖ ^ 2)

variable (s : Set E) {f : E → ℝ} {m : ℝ}

lemma equiv_lemma {x y : E} {a b m: ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a * (f x - m / 2 * ‖x‖ ^ 2) + b * (f y - m / 2 * ‖y‖ ^ 2) + m / 2 * ‖a • x + b • y‖ ^ 2
      = a * f x + b * f y - m / 2 * a * b * ‖x - y‖ ^ 2 := by
  have : b = 1 - a := Eq.symm (sub_eq_of_eq_add' (id (Eq.symm hab)))
  rw [this]
  calc a * (f x - m / 2 * ‖x‖ ^ 2) + (1 - a) * (f y - m / 2 * ‖y‖ ^ 2)
        + m / 2 * ‖a • x + (1 - a) • y‖ ^ 2
          = a * f x + (1 - a) * f y - m / 2 * a
            * (1 - a) * (‖x‖ ^ 2 - 2 * inner x y + ‖y‖ ^ 2) := by
              simp only [Real.rpow_two]
              rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, inner_smul_right]
              simp only [Real.norm_eq_abs]
              rw [abs_of_pos (by linarith), abs_of_pos (by linarith), mul_pow, mul_pow]; ring_nf
        _ = a * f x + (1 - a) * f y - m / 2 * a * (1 - a) * ‖x - y‖ ^ 2 := by
            simp only [Real.rpow_two]; rw [← norm_sub_sq_real]

theorem Strongly_Convex_Bound (m : ℝ) (strongly_convex: StronglyConvexOn s m f):
  m > 0 ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
     ∀ ⦃a⦄, 0 < a → ∀ ⦃b⦄, 0 < b → a + b = 1 → f (a • x + b • y)
       ≤ a * f x + b * f y - m / 2 * a * b * ‖x - y‖ ^ 2 := by
  rcases strongly_convex with ⟨hm, _, hh⟩
  constructor; exact hm
  intro x hx y hy a ha b hb hab
  specialize @hh x hx y hy a b (by linarith) (by linarith) hab
  simp only [smul_eq_mul, tsub_le_iff_right] at hh
  rw [equiv_lemma ha hb hab] at hh
  exact hh

theorem stronglyConvexOn_def (hs : Convex ℝ s) (hm : m > 0)
(hfun : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
    ∀ ⦃a⦄, 0 < a → ∀ ⦃b⦄, 0 < b → a + b = 1 → f (a • x + b • y)
      ≤ a * f x + b * f y - m / 2 * a * b * ‖x - y‖ ^ 2) :
StronglyConvexOn s m f := by
  constructor
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
  rw [hop, sub_le_iff_le_add, equiv_lemma hog (by linarith) (by ring)]
  exact hfun hx hy hog (by linarith) (by ring)

/-
  m - strongly convex function ↔ ∀ x, y in domain s, ∀ θ ∈ (0, 1),
    f (θ • x + (1 - θ) • y) ≤ θ * f x + (1 - θ) * f y - m / 2 * θ * (1 - θ) * ‖x - y‖ ^ 2
-/
theorem stronglyConvexOn_Iff :
  StronglyConvexOn s m f ↔ m > 0 ∧ Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
     ∀ ⦃a⦄, 0 < a → ∀ ⦃b⦄, 0 < b → a + b = 1 → f (a • x + b • y)
       ≤ a * f x + b * f y - m / 2 * a * b * ‖x - y‖ ^ 2 := by
  constructor
  · intro h
    have : StronglyConvexOn s m f := h
    rcases h with ⟨hm, ⟨h1, _⟩⟩
    constructor
    · exact hm
    · constructor
      · exact h1
      · exact (Strongly_Convex_Bound s m this).2
  · rintro ⟨hm, hs, h'⟩
    exact stronglyConvexOn_def s hs hm h'

lemma StronglyConvexOn.strictConvexOn (hsc : StronglyConvexOn s m f) : StrictConvexOn ℝ s f := by
  have hsc': StronglyConvexOn s m f := hsc
  rcases hsc with ⟨_, ⟨hs, _⟩⟩
  constructor; exact hs
  intro x hx y hy hxy o p ho hp hop
  have hhp: p = 1 - o := Eq.symm (sub_eq_of_eq_add' (id (Eq.symm hop)))
  simp; rw [hhp] at hp;
  have hol: o < 1 := Iff.mp sub_pos hp
  rcases Strongly_Convex_Bound s m hsc' with ⟨_, hfun⟩
  specialize hfun hx hy ho (by linarith) hop
  have h₂ : m / 2 * o * p * ‖x - y‖ ^ 2 > 0 := by
    apply mul_pos
    · rw [hhp]
      positivity
    · rw [Real.rpow_two, sq_pos_iff, norm_ne_zero_iff]
      exact Iff.mpr sub_ne_zero hxy
  linarith

-- If a strongly convex function admits a global minima, then it is unique.
theorem Strongly_Convex_Unique_Minima (m : ℝ) {xm xm': E} (hsc: StronglyConvexOn s m f)
(min: IsMinOn f s xm) (min' : IsMinOn f s xm') (hxm : xm ∈ s) (hxm' : xm' ∈ s): xm = xm' := by
  by_contra h
  push_neg at h
  have hsc' : StronglyConvexOn s m f := hsc
  rw [StronglyConvexOn] at hsc'
  rcases hsc' with ⟨_, ⟨hs, _⟩⟩
  have : f xm =  f xm' := by
    apply le_antisymm
    exact min hxm'
    exact min' hxm
  rcases Strongly_Convex_Bound s m hsc with ⟨_, hfun⟩
  specialize @hfun xm hxm xm' hxm' (1 / 2) (by norm_num) (1 / 2) (by norm_num) (by ring)
  rw [this, ← add_mul, add_comm (1 / 2)] at hfun
  have hl : f (((1 : ℝ) / 2) • xm + ((1 : ℝ) / 2) • xm') < f xm' := by
    have h₂ : m / 2 * (1 / 2) * (1 - 1 / 2) * ‖xm - xm'‖ ^ 2 > 0 := by
      apply mul_pos
      · positivity
      · simp only [Real.rpow_two]
        apply pow_two_pos_of_ne_zero
        rw [norm_ne_zero_iff,sub_ne_zero]
        exact h
    linarith
  have hg : f xm' ≤ f (((1 : ℝ) / 2) • xm + ((1 : ℝ) / 2) • xm') := by
    have : (1 : ℝ) / 2 = (1 : ℝ) - 1 / 2 := by ring
    nth_rw 2 [this]
    have hb: ((1 : ℝ) / 2) • xm + ((1 : ℝ) - 1 / 2) • xm' ∈ s := by
      rw [convex_iff_forall_pos] at hs
      exact @hs xm hxm xm' hxm' (1 / 2) (1 - 1 / 2) (by norm_num) (by norm_num) (by ring)
    exact min' hb
  linarith