/-
Copyright (c) 2026 Ji Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ji Huang
-/
module

public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# Hurwitz Stability of Real Polynomials

A real polynomial is called *Hurwitz stable* if all of its complex roots have strictly negative
real part. This is a fundamental concept in control theory and the analysis of linear ODE systems,
where it characterises asymptotic stability.

## Main Definitions

* `Polynomial.IsHurwitzStable`: all complex roots of a real polynomial have negative real part.

## Main Results

* `Polynomial.isHurwitzStable_X_add_C`: `X + C a` is Hurwitz stable iff `0 < a`.
* `Polynomial.isHurwitzStable_quadratic`: `X ^ 2 + C b * X + C c` is Hurwitz stable
  iff `0 < b ∧ 0 < c`.

## References

* <https://en.wikipedia.org/wiki/Routh%E2%80%93Hurwitz_stability_criterion>
-/

@[expose] public section

open Complex Polynomial

namespace Polynomial

variable {a b c : ℝ}

/-- A real polynomial is *Hurwitz stable* if all its complex roots have strictly negative
real part. -/
def IsHurwitzStable (p : Polynomial ℝ) : Prop :=
  ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).IsRoot z → z.re < 0

/-- The zero polynomial is not Hurwitz stable since every complex number is a root. -/
theorem not_isHurwitzStable_zero : ¬IsHurwitzStable (0 : Polynomial ℝ) := by
  intro h
  have := h 0 (by simp [IsRoot.def])
  simp at this

/-- A Hurwitz stable polynomial is nonzero. -/
theorem IsHurwitzStable.ne_zero {p : Polynomial ℝ} (hp : IsHurwitzStable p) : p ≠ 0 :=
  fun h => not_isHurwitzStable_zero (h ▸ hp)

/-- The monic linear polynomial `X + C a` is Hurwitz stable if and only if `0 < a`. -/
theorem isHurwitzStable_X_add_C : IsHurwitzStable (X + C a) ↔ 0 < a := by
  constructor
  · intro h
    have hroot : ((X + C a : ℝ[X]).map (algebraMap ℝ ℂ)).IsRoot (-(a : ℂ)) := by
      rw [IsRoot.def]
      simp [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
            RCLike.algebraMap_eq_ofReal]
    have key := h _ hroot
    simp only [neg_re, ofReal_re] at key
    linarith
  · intro ha z hz
    rw [IsRoot.def] at hz
    simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
               RCLike.algebraMap_eq_ofReal, Polynomial.eval_add, Polynomial.eval_X,
               Polynomial.eval_C] at hz
    have heq : z = -(a : ℂ) := eq_neg_of_add_eq_zero_left hz
    simp only [heq, neg_re, ofReal_re]
    linarith

-- Helper: the degree of the complexified quadratic is positive
private lemma quad_map_degree_pos (b c : ℝ) :
    0 < ((X ^ 2 + C b * X + C c : ℝ[X]).map (algebraMap ℝ ℂ)).degree := by
  have hnd : (X ^ 2 + C b * X + C c : ℝ[X]).natDegree = 2 := by
    rw [show (X ^ 2 + C b * X + C c : ℝ[X]) = C 1 * X ^ 2 + C b * X + C c by simp]
    exact natDegree_quadratic (by norm_num : (1 : ℝ) ≠ 0)
  have hne : X ^ 2 + C b * X + C c ≠ (0 : ℝ[X]) := by
    intro h
    have := congr_arg (Polynomial.coeff · 2) h
    simp at this
  rw [Polynomial.degree_map_eq_of_injective (algebraMap ℝ ℂ).injective,
      degree_eq_natDegree hne, hnd]
  norm_num

-- Helper: IsRoot of the quadratic corresponds to the complex equation
private lemma quad_isRoot_iff (b c : ℝ) (z : ℂ) :
    ((X ^ 2 + C b * X + C c : ℝ[X]).map (algebraMap ℝ ℂ)).IsRoot z ↔
    z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0 := by
  rw [IsRoot.def]
  simp [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
        Polynomial.map_C, RCLike.algebraMap_eq_ofReal, Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]

-- Helper: real and imaginary parts of a quadratic root equation
private lemma quad_re_im (b c : ℝ) (z : ℂ) (hz : z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0) :
    z.re ^ 2 - z.im ^ 2 + b * z.re + c = 0 ∧ z.im * (2 * z.re + b) = 0 := by
  exact ⟨by have := congr_arg re hz; simp [add_re, sq, mul_re] at this; linarith,
         by have := congr_arg im hz; simp [add_im, sq, mul_im] at this; linarith⟩

/-- The monic quadratic `X ^ 2 + C b * X + C c` is Hurwitz stable iff `0 < b ∧ 0 < c`. -/
theorem isHurwitzStable_quadratic :
    IsHurwitzStable (X ^ 2 + C b * X + C c) ↔ 0 < b ∧ 0 < c := by
  simp_rw [IsHurwitzStable, quad_isRoot_iff]
  constructor
  · intro h
    -- Obtain a root using the Fundamental Theorem of Algebra
    obtain ⟨z, hz⟩ := Complex.exists_root (quad_map_degree_pos b c)
    rw [quad_isRoot_iff] at hz
    have hzre : z.re < 0 := h z hz
    obtain ⟨hre, him⟩ := quad_re_im b c z hz
    rcases mul_eq_zero.mp him with him0 | him1
    · -- Real root: both the root z.re and the complementary root -b - z.re are in left half-plane
      have hc_eq : z.re ^ 2 + b * z.re + c = 0 := by simp [him0] at hre; linarith
      -- The complementary root -b - z.re is also a root (by Vieta)
      have hroot2 : ((-b - z.re : ℝ) : ℂ) ^ 2 + (b : ℂ) * ((-b - z.re : ℝ) : ℂ) + (c : ℂ) = 0 := by
        norm_cast
        have : (-b - z.re) ^ 2 + b * (-b - z.re) + c = z.re ^ 2 + b * z.re + c := by ring
        linarith [hc_eq]
      have h2re := h (-b - z.re : ℝ) hroot2
      simp only [ofReal_re] at h2re
      exact ⟨by linarith, by nlinarith [hc_eq]⟩
    · -- Complex root: z.re = -b/2
      have hb_val : b = -2 * z.re := by linarith
      constructor
      · linarith
      · rw [hb_val] at hre
        nlinarith [sq_nonneg z.im, sq_nonneg z.re]
  · -- Sufficient: 0 < b, 0 < c implies all roots have Re < 0
    intro ⟨hb, hc⟩ z hz
    obtain ⟨hre, him⟩ := quad_re_im b c z hz
    rcases mul_eq_zero.mp him with him0 | him1
    · -- Real root: z.re^2 + b*z.re + c = 0 with b, c > 0 forces z.re < 0
      have hc_eq : z.re ^ 2 + b * z.re + c = 0 := by simp [him0] at hre; linarith
      by_contra h
      simp only [not_lt] at h
      nlinarith [sq_nonneg z.re]
    · -- Complex root: 2*z.re + b = 0, so z.re = -b/2 < 0
      linarith

end Polynomial
