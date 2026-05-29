/-
Copyright (c) 2026 Ji Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ji Huang
-/
module

public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Hurwitz Stability of Polynomials

A polynomial with complex coefficients is called *Hurwitz stable* if all of its roots have
strictly negative real part. This is a fundamental concept in control theory and the analysis of
linear ODE systems, where it characterises asymptotic stability.

## Main Definitions

* `Polynomial.IsHurwitzStable`: all roots of a polynomial have negative real part.

## Main Results

* `Polynomial.isHurwitzStable_X_add_C`: `X + C a` is Hurwitz stable iff `0 < a`.
* `Polynomial.isHurwitzStable_quadratic`: `X ^ 2 + C b * X + C c` is Hurwitz stable
  iff `0 < b ∧ 0 < c`.

## Scope

This file treats only monic polynomials of degree 1 and 2. The general Routh–Hurwitz criterion
for degree `n` — stated in terms of the `n × n` Hurwitz matrix and its leading principal minors —
requires infrastructure (Cauchy index or Bezoutian theory) not yet present in Mathlib and is left
for future work.

## References

* <https://en.wikipedia.org/wiki/Routh%E2%80%93Hurwitz_stability_criterion>
-/

@[expose] public section

open Complex Polynomial

namespace Polynomial

variable {a b c : ℝ}

/-- A polynomial is *Hurwitz stable* if all its roots have strictly negative real part. -/
def IsHurwitzStable (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, p.IsRoot z → z.re < 0

/-- The zero polynomial is not Hurwitz stable since every complex number is a root. -/
theorem not_isHurwitzStable_zero : ¬IsHurwitzStable (0 : Polynomial ℂ) := by
  intro h
  have := h 0 (by simp [IsRoot.def])
  simp at this

/-- A Hurwitz stable polynomial is nonzero. -/
theorem IsHurwitzStable.ne_zero {p : Polynomial ℂ} (hp : IsHurwitzStable p) : p ≠ 0 :=
  fun h => not_isHurwitzStable_zero (h ▸ hp)

/-- The monic linear polynomial `X + C a` is Hurwitz stable if and only if `0 < a`. -/
theorem isHurwitzStable_X_add_C : IsHurwitzStable (X + C (a : ℂ)) ↔ 0 < a := by
  constructor
  · intro h
    have hroot : (X + C (a : ℂ) : ℂ[X]).IsRoot (-(a : ℂ)) := by simp [IsRoot.def]
    have key := h _ hroot
    simp only [neg_re, ofReal_re] at key
    linarith
  · intro ha z hz
    rw [IsRoot.def] at hz
    simp only [eval_add, eval_X, eval_C] at hz
    have heq : z = -(a : ℂ) := eq_neg_of_add_eq_zero_left hz
    simp only [heq, neg_re, ofReal_re]
    linarith

-- Helper: the degree of the complex quadratic is positive
private lemma quad_degree_pos (b c : ℝ) :
    0 < (X ^ 2 + C (b : ℂ) * X + C (c : ℂ) : ℂ[X]).degree := by
  have hne : X ^ 2 + C (b : ℂ) * X + C (c : ℂ) ≠ (0 : ℂ[X]) := by
    intro h; have := congr_arg (Polynomial.coeff · 2) h; simp at this
  have hnd : (X ^ 2 + C (b : ℂ) * X + C (c : ℂ) : ℂ[X]).natDegree = 2 := by
    rw [show (X ^ 2 + C (b : ℂ) * X + C (c : ℂ) : ℂ[X]) =
        C 1 * X ^ 2 + C (b : ℂ) * X + C (c : ℂ) by simp]
    exact natDegree_quadratic (by norm_num : (1 : ℂ) ≠ 0)
  rw [degree_eq_natDegree hne, hnd]; norm_num

-- Helper: IsRoot of the complex quadratic corresponds to the root equation
private lemma quad_isRoot_iff (b c : ℝ) (z : ℂ) :
    (X ^ 2 + C (b : ℂ) * X + C (c : ℂ) : ℂ[X]).IsRoot z ↔
    z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0 := by
  rw [IsRoot.def]; simp

-- Helper: real and imaginary parts of a quadratic root equation
private lemma quad_re_im (b c : ℝ) (z : ℂ) (hz : z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0) :
    z.re ^ 2 - z.im ^ 2 + b * z.re + c = 0 ∧ z.im * (2 * z.re + b) = 0 :=
  ⟨by have := congr_arg re hz; simp [add_re, sq, mul_re] at this; linarith,
   by have := congr_arg im hz; simp [add_im, sq, mul_im] at this; linarith⟩

/-- The monic quadratic `X ^ 2 + C b * X + C c` is Hurwitz stable iff `0 < b ∧ 0 < c`. -/
theorem isHurwitzStable_quadratic :
    IsHurwitzStable (X ^ 2 + C (b : ℂ) * X + C (c : ℂ)) ↔ 0 < b ∧ 0 < c := by
  simp_rw [IsHurwitzStable, quad_isRoot_iff]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := Complex.exists_root (quad_degree_pos b c)
    rw [quad_isRoot_iff] at hz
    have hzre : z.re < 0 := h z hz
    obtain ⟨hre, him⟩ := quad_re_im b c z hz
    rcases mul_eq_zero.mp him with him0 | him1
    · have hc_eq : z.re ^ 2 + b * z.re + c = 0 := by simp [him0] at hre; linarith
      have hroot2 : ((-b - z.re : ℝ) : ℂ) ^ 2 + (b : ℂ) * ((-b - z.re : ℝ) : ℂ) + (c : ℂ) = 0 := by
        norm_cast
        have : (-b - z.re) ^ 2 + b * (-b - z.re) + c = z.re ^ 2 + b * z.re + c := by ring
        linarith [hc_eq]
      have h2re := h (-b - z.re : ℝ) hroot2
      simp only [ofReal_re] at h2re
      exact ⟨by linarith, by nlinarith [hc_eq]⟩
    · have hb_val : b = -2 * z.re := by linarith
      exact ⟨by linarith, by rw [hb_val] at hre; nlinarith [sq_nonneg z.im, sq_nonneg z.re]⟩
  · intro ⟨hb, hc⟩ z hz
    obtain ⟨hre, him⟩ := quad_re_im b c z hz
    rcases mul_eq_zero.mp him with him0 | him1
    · have hc_eq : z.re ^ 2 + b * z.re + c = 0 := by simp [him0] at hre; linarith
      by_contra h
      simp only [not_lt] at h
      nlinarith [sq_nonneg z.re]
    · linarith

end Polynomial
