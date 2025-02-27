/-
Copyright (c) 2024 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Derivative

/-!
# An analogue of L'Hôpital's Rule for Polynomials over Arbitrary Fields

This file proves an analogue of l'Hôpital's Rule for polynomials over arbitrary fields.
The main result states that given polynomials f, g, and h, such that f(x) = g(x) * h(x),
and α such that both f(α) = 0 and g(α) = 0, then f'(α) = g'(α)h(α).
As pre-requisites we prove that, given a polynomial f and a root α,
there exists a unique polynomial q such that f(x) = (x - α) * q(x) and f'(α) = q(α).
(Uniqueness of q is not needed to prove the main result, but strengthens the intermediary results.)

## References
[Chalkias et al., *Improved Polynomial Division in Cryptography* (Appendix A)][chalkias2024improved]

-/

open Polynomial

variable {F : Type*} [Field F]

-- Given f : F[X] and a root α, there exists a unique q : F[X] s.t. f(x)=(x - α)*q(x)
theorem exists_unique_factor_at_root {f : F[X]} {α : F} (hf : IsRoot f α) :
  ∃! q : F[X], f = (X - C α) * q := by
  by_cases f0 : f = 0
  · -- case: f = 0, which gives us q = 0
    refine ⟨0, ?existence, ?uniqueness⟩
    · -- existence
      simp [f0]
    · --uniqueness
      intro y hy
      rw [f0] at hy
      exact (mul_eq_zero_iff_left (X_sub_C_ne_zero α)).mp (id (Eq.symm hy))
  · -- case: f ≠ 0, α is a root of f so (x-α) divides f which leaves us with q
    obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hf
    use q
    constructor
    · -- existence
      exact hq
    · --uniqueness
      intro y hy
      apply mul_left_cancel₀ (X_sub_C_ne_zero α)
      rw [← hy, hq]

-- Given f : F[X] and a root α, there exists a unique q : F[X] s.t. f(x)=(x - α)*q(x) and f'(α)=q(α)
theorem derivative_eval_eq_quotient_eval {f : F[X]} {α : F} (h : IsRoot f α) :
  ∃! q : F[X], f = (X - C α) * q ∧ eval α (derivative f) = eval α q := by
  -- use the unique factor theorem
  obtain ⟨q, hq⟩ := exists_unique_factor_at_root h
  -- compute the derivative
  have eval_deriv : eval α (derivative f) = eval α q := by
    rw [hq.1]
    simp
  -- now show existence and uniqueness of q
  exists q
  constructor
  · -- existence
    exact ⟨hq.1, eval_deriv⟩
  · -- uniqueness
    intro y hy
    exact hq.2 y (And.left hy)

-- L'Hôpital's Rule for Polynomials: if f(x) = g(x)h(x), f(α) = 0, g(α) = 0, then f'(α) = g'(α)h(α)
theorem lhopital_rule_polynomials {f g h : F[X]} {α : F}
    (hfgh : f = g * h) (hfα : IsRoot f α) (hgα : IsRoot g α) :
    eval α (derivative f) = eval α (derivative g) * eval α h := by
  -- get quotients for both f and g and establish their relation
  obtain ⟨qf, hqf, hderivf⟩ := derivative_eval_eq_quotient_eval hfα
  obtain ⟨qg, hqg, hderivg⟩ := derivative_eval_eq_quotient_eval hgα
  have quotient_rel : qf = qg * h := by
    rw [hqf.1, hqg.1, mul_assoc] at hfgh
    exact mul_left_cancel₀ (Monic.ne_zero (monic_X_sub_C α)) hfgh
  -- then relate the derivatives of f and g
  rw [hqf.2, hqg.2, quotient_rel, eval_mul]
