/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Estimates for `log⁺` of Polynomial Expressions

Let `R` be a normed ring, let `w : R`, and let `a : ℕ → R` be a family of coefficients. This file
compares the size of polynomial expressions `∑ j ∈ range (d + 1), a j * w ^ j` with the size of `w`.
Size is measured by `log⁺ ‖·‖`, and all estimates are explicit: the error terms depend only on the
degree `d` and on the numbers `log⁺ ‖a j‖`.

## Main results

Growth of polynomial expressions.

- `Real.posLog_norm_sum_mul_pow_le`: an upper bound. The number
  `log⁺ ‖∑ j ∈ range (d + 1), a j * w ^ j‖` is at most `d * log⁺ ‖w‖`, plus the sum of the
  `log⁺ ‖a j‖`, plus `log (d + 1)`.
- `Real.mul_posLog_norm_le_posLog_norm_pow_add_sum`: a lower bound for monic expressions. The number
  `d * log⁺ ‖w‖` is at most `log⁺ ‖w ^ d + ∑ j ∈ range d, a j * w ^ j‖`, plus `d` times the sum of
  the `log⁺ ‖a j‖`, plus `d * log (2 * d)`.

Taken together, the two bounds say that `log⁺` of the norm of a monic polynomial expression of
degree `d` in `w` agrees with `d * log⁺ ‖w‖`, up to an error that is controlled by the coefficients.

Bounds for roots.

- `norm_le_max_one_sum_norm_of_pow_add_sum_eq_zero`: a variant of Cauchy's bound, with the sum of
  the norms of the coefficients in place of their maximum. If
  `w ^ d + ∑ j ∈ range d, a j * w ^ j = 0`, then `‖w‖ ≤ max 1 (∑ j ∈ range d, ‖a j‖)`.
- `Real.posLog_norm_le_of_pow_add_sum_eq_zero`: the logarithmic form
  `log⁺ ‖w‖ ≤ ∑ j ∈ range d, log⁺ ‖a j‖ + log d` of this bound.
- `Real.posLog_inv_norm_le_of_sum_mul_pow_eq_zero`: roots are not small, either. If
  `∑ j ∈ range (d + 1), a j * w ^ j = 0` and `a 0 ≠ 0`, then `log⁺ ‖w‖⁻¹` is at most `log⁺ ‖a 0‖⁻¹`,
  plus the sum of the `log⁺ ‖a j‖` for `1 ≤ j ≤ d`, plus `log d`.

Polynomial relations.

- `Real.posLog_norm_sum_mul_pow_le_of_pow_mul_eq`: if `w ^ n * P = Q`, where `P` and `Q` are
  polynomial expressions in `w` and `Q` has degree at most `n`, then `log⁺ ‖P‖` is bounded in terms
  of the coefficients of `P` and `Q`, independently of `w`.

## Implementation notes

The results are stated for sums over `Finset.range`, and not for `Polynomial.eval`. In typical
applications, `w` and the coefficients `a j` are the values of functions at a point, and there is no
polynomial to evaluate. Versions for `Polynomial.eval` follow with `Polynomial.eval_eq_sum_range`.

The upper bound holds in every seminormed ring with `‖1‖ = 1`, and the lower bound for roots holds
in every normed ring. The other results require in addition that the norm is multiplicative, as
expressed by `NormMulClass`. This assumption cannot be dropped: a square matrix `w` with `w ^ 2 = 0`
is a root of a monic polynomial whose other coefficients vanish, and its norm can be arbitrarily
large. Normed division rings satisfy all assumptions.

## Motivation

The estimates are designed for comple analysis, where `w` and the `a j` are the values of
meromorphic functions. Averaged over circles, the estimates compare the growth of a meromorphic
function `f` with the growth of polynomials in `f`, they bound the growth of functions that are
algebraic over a field of meromorphic functions, and they yield the algebraic cases of the lemmas of
Clunie and Mohon'ko.

## References

* <https://en.wikipedia.org/wiki/Geometrical_properties_of_polynomial_roots#Bounds_on_all_roots>
-/

@[expose] public section

open Finset Real

variable {R : Type*} [SeminormedRing R] [NormOneClass R] {a : ℕ → R} {w : R}

/-!
## Norm Estimates for Polynomial Expressions
-/

/--
If `‖w‖ ≤ 1`, then the norm of a polynomial expression in `w` is at most the sum of the norms of its
coefficients.
-/
lemma norm_sum_mul_pow_le_of_norm_le_one {s : Finset ℕ} (hw : ‖w‖ ≤ 1) :
    ‖∑ j ∈ s, a j * w ^ j‖ ≤ ∑ j ∈ s, ‖a j‖ := by
  refine norm_sum_le_of_le s fun j _ ↦ ?_
  grw [norm_mul_le, norm_pow_le, pow_le_one₀ (norm_nonneg w) hw, mul_one]

/--
If `1 ≤ ‖w‖`, then the norm of a polynomial expression in `w` whose exponents are at most `d` is at
most `‖w‖ ^ d` times the sum of the norms of its coefficients.
-/
lemma norm_sum_mul_pow_le_of_one_le_norm {s : Finset ℕ} {d : ℕ} (hw : 1 ≤ ‖w‖)
    (hs : ∀ j ∈ s, j ≤ d) :
    ‖∑ j ∈ s, a j * w ^ j‖ ≤ (∑ j ∈ s, ‖a j‖) * ‖w‖ ^ d := by
  rw [sum_mul]
  refine norm_sum_le_of_le s fun j hj ↦ ?_
  grw [norm_mul_le, norm_pow_le, pow_le_pow_right₀ hw (hs j hj)]

/--
If `‖w‖` is at least one and at least twice the sum of the norms of the coefficients, then a
polynomial expression of degree less than `d` in `w` is at most half as large as `‖w‖ ^ d`.
-/
lemma two_mul_norm_sum_mul_pow_le_norm_pow {d : ℕ} (hw₁ : 1 ≤ ‖w‖)
    (hw₂ : 2 * ∑ j ∈ range d, ‖a j‖ ≤ ‖w‖) :
    2 * ‖∑ j ∈ range d, a j * w ^ j‖ ≤ ‖w‖ ^ d := by
  obtain _ | d := d
  · simp
  grw [norm_sum_mul_pow_le_of_one_le_norm hw₁ fun _ ↦ mem_range_succ_iff.1, ← mul_assoc, hw₂,
    pow_succ']

/--
If `‖w‖` is at least one and at least twice the sum of the norms of the coefficients, then a monic
polynomial expression of degree `d` in `w` is at most twice as large as `‖w‖ ^ d`. See
`norm_pow_le_two_mul_norm_pow_add_sum` for the converse estimate.
-/
lemma norm_pow_add_sum_le_two_mul_norm_pow {d : ℕ} (hw₁ : 1 ≤ ‖w‖)
    (hw₂ : 2 * ∑ j ∈ range d, ‖a j‖ ≤ ‖w‖) :
    ‖w ^ d + ∑ j ∈ range d, a j * w ^ j‖ ≤ 2 * ‖w‖ ^ d := by
  grw [norm_add_le, norm_pow_le]
  linarith [two_mul_norm_sum_mul_pow_le_norm_pow hw₁ hw₂,
    norm_nonneg (∑ j ∈ range d, a j * w ^ j)]

/--
If `‖w‖` is at least one and at least twice the sum of the norms of the coefficients, then the
leading term of a monic polynomial expression of degree `d` in `w` dominates: `‖w‖ ^ d` is at most
twice as large as the expression. See `norm_pow_add_sum_le_two_mul_norm_pow` for the converse
estimate.
-/
lemma norm_pow_le_two_mul_norm_pow_add_sum [NormMulClass R] {d : ℕ} (hw₁ : 1 ≤ ‖w‖)
    (hw₂ : 2 * ∑ j ∈ range d, ‖a j‖ ≤ ‖w‖) :
    ‖w‖ ^ d ≤ 2 * ‖w ^ d + ∑ j ∈ range d, a j * w ^ j‖ := by
  have := norm_le_add_norm_add (w ^ d) (∑ j ∈ range d, a j * w ^ j)
  rw [norm_pow] at this
  linarith [two_mul_norm_sum_mul_pow_le_norm_pow hw₁ hw₂]

/-!
## Growth of Polynomial Expressions
-/

/--
**Upper bound for polynomial expressions**: `log⁺` of the norm of a polynomial expression of degree
at most `d` in `w` is at most `d * log⁺ ‖w‖`, plus the sum of `log⁺` of the norms of the
coefficients, plus `log (d + 1)`.

The constant `log (d + 1)` accounts for the number of terms, as in `Real.posLog_sum`. The factor of
`log⁺ ‖w‖` is the degree `d`. Estimating the terms one by one, with `Real.posLog_norm_sum_le` and
`Real.posLog_mul`, gives the larger factor `∑ j ∈ range (d + 1), j` instead.
-/
theorem Real.posLog_norm_sum_mul_pow_le (d : ℕ) (a : ℕ → R) (w : R) :
    log⁺ ‖∑ j ∈ range (d + 1), a j * w ^ j‖
      ≤ d * log⁺ ‖w‖ + ∑ j ∈ range (d + 1), log⁺ ‖a j‖ + log (d + 1) := by
  have h₀ : 0 ≤ d * log⁺ ‖w‖ := mul_nonneg d.cast_nonneg posLog_nonneg
  obtain hw | hw := le_total ‖w‖ 1
  · grw [norm_sum_mul_pow_le_of_norm_le_one hw, posLog_sum, card_range, Nat.cast_add_one]
    · linarith
    · exact neg_one_lt_zero.le.trans (norm_nonneg _)
  · grw [norm_sum_mul_pow_le_of_one_le_norm hw fun _ ↦ mem_range_succ_iff.1, posLog_mul,
      posLog_pow, posLog_sum, card_range, Nat.cast_add_one]
    · linarith
    · exact neg_one_lt_zero.le.trans (norm_nonneg _)

/--
**Lower bound for monic polynomial expressions**: `d * log⁺ ‖w‖` is at most `log⁺` of the norm of
the monic polynomial expression `w ^ d + ∑ j ∈ range d, a j * w ^ j`, plus `d` times the sum of
`log⁺` of the norms of the coefficients, plus `d * log (2 * d)`. See
`Real.posLog_norm_sum_mul_pow_le` for the upper bound.

The point of the estimate is the factor `d` on the left. Write `g` for the value of the monic
expression. Then `w` is a root of a monic polynomial of degree `d` whose constant coefficient is
`a 0 - g`, but bounds for the roots of this polynomial, such as
`Real.posLog_norm_le_of_pow_add_sum_eq_zero`, only bound `log⁺ ‖w‖` by `log⁺ ‖g‖` and an error term,
without the factor `d`.

In the constant, `log d` accounts for the number of coefficients, as in `Real.posLog_sum`, and
`log 2` for the threshold `max 1 (2 * ∑ j ∈ range d, ‖a j‖)`: if `‖w‖` exceeds it, then the leading
term `w ^ d` dominates the monic expression. For `d = 1`, the estimate is an instance of
`Real.posLog_norm_add_le`.
-/
theorem Real.mul_posLog_norm_le_posLog_norm_pow_add_sum [NormMulClass R] (d : ℕ) (a : ℕ → R)
    (w : R) :
    d * log⁺ ‖w‖ ≤ log⁺ ‖w ^ d + ∑ j ∈ range d, a j * w ^ j‖
      + d * ∑ j ∈ range d, log⁺ ‖a j‖ + d * log (2 * d) := by
  obtain rfl | hd := d.eq_zero_or_pos
  · simp
  have hd₁ : (1 : ℝ) ≤ d := mod_cast hd
  have h₀ : 0 ≤ ∑ j ∈ range d, log⁺ ‖a j‖ := sum_nonneg fun _ _ ↦ posLog_nonneg
  have h₁ := posLog_nonneg (x := ‖w ^ d + ∑ j ∈ range d, a j * w ^ j‖)
  have h₂ : log⁺ (2 : ℝ) = log 2 := posLog_eq_log (by norm_num)
  rw [log_mul two_ne_zero (by positivity)]
  obtain hw | hw := le_total ‖w‖ (max 1 (2 * ∑ j ∈ range d, ‖a j‖))
  · -- If `w` is bounded in terms of the coefficients, then so is the left-hand side.
    grw [posLog_le_posLog_of_le_max_one (norm_nonneg w) hw, posLog_mul, posLog_sum, card_range, h₂]
    linarith
  · -- Otherwise, the leading term `w ^ d` dominates the monic expression.
    rw [← posLog_pow]
    grw [norm_pow_le_two_mul_norm_pow_add_sum ((le_max_left ..).trans hw)
      ((le_max_right ..).trans hw), posLog_mul, h₂]
    · nlinarith [log_natCast_nonneg d, log_nonneg one_le_two]
    · exact neg_one_lt_zero.le.trans (by positivity)

/-!
## Bounds for Roots
-/

/--
**Bound for the roots of a monic polynomial**: if `w ^ d + ∑ j ∈ range d, a j * w ^ j = 0`, then
`‖w‖ ≤ max 1 (∑ j ∈ range d, ‖a j‖)`. This is a variant of Cauchy's bound,
`Polynomial.IsRoot.norm_lt_cauchyBound`, with the sum of the norms of the coefficients in place of
their maximum. Both bounds are discussed in
<https://en.wikipedia.org/wiki/Geometrical_properties_of_polynomial_roots#Bounds_on_all_roots>,
where the present one is listed as Lagrange's bound. See
`Real.posLog_norm_le_of_pow_add_sum_eq_zero` for the logarithmic form.
-/
theorem norm_le_max_one_sum_norm_of_pow_add_sum_eq_zero [NormMulClass R] {d : ℕ}
    (h : w ^ d + ∑ j ∈ range d, a j * w ^ j = 0) :
    ‖w‖ ≤ max 1 (∑ j ∈ range d, ‖a j‖) := by
  obtain _ | d := d
  · simpa using congr(‖$h‖)
  refine le_max_iff.2 ((le_total ‖w‖ 1).imp_right fun hw ↦ ?_)
  have key := norm_sum_mul_pow_le_of_one_le_norm (a := a) (d := d) hw fun _ ↦ mem_range_succ_iff.1
  rw [eq_neg_of_add_eq_zero_right h, norm_neg, norm_pow, pow_succ'] at key
  exact le_of_mul_le_mul_right key (pow_pos (zero_lt_one.trans_le hw) d)

/--
**Bound for the roots of a monic polynomial, logarithmic form**: if
`w ^ d + ∑ j ∈ range d, a j * w ^ j = 0`, then `log⁺ ‖w‖` is at most the sum of `log⁺` of the
norms of the coefficients, plus `log d`. The constant accounts for the number of coefficients, as
in `Real.posLog_sum`. See
`norm_le_max_one_sum_norm_of_pow_add_sum_eq_zero` for the bound on `‖w‖` itself, and
`Real.mul_posLog_norm_le_posLog_norm_pow_add_sum` for an estimate that does not require the monic
expression to vanish.
-/
theorem Real.posLog_norm_le_of_pow_add_sum_eq_zero [NormMulClass R] {d : ℕ}
    (h : w ^ d + ∑ j ∈ range d, a j * w ^ j = 0) :
    log⁺ ‖w‖ ≤ ∑ j ∈ range d, log⁺ ‖a j‖ + log d := by
  grw [posLog_le_posLog_of_le_max_one (norm_nonneg w)
    (norm_le_max_one_sum_norm_of_pow_add_sum_eq_zero h), posLog_sum, card_range, add_comm]

section NormedRing

variable {R : Type*} [NormedRing R] {a : ℕ → R} {w : R}

/--
**Lower bound for roots**: if `∑ j ∈ range (d + 1), a j * w ^ j = 0` and the constant coefficient
`a 0` is not zero, then `log⁺ ‖w‖⁻¹` is at most `log⁺ ‖a 0‖⁻¹`, plus the sum of `log⁺` of the norms
of the other coefficients, plus `log d`. In other words, a root is small only if the constant
coefficient is small or another coefficient is large.

This is the counterpart of `Real.posLog_norm_le_of_pow_add_sum_eq_zero` for small roots: the inverse
of an invertible root is a root of the polynomial with the coefficients in reverse order, whose
leading coefficient is `a 0`. The assumption `a 0 ≠ 0` cannot be dropped: if all coefficients
vanish, then every `w` is a root, but the right-hand side is the constant `log d`.
-/
theorem Real.posLog_inv_norm_le_of_sum_mul_pow_eq_zero {d : ℕ}
    (h : ∑ j ∈ range (d + 1), a j * w ^ j = 0) (h₀ : a 0 ≠ 0) :
    log⁺ ‖w‖⁻¹ ≤ log⁺ ‖a 0‖⁻¹ + ∑ j ∈ Ico 1 (d + 1), log⁺ ‖a j‖ + log d := by
  have key : ‖w‖⁻¹ ≤ max 1 (‖a 0‖⁻¹ * ∑ j ∈ Ico 1 (d + 1), ‖a j‖) := by
    refine le_max_iff.2 ((le_total 1 ‖w‖).imp inv_le_one_of_one_le₀ fun hw ↦ ?_)
    -- For `‖w‖ ≤ 1`, isolate the constant coefficient: `‖a 0‖ ≤ ‖w‖ * ∑ j ∈ Ico 1 (d + 1), ‖a j‖`.
    have h₁ : ‖a 0‖ ≤ ‖w‖ * ∑ j ∈ Ico 1 (d + 1), ‖a j‖ := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot d.succ_pos, pow_zero, mul_one] at h
      rw [eq_neg_of_add_eq_zero_left h, norm_neg, mul_sum]
      refine norm_sum_le_of_le _ fun j hj ↦ ?_
      grw [norm_mul_le, norm_pow_le' w (by grind), mul_comm,
        pow_le_of_le_one (norm_nonneg w) hw (by grind)]
    have ha : 0 < ‖a 0‖ := norm_pos_iff.2 h₀
    have hw₀ : 0 < ‖w‖ :=
      pos_of_mul_pos_left (ha.trans_le h₁) (sum_nonneg fun _ _ ↦ norm_nonneg _)
    rwa [← div_eq_inv_mul, le_div_iff₀ ha, inv_mul_le_iff₀ hw₀]
  grw [posLog_le_posLog_of_le_max_one (by positivity) key, posLog_mul, posLog_sum, Nat.card_Ico,
    add_tsub_cancel_right]
  linarith

end NormedRing

/-!
## Polynomial Relations
-/

/--
If `w ^ n * P = Q`, where `P = ∑ j ∈ range (p + 1), a j * w ^ j` and
`Q = ∑ k ∈ range (n + 1), b k * w ^ k` are polynomial expressions in `w` and `Q` has degree at most
`n`, then `log⁺ ‖P‖` is bounded in terms of the coefficients of `P` and `Q`, independently of `w`:
it is at most the sum of `log⁺` of the norms of all coefficients, plus the logarithm of the larger
of the two numbers of coefficients. Indeed, the coefficients of `P` bound `P` if `‖w‖ ≤ 1`, and by
the relation, the coefficients of `Q` bound `P` if `1 ≤ ‖w‖`.

This is the pointwise estimate behind Clunie's lemma in value distribution theory.
-/
theorem Real.posLog_norm_sum_mul_pow_le_of_pow_mul_eq [NormMulClass R] {n p : ℕ} {b : ℕ → R}
    (h : w ^ n * ∑ j ∈ range (p + 1), a j * w ^ j = ∑ k ∈ range (n + 1), b k * w ^ k) :
    log⁺ ‖∑ j ∈ range (p + 1), a j * w ^ j‖
      ≤ ∑ j ∈ range (p + 1), log⁺ ‖a j‖ + ∑ k ∈ range (n + 1), log⁺ ‖b k‖
        + log (max (p + 1) (n + 1)) := by
  have hA : 0 ≤ ∑ j ∈ range (p + 1), log⁺ ‖a j‖ := sum_nonneg fun _ _ ↦ posLog_nonneg
  have hB : 0 ≤ ∑ k ∈ range (n + 1), log⁺ ‖b k‖ := sum_nonneg fun _ _ ↦ posLog_nonneg
  have hp : log (p + 1 : ℝ) ≤ log (max (p + 1) (n + 1)) :=
    log_le_log (by positivity) (le_max_left ..)
  have hn : log (n + 1 : ℝ) ≤ log (max (p + 1) (n + 1)) :=
    log_le_log (by positivity) (le_max_right ..)
  obtain hw | hw := le_total ‖w‖ 1
  · grw [norm_sum_mul_pow_le_of_norm_le_one hw, posLog_sum, card_range, Nat.cast_add_one]
    · linarith
    · exact neg_one_lt_zero.le.trans (norm_nonneg _)
  · have key := norm_sum_mul_pow_le_of_one_le_norm (a := b) (d := n) hw
      fun _ ↦ mem_range_succ_iff.1
    rw [← h, norm_mul, norm_pow, mul_comm] at key
    grw [le_of_mul_le_mul_right key (pow_pos (zero_lt_one.trans_le hw) n), posLog_sum, card_range,
      Nat.cast_add_one]
    · linarith
    · exact neg_one_lt_zero.le.trans (norm_nonneg _)
