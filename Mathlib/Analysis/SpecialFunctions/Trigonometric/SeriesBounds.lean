/-
Copyright (c) 2025 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving, Yury Kudryashov, Runtian Zhou
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Taylor series bounds for trigonometric functions

## Main statements

* `Complex.sin_series_bound`, `Complex.cos_series_bound`, `Real.sin_series_bound` and
  `Real.cos_series_bound` bound the Taylor remainder of `sin` and `cos` at every order, for
  `‖z‖ ≤ 1`. At order `2` they specialise to `Complex.sin_bound` and `Complex.cos_bound`, which
  they generalise.
* `Real.sum_lt_sin_of_pos`, `Real.sin_lt_sum_of_pos`, `Real.sum_lt_cos_of_pos` and
  `Real.cos_lt_sum_of_pos` bracket `sin x` and `cos x` strictly between consecutive partial sums
  of their Taylor series, at every order and for every `x > 0`, with no bound on `x`.
* `Real.cos_lt_one_sub_sq_div_two_add_pow_four`, `Real.sin_lt_sub_cube_add_pow_five` and
  `Real.sub_cube_add_pow_five_lt_sin` are the low-order corollaries, with their non-strict forms.
  They complete the brackets whose lower halves are in
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`.

See `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean` for simpler inequalities and
monotonicity in various intervals, and `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`
for even simpler inequalities and monotonicity results.

## Implementation notes

The four strict bounds for `x > 0` are projections of a single `private` lemma that proves all
four at once: the induction deduces the bound on `sin` at one order from the bound on `cos` at the
previous order and vice versa, so its induction hypothesis has to carry all four.

## Tags

sin, cos
-/

public section

open Set
open scoped Real Nat

/-! ### Remainder bounds on the unit disc -/

/-- Bounds the Taylor remainder of `Complex.sin` at order `n`, for `‖z‖ ≤ 1`. -/
lemma Complex.sin_series_bound {z : ℂ} (z1 : ‖z‖ ≤ 1) (n : ℕ) :
    ‖sin z - z * ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k + 1).factorial‖ ≤
      ‖z‖ ^ (2 * n + 1) * ((2 * n + 2) / ((2 * n + 1).factorial * (2 * n + 1))) := by
  have e : z * ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k + 1).factorial =
      (∑ k ∈ Finset.range (2 * n + 1), (-z * I) ^ k / k.factorial -
       ∑ k ∈ Finset.range (2 * n + 1), (z * I) ^ k / k.factorial) * I / 2 := by
    simp_rw [← Finset.sum_sub_distrib, ← sub_div, Finset.sum_range_even n, Finset.mul_sum,
      Finset.sum_mul, Finset.sum_div, Finset.sum_range_succ', pow_zero, sub_self, zero_div,
      zero_mul, zero_div, add_zero]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rcases k.even_or_odd' with ⟨a, e | e⟩
    · simp only [e, even_two, Even.mul_right, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_div_cancel_left₀, pow_mul, pow_succ', pow_zero, mul_one, mul_pow,
        neg_mul, mul_neg, neg_neg]
      ring_nf
      simp [mul_comm _ 2, pow_mul]
    · simp [e, pow_mul, pow_add, mul_pow]
  rw [sin, e, ← sub_div, ← sub_mul, sub_sub_sub_comm, norm_div, Complex.norm_two,
    div_le_iff₀ (by norm_num), norm_mul, Complex.norm_I, mul_one]
  grw [norm_sub_le, add_le_add ((-z * I).exp_bound (by simpa) (by simp))
    ((z * I).exp_bound (by simpa) (by simp))]
  apply le_of_eq
  simp only [norm_mul, Complex.norm_I, norm_neg, Nat.succ_eq_add_one,
    Nat.cast_add, Nat.cast_mul]
  ring_nf

/-- Bounds the Taylor remainder of `Complex.cos` at order `n`, for `‖z‖ ≤ 1`. -/
lemma Complex.cos_series_bound {z : ℂ} (z1 : ‖z‖ ≤ 1) {n : ℕ} (n0 : 0 < n) :
    ‖cos z - ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k).factorial‖ ≤
      ‖z‖ ^ (2 * n) * ((2 * n + 1) / ((2 * n).factorial * (2 * n))) := by
  have e : ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k).factorial =
      (∑ k ∈ Finset.range (2 * n), (z * I) ^ k / k.factorial +
       ∑ k ∈ Finset.range (2 * n), (-z * I) ^ k / k.factorial) / 2 := by
    simp only [← Finset.sum_add_distrib, Finset.sum_range_even n, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rcases k.even_or_odd' with ⟨a, e | e⟩
    · simp only [e, even_two, Even.mul_right, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_div_cancel_left₀, pow_mul, mul_pow, I_sq, mul_neg, mul_one, neg_mul,
        Even.neg_pow, ← add_div, neg_pow' (z ^ 2), mul_comm _ ((-1 : ℂ) ^ a), ← add_mul]
      ring
    · simp [e, pow_mul, pow_add, mul_pow, neg_div]
  rw [cos, e, ← sub_div, add_sub_add_comm, norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
  grw [norm_add_le, add_le_add ((z * I).exp_bound (by simpa) (by lia))
    ((-z * I).exp_bound (by simpa) (by lia))]
  apply le_of_eq
  simp only [norm_mul, Complex.norm_I, norm_neg, Nat.succ_eq_add_one,
    Nat.cast_add, Nat.cast_mul]
  ring_nf

/-- Bounds the Taylor remainder of `Real.sin` at order `n`, for `|x| ≤ 1`. -/
lemma Real.sin_series_bound {x : ℝ} (x1 : |x| ≤ 1) (n : ℕ) :
    |sin x - x * ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k) / (2 * k + 1).factorial| ≤
      |x| ^ (2 * n + 1) * ((2 * n + 2) / ((2 * n + 1).factorial * (2 * n + 1))) := by
  have b := Complex.sin_series_bound (z := x) (by simpa only [Complex.norm_real]) n
  convert b <;> norm_cast

/-- Bounds the Taylor remainder of `Real.cos` at order `n`, for `|x| ≤ 1`. -/
lemma Real.cos_series_bound {x : ℝ} (x1 : |x| ≤ 1) {n : ℕ} (n0 : 0 < n) :
    |cos x - ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k) / (2 * k).factorial| ≤
      |x| ^ (2 * n) * ((2 * n + 1) / ((2 * n).factorial * (2 * n))) := by
  have b := Complex.cos_series_bound (z := x) (by simpa only [Complex.norm_real]) n0
  convert b <;> norm_cast

/-! ### Strict bracketing by consecutive partial sums, for `x > 0` -/

/-- All four strict bounds at once, for `x > 0`. The four projections below are the intended
interface. -/
private theorem Real.sin_cos_bound_of_pos (x : ℝ) (hx : 0 < x) (n : ℕ) :
    (∑ i ∈ .range (2 * n + 2), (-1) ^ i * x ^ (2 * i + 1) / (2 * i + 1)! < x.sin) ∧
    (x.sin < ∑ i ∈ .range (2 * n + 1), (-1) ^ i * x ^ (2 * i + 1) / (2 * i + 1)!) ∧
    (∑ i ∈ .range (2 * n + 2), (-1) ^ i * x ^ (2 * i) / (2 * i)! < x.cos) ∧
    (x.cos < ∑ i ∈ .range (2 * n + 3), (-1) ^ i * x ^ (2 * i) / (2 * i)!) := by
  have H₀ (x : ℝ) (n : ℕ) (k : ℕ → ℕ) :
      HasDerivAt (fun x : ℝ ↦ ∑ i ∈ .range n, (-1) ^ i * x ^ (k i) / (k i)!)
        (∑ i ∈ .range n, (-1) ^ i * k i * x ^ (k i - 1) / (k i)!) x := by
    refine HasDerivAt.fun_sum fun i hi ↦ ?_
    simpa only [mul_assoc] using ((hasDerivAt_pow (k i) x).const_mul _).div_const _
  set cosSeries := fun (n : ℕ) (x : ℝ) ↦ ∑ i ∈ .range n, (-1) ^ i * x ^ (2 * i) / (2 * i)!
  set sinSeries := fun (n : ℕ) (x : ℝ) ↦ ∑ i ∈ .range n, (-1) ^ i * x ^ (2 * i + 1) / (2 * i + 1)!
  have Hcos₀ (n) : cosSeries (n + 1) 0 = 1 := by simp [cosSeries, Finset.sum_range_succ']
  have Hsin₀ (n) : sinSeries n 0 = 0 := by simp [sinSeries]
  have HsinDeriv (x : ℝ) (n : ℕ) : HasDerivAt (sin - sinSeries n) (cos x - cosSeries n x) x := by
    convert (hasDerivAt_sin x).sub (H₀ x n _) using 1
    simp (disch := positivity) [Nat.factorial_succ, field, mul_assoc,
      mul_left_comm _ (2 * _ + 1 : ℝ), mul_div_mul_left]
  have HcosDeriv (x : ℝ) (n : ℕ) :
      HasDerivAt (cos - cosSeries (n + 1)) (-sin x + sinSeries n x) x := by
    rw [← sub_neg_eq_add (-sin x)]
    convert (hasDerivAt_cos x).sub (H₀ x (n + 1) _) using 2
    rw [Finset.sum_range_succ', ← Finset.sum_neg_distrib, eq_comm]
    convert add_zero _ using 2
    · simp
    · simp [field, Nat.factorial_succ, mul_add_one]
      ring
  have Hstep_sin_cos (n : ℕ) (ih : ∀ x > 0, sin x < sinSeries n x) (x : ℝ) (hx : 0 < x) :
      cosSeries (n + 1) x < cos x := by
    suffices StrictMonoOn (cos - cosSeries (n + 1)) (.Ici 0) by
      simpa [Hcos₀] using this Set.self_mem_Ici hx.le hx
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
    simpa [(HcosDeriv _ _).deriv] using ih
  have Hstep_sin_cos' (n : ℕ) (ih : ∀ x > 0, sinSeries n x < sin x) (x : ℝ) (hx : 0 < x) :
      cos x < cosSeries (n + 1) x := by
    suffices StrictAntiOn (cos - cosSeries (n + 1)) (.Ici 0) by
      simpa [Hcos₀] using this Set.self_mem_Ici hx.le hx
    apply strictAntiOn_of_deriv_neg (convex_Ici 0) (by fun_prop)
    simpa [(HcosDeriv _ _).deriv] using ih
  have Hstep_cos_sin (n : ℕ) (ih : ∀ x > 0, cos x < cosSeries n x) (x : ℝ) (hx : 0 < x) :
      sin x < sinSeries n x := by
    suffices StrictAntiOn (sin - sinSeries n) (Set.Ici 0) by
      simpa [Hsin₀] using this Set.self_mem_Ici hx.le hx
    apply strictAntiOn_of_deriv_neg (convex_Ici 0) (by fun_prop)
    simpa [(HsinDeriv _ _).deriv] using ih
  have Hstep_cos_sin' (n : ℕ) (ih : ∀ x > 0, cosSeries n x < cos x) (x : ℝ) (hx : 0 < x) :
      sinSeries n x < sin x := by
    suffices StrictMonoOn (sin - sinSeries n) (Set.Ici 0) by
      simpa [Hsin₀] using this Set.self_mem_Ici hx.le hx
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
    simpa [(HsinDeriv _ _).deriv] using ih
  induction n generalizing x with
  | zero =>
    have Hsin_lt : ∀ x > 0, sin x < sinSeries 1 x := by
      intro x hx
      simpa [sinSeries] using sin_lt hx
    have Hlt_cos : ∀ x > 0, cosSeries 2 x < cos x := Hstep_sin_cos 1 Hsin_lt
    have Hlt_sin : ∀ x > 0, sinSeries 2 x < sin x := Hstep_cos_sin' 2 Hlt_cos
    have Hcos_lt : ∀ x > 0, cos x < cosSeries 3 x := Hstep_sin_cos' 2 Hlt_sin
    exact ⟨Hlt_sin _ hx, Hsin_lt _ hx, Hlt_cos _ hx, Hcos_lt _ hx⟩
  | succ n ihn =>
    have Hsin_lt : ∀ x > 0, sin x < sinSeries (2 * n + 3) x := Hstep_cos_sin _ fun x hx ↦
      (ihn x hx).2.2.2
    have Hlt_cos : ∀ x > 0, cosSeries (2 * n + 4) x < cos x := Hstep_sin_cos _ Hsin_lt
    have Hlt_sin : ∀ x > 0, sinSeries (2 * n + 4) x < sin x := Hstep_cos_sin' _ Hlt_cos
    have Hcos_lt : ∀ x > 0, cos x < cosSeries (2 * n + 5) x := Hstep_sin_cos' _ Hlt_sin
    simp only [mul_add_one, add_assoc]
    exact ⟨Hlt_sin _ hx, Hsin_lt _ hx, Hlt_cos _ hx, Hcos_lt _ hx⟩

/-- For `x > 0`, the partial sum of the Taylor series of `sin` over `Finset.range (2 * n + 2)`
is a strict lower bound for `sin x`. -/
theorem Real.sum_lt_sin_of_pos {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∑ i ∈ .range (2 * n + 2), (-1) ^ i * x ^ (2 * i + 1) / (2 * i + 1)! < x.sin :=
  (Real.sin_cos_bound_of_pos x hx n).1

/-- For `x > 0`, the partial sum of the Taylor series of `sin` over `Finset.range (2 * n + 1)`
is a strict upper bound for `sin x`. -/
theorem Real.sin_lt_sum_of_pos {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x.sin < ∑ i ∈ .range (2 * n + 1), (-1) ^ i * x ^ (2 * i + 1) / (2 * i + 1)! :=
  (Real.sin_cos_bound_of_pos x hx n).2.1

/-- For `x > 0`, the partial sum of the Taylor series of `cos` over `Finset.range (2 * n + 2)`
is a strict lower bound for `cos x`. -/
theorem Real.sum_lt_cos_of_pos {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∑ i ∈ .range (2 * n + 2), (-1) ^ i * x ^ (2 * i) / (2 * i)! < x.cos :=
  (Real.sin_cos_bound_of_pos x hx n).2.2.1

/-- For `x > 0`, the partial sum of the Taylor series of `cos` over `Finset.range (2 * n + 3)`
is a strict upper bound for `cos x`. -/
theorem Real.cos_lt_sum_of_pos {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x.cos < ∑ i ∈ .range (2 * n + 3), (-1) ^ i * x ^ (2 * i) / (2 * i)! :=
  (Real.sin_cos_bound_of_pos x hx n).2.2.2

/-! ### Low-order corollaries

The lower halves of the bracket at this order are `one_sub_sq_div_two_lt_cos` and
`sin_gt_sub_cube`; the upper halves below complete it.
-/

namespace Real

/-- The quartic Taylor polynomial strictly dominates `cos` away from zero.

The upper half of the bracket whose lower half is `one_sub_sq_div_two_lt_cos`; the hypothesis
`x ≠ 0` matches that lemma's, since both sides here are even. -/
theorem cos_lt_one_sub_sq_div_two_add_pow_four {x : ℝ} (hx : x ≠ 0) :
    cos x < 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have h := cos_lt_sum_of_pos (abs_pos.2 hx) 0
  norm_num [Finset.sum_range_succ, Even.pow_abs] at h
  linarith

/-- The non-strict form of `cos_lt_one_sub_sq_div_two_add_pow_four`, valid for every `x`.

Compare `one_sub_sq_div_two_le_cos`. -/
theorem cos_le_one_sub_sq_div_two_add_pow_four (x : ℝ) : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (cos_lt_one_sub_sq_div_two_add_pow_four hx).le

/-- The quintic Taylor polynomial strictly dominates `sin` on `(0, ∞)`.

The upper half of the bracket whose lower half is `sin_gt_sub_cube`. Unlike the `cos` bound this
is one-sided: both sides are odd, so the inequality reverses for `x < 0` — see
`sub_cube_add_pow_five_lt_sin`. -/
theorem sin_lt_sub_cube_add_pow_five {x : ℝ} (hx : 0 < x) :
    sin x < x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have h := sin_lt_sum_of_pos hx 1
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The non-strict form of `sin_lt_sub_cube_add_pow_five`. Compare `sin_ge_sub_cube`. -/
theorem sin_le_sub_cube_add_pow_five {x : ℝ} (hx : 0 ≤ x) :
    sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  rcases hx.lt_or_eq with h | rfl
  · exact (sin_lt_sub_cube_add_pow_five h).le
  · simp

/-- `sin_lt_sub_cube_add_pow_five` reversed, for negative arguments. Compare `lt_sin`. -/
theorem sub_cube_add_pow_five_lt_sin {x : ℝ} (hx : x < 0) :
    x - x ^ 3 / 6 + x ^ 5 / 120 < sin x := by
  have h := sin_lt_sub_cube_add_pow_five (x := -x) (by linarith)
  rw [sin_neg] at h
  linarith

/-- The non-strict form of `sub_cube_add_pow_five_lt_sin`. Compare `le_sin`. -/
theorem sub_cube_add_pow_five_le_sin {x : ℝ} (hx : x ≤ 0) :
    x - x ^ 3 / 6 + x ^ 5 / 120 ≤ sin x := by
  rcases hx.lt_or_eq with h | rfl
  · exact (sub_cube_add_pow_five_lt_sin h).le
  · simp

end Real
