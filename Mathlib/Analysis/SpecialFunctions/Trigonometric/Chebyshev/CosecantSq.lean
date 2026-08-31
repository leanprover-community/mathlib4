/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Algebra.Polynomial.Splits

/-!
# The cosecant-squared identity

This file proves the classical identity
$$\sum_{k=1}^{N-1} \csc^2\!\left(\frac{k\pi}{N}\right) = \frac{N^2 - 1}{3},$$
stated over `Real.sin` as
`∑ k ∈ Finset.Ico 1 N, (Real.sin (k * π / N))⁻¹ ^ 2 = (N ^ 2 - 1) / 3` for `1 ≤ N`.

The proof uses the Chebyshev polynomial of the second kind `U (N-1)`, whose roots are exactly
`cos (k * π / N)` for `k = 1, …, N-1`. It splits over `ℝ`, so its logarithmic derivative at
`x = 1` sums `1 / (1 - z)` over those roots and evaluates to `(N ^ 2 - 1) / 3`
(`Polynomial.Splits.eval_derivative_div_eval_of_ne_zero` and `derivative_U_eval_one_eq_div`).
The roots are symmetric about `0` (`roots_U_real_map_neg`), so `∑ 1 / (1 + z) = ∑ 1 / (1 - z)`;
averaging the two gives `∑ 1 / (1 - z ^ 2)`, and `1 - cos ^ 2 = sin ^ 2` turns that into the
statement.

## Main statements

* `Polynomial.Chebyshev.splits_U_real`: `U ℝ n` splits over `ℝ`.
* `Polynomial.Chebyshev.roots_U_real_map_neg`: the real roots of `U ℝ n` are symmetric about `0`.
* `Polynomial.Chebyshev.abs_lt_one_of_mem_roots_U_real`: every real root of `U ℝ n` lies in
  `(-1, 1)`.
* `Polynomial.Chebyshev.sum_one_div_one_sub_sq_roots_U_real`: `∑ 1 / (1 - z ^ 2)` over the real
  roots of `U ℝ n` equals `((n + 1) ^ 2 - 1) / 3`.
* `Real.sum_inv_sin_sq_pi_div`: the cosecant-squared identity.

## References

The identity is classical (Cauchy, *Cours d'analyse*, 1821). The related sum
`∑_{k=1}^{m} cot²(kπ/(2m+1)) = m(2m-1)/3` is the arithmetic core of the elementary evaluation of
`∑ 1 / k ^ 2 = π ^ 2 / 6` in M. Aigner and G. M. Ziegler, *Proofs from THE BOOK*, Chapter "π²/6".

## Implementation notes

`splits_U_real`, `roots_U_real_map_neg` and `abs_lt_one_of_mem_roots_U_real` are facts about
`U ℝ n` on their own and could move next to `roots_U_real` in
`Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/RootsExtrema.lean`.
-/

public section

open Polynomial Polynomial.Chebyshev Real

namespace Polynomial.Chebyshev

/-- `U ℝ n` splits over `ℝ`: it has `n` real roots, `cos ((k + 1) * π / (n + 1))` for `k < n`. -/
theorem splits_U_real (n : ℕ) : (U ℝ n).Splits := by
  rw [splits_iff_card_roots, roots_U_real, natDegree_U_natCast, ← Finset.card_def,
    Finset.card_image_of_injOn
      ((Finset.range n).nodup_map_iff_injOn.mp (roots_U_real_nodup n)), Finset.card_range]

/-- The real roots of `U ℝ n` are symmetric about `0`. -/
theorem roots_U_real_map_neg (n : ℕ) : (U ℝ n).roots.map (- ·) = (U ℝ n).roots := by
  have hcomp : (U ℝ n).comp (-X) = Polynomial.C ((-1 : ℝ) ^ n) * U ℝ n :=
    Polynomial.funext fun x ↦ by
      rw [eval_comp, eval_neg, eval_X, U_eval_neg, eval_mul, eval_C, Int.cast_negOnePow_natCast]
  have hu : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero n (neg_ne_zero.2 one_ne_zero)
  have h := map_roots_comp_C_mul_X_add_C (U ℝ n) (-1 : ℝ) 0 isUnit_one.neg
  rw [show Polynomial.C (-1 : ℝ) * X + Polynomial.C 0 = -X by
        rw [map_zero, add_zero, map_neg, map_one, neg_one_mul], hcomp, roots_C_mul _ hu] at h
  simpa [neg_one_mul] using h

/-- `∑ 1 / (1 - z)` over the real roots `z` of `U ℝ n` equals `((n + 1) ^ 2 - 1) / 3`. -/
theorem sum_one_div_one_sub_roots_U_real (n : ℕ) :
    ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ 1 / (1 - z)).sum = (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
  have hne : (U ℝ (n : ℤ)).eval (1 : ℝ) ≠ 0 := by rw [U_eval_one]; positivity
  rw [← (splits_U_real n).eval_derivative_div_eval_of_ne_zero hne, derivative_U_eval_one_eq_div,
    U_eval_one]
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `∑ 1 / (1 + z)` over the real roots `z` of `U ℝ n` equals `((n + 1) ^ 2 - 1) / 3`; by
`roots_U_real_map_neg` it is the same sum as `∑ 1 / (1 - z)`. -/
theorem sum_one_div_one_add_roots_U_real (n : ℕ) :
    ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ 1 / (1 + z)).sum = (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
  conv_lhs => rw [← roots_U_real_map_neg n, Multiset.map_map]
  rw [← sum_one_div_one_sub_roots_U_real n]
  exact congr_arg Multiset.sum (Multiset.map_congr rfl fun z _ ↦ by
    simp only [Function.comp_apply, ← sub_eq_add_neg])

/-- Every real root of `U ℝ n` lies strictly inside `(-1, 1)`. -/
theorem abs_lt_one_of_mem_roots_U_real {n : ℕ} {z : ℝ} (hz : z ∈ (U ℝ (n : ℤ)).roots) :
    |z| < 1 := by
  rw [roots_U_real, Finset.mem_val, Finset.mem_image] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  rw [Finset.mem_range] at hk
  set θ : ℝ := (k + 1) * π / (n + 1) with hθ
  have hpos : 0 < θ := by rw [hθ]; positivity
  have hlt : θ < π := by
    rw [hθ, div_lt_iff₀ (by positivity)]
    have : (k : ℝ) + 1 < n + 1 := by exact_mod_cast Nat.succ_lt_succ hk
    nlinarith [pi_pos]
  have hsin : 0 < sin θ := sin_pos_of_pos_of_lt_pi hpos hlt
  rw [← sq_lt_one_iff_abs_lt_one]
  nlinarith [sin_sq_add_cos_sq θ, mul_pos hsin hsin]

/-- `∑ 1 / (1 - z ^ 2)` over the real roots `z` of `U ℝ n` equals `((n + 1) ^ 2 - 1) / 3`. -/
theorem sum_one_div_one_sub_sq_roots_U_real (n : ℕ) :
    ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ 1 / (1 - z ^ 2)).sum = (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
  have hpoint : ∀ z ∈ (U ℝ (n : ℤ)).roots,
      (fun z : ℝ ↦ 1 / (1 - z ^ 2)) z = (fun z : ℝ ↦ 2⁻¹ * (1 / (1 - z) + 1 / (1 + z))) z :=
    fun z hz ↦ by
      obtain ⟨hz₁, hz₂⟩ := abs_lt.mp (abs_lt_one_of_mem_roots_U_real hz)
      have h1 : (1 - z : ℝ) ≠ 0 := by intro h; linarith
      have h2 : (1 + z : ℝ) ≠ 0 := by intro h; linarith
      simp only
      rw [show (1 : ℝ) - z ^ 2 = (1 - z) * (1 + z) by ring]
      field_simp
      ring
  rw [Multiset.map_congr rfl hpoint, Multiset.sum_map_mul_left, Multiset.sum_map_add,
    sum_one_div_one_sub_roots_U_real n, sum_one_div_one_add_roots_U_real n]
  ring

end Polynomial.Chebyshev

/-- **The cosecant-squared identity.**
`∑_{k=1}^{N-1} csc²(kπ/N) = (N² - 1) / 3`, stated over `Real.sin`. -/
theorem Real.sum_inv_sin_sq_pi_div (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Ico 1 N, (Real.sin ((k : ℝ) * π / N))⁻¹ ^ 2 = ((N : ℝ) ^ 2 - 1) / 3 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hsum := Polynomial.Chebyshev.sum_one_div_one_sub_sq_roots_U_real n
  have hinj : Set.InjOn (fun k : ℕ ↦ Real.cos ((k + 1) * π / (n + 1))) (Finset.range n) :=
    (Finset.range n).nodup_map_iff_injOn.mp (Polynomial.Chebyshev.roots_U_real_nodup n)
  have hfin : ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ 1 / (1 - z ^ 2)).sum =
      ∑ k ∈ Finset.range n, 1 / (1 - Real.cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2) := by
    rw [Polynomial.Chebyshev.roots_U_real n, Finset.image_val_of_injOn hinj, Multiset.map_map]
    rfl
  have hsin : ∑ k ∈ Finset.range n, 1 / (1 - Real.cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2) =
      ∑ k ∈ Finset.range n, (Real.sin ((k + 1 : ℝ) * π / (n + 1)))⁻¹ ^ 2 :=
    Finset.sum_congr rfl fun k _ ↦ by
      rw [show (1 : ℝ) - Real.cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2 =
            Real.sin ((k + 1 : ℝ) * π / (n + 1)) ^ 2 by
          linarith [sin_sq_add_cos_sq ((k + 1 : ℝ) * π / (n + 1))], one_div, inv_pow]
  have himg : Finset.Ico 1 (n + 1) = (Finset.range n).image (· + 1) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨_, h2⟩; exact ⟨k - 1, by omega, by omega⟩
    · rintro ⟨j, _, rfl⟩; omega
  rw [himg, Finset.sum_image fun x _ y _ h ↦ by omega]
  push_cast
  rw [← hsin, ← hfin]
  exact hsum
