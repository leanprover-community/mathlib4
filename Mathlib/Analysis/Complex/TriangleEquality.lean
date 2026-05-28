/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Complex.Arg
public import Mathlib.Data.Complex.BigOperators

/-!
# Triangle equality for sums of complex vectors

If `u = ∑ i, v i` and `‖u‖ = ∑ i, ‖v i‖`, then all summands lie on the same closed ray.
This generalizes `Complex.norm_add_eq_iff` to finite sums.

## Main results

* `Complex.triangle_equality_iff_aligned`: triangle equality iff all terms are nonnegative
  real multiples of a common unit phase.
* `Complex.sameRay_of_triangle_eq`: each summand is `SameRay` to the sum.
* `Complex.aligned_of_triangle_eq`: each nonzero summand has the same phase as the sum.

## References

See `Complex.norm_add_eq_iff` in `Mathlib/Analysis/Complex/Arg.lean` for the two-vector case.
-/

@[expose] public section

namespace Complex

variable {ι n : Type*} {u : ℂ} {v : ι → ℂ} {s : Finset ι}

open Finset Real
open scoped BigOperators

/-- The square of the norm of a sum is the sum of real parts of `v i * star u`. -/
lemma norm_sq_eq_sum_re_mul_star (h_eq : u = ∑ i ∈ s, v i) :
    ‖u‖ ^ 2 = ∑ i ∈ s, re (v i * star u) := by
  calc
    ‖u‖ ^ 2 = re (u * star u) := by
      rw [star_def, mul_conj, normSq_eq_norm_sq, ofReal_re]
    _ = re ((∑ i ∈ s, v i) * star u) := by rw [h_eq]
    _ = re (∑ i ∈ s, (v i * star u)) := by rw [sum_mul]
    _ = ∑ i ∈ s, re (v i * star u) := by rw [re_sum]

/-- Triangle equality forces `re (v i * star u) = ‖v i‖ * ‖u‖` for each summand. -/
lemma re_mul_star_eq_norm_mul_norm_of_triangle_eq (h_eq : u = ∑ i ∈ s, v i)
    (h_sum : ‖u‖ = ∑ i ∈ s, ‖v i‖) :
    ∀ i ∈ s, re (v i * star u) = ‖v i‖ * ‖u‖ := by
  have h_norm_u_sq := norm_sq_eq_sum_re_mul_star h_eq
  have h_le : ∀ i ∈ s, re (v i * star u) ≤ ‖v i‖ * ‖u‖ := by
    intro i _
    calc re (v i * star u) ≤ ‖v i * star u‖ := re_le_norm _
      _ = ‖v i‖ * ‖star u‖ := by rw [norm_mul]
      _ = ‖v i‖ * ‖u‖ := by rw [star_def, norm_conj]
  apply Finset.eq_of_sum_eq_of_le h_le
  calc
    ∑ i ∈ s, re (v i * star u) = ‖u‖ ^ 2 := h_norm_u_sq.symm
    _ = (∑ i ∈ s, ‖v i‖) * ‖u‖ := by rw [h_sum, pow_two]
    _ = ∑ i ∈ s, (‖v i‖ * ‖u‖) := by rw [sum_mul]

/--
If `u = ∑ v i` with triangle equality and `u ≠ 0`, then each `v i` is a nonnegative real
multiple of `u`.
-/
lemma each_term_is_nonneg_real_multiple_of_sum_of_triangle_eq (h_eq : u = ∑ i ∈ s, v i)
    (h_sum : ‖u‖ = ∑ i ∈ s, ‖v i‖) (h_ne : u ≠ 0) :
    ∀ i ∈ s, ∃ k : ℝ, k ≥ 0 ∧ v i = (k : ℂ) * u := by
  have h_re_norm := re_mul_star_eq_norm_mul_norm_of_triangle_eq h_eq h_sum
  intro i hi
  by_cases hv : v i = 0
  · exact ⟨0, by simp, by simp [hv]⟩
  have hk_pos : 0 < ‖v i‖ / ‖u‖ := div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr h_ne)
  let k := ‖v i‖ / ‖u‖
  refine ⟨k, le_of_lt hk_pos, ?_⟩
  have h : v i * star u = (‖v i‖ * ‖u‖ : ℂ) := by
    rw [← ofReal_mul, ← h_re_norm i hi]
    exact eq_coe_re_of_mul_eq_norm_mul (h_re_norm i hi)
  calc
    v i = (v i * star u) * u / (u * star u) := by
      rw [mul_assoc, mul_comm (star u), mul_div_cancel_right₀ _ <|
        (mul_ne_zero_iff.mpr ⟨h_ne, star_ne_zero.mpr h_ne⟩)]
    _ = (‖v i‖ * ‖u‖ : ℂ) * u / (‖u‖ ^ 2 : ℂ) := by
      rw [h, star_def, mul_conj, normSq_eq_norm_sq, ofReal_pow]
    _ = (k : ℂ) * u := by
      rw [ofReal_div, ← ofReal_mul]
      simp only [ofReal_mul]
      field_simp [norm_ne_zero_iff.mpr h_ne]

/-- If `vi = k • u` for `k ≥ 0` and `u ≠ 0`, then `k = ‖vi‖ / ‖u‖`. -/
lemma coeff_of_nonneg_smul (vi : ℂ) {k : ℝ} (hvi : vi = (k : ℂ) * u) (hk : 0 ≤ k)
    (hu : u ≠ 0) : k = ‖vi‖ / ‖u‖ := by
  have h_norm : ‖vi‖ = k * ‖u‖ := by
    rw [hvi, norm_mul, Complex.norm_of_nonneg hk]
  rcases eq_or_ne vi 0 with hvi_zero | hvi_ne
  · have hk_zero : k = 0 := by
      have : (k : ℂ) = 0 :=
        (mul_eq_zero.mp (by rw [← hvi]; exact hvi_zero)).resolve_right (mod_cast hu)
      exact ofReal_injective this
    simp [hk_zero, hvi_zero]
  · exact eq_div_of_mul_eq (norm_ne_zero_iff.mpr hu) (id (Eq.symm h_norm))

/-- If triangle equality holds, then each summand is on the same ray as `u`. -/
lemma sameRay_of_triangle_eq (h_eq : u = ∑ i ∈ s, v i) (h_sum : ‖u‖ = ∑ i ∈ s, ‖v i‖)
    (h_ne : u ≠ 0) : ∀ i ∈ s, SameRay ℝ (v i) u := by
  intro i hi
  obtain ⟨k, hk, hvi⟩ :=
    each_term_is_nonneg_real_multiple_of_sum_of_triangle_eq h_eq h_sum h_ne i hi
  rcases eq_or_lt_of_le hk with rfl | hk_pos
  · simpa [hvi] using SameRay.zero_left u
  · rw [hvi]
    exact SameRay.sameRay_pos_smul_left u hk_pos

/-- Triangle equality forces each nonzero summand to have the same phase as `u`. -/
lemma aligned_of_triangle_eq (h_eq : u = ∑ i ∈ s, v i) (h_sum : ‖u‖ = ∑ i ∈ s, ‖v i‖)
    (h_ne : u ≠ 0) (i : ι) (hi : i ∈ s) (hvi : v i ≠ 0) :
    v i / (‖v i‖ : ℂ) = u / (‖u‖ : ℂ) := by
  have hray := sameRay_of_triangle_eq h_eq h_sum h_ne i hi
  rw [div_norm_eq_inv_norm_smul hvi, div_norm_eq_inv_norm_smul h_ne,
    SameRay.inv_norm_smul_eq hvi h_ne hray]

variable [Fintype n]

/-- Triangle equality on a sum of nonzero vectors iff all terms share the same unit phase. -/
theorem triangle_equality_iff_aligned {v : n → ℂ} (hv : ∀ i, v i ≠ 0) [Nonempty n] :
    ‖∑ i, v i‖ = ∑ i, ‖v i‖ ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i, v i = (‖v i‖ : ℂ) * c := by
  constructor
  · intro h_eq
    let u := ∑ i, v i
    have hu : u ≠ 0 := by
      intro h_u_zero
      have h_eq_zero : ∑ i, ‖v i‖ = 0 := by simpa [u, h_u_zero, norm_zero] using h_eq.symm
      rw [sum_eq_zero_iff_of_nonneg fun i _ => norm_nonneg (v i)] at h_eq_zero
      obtain ⟨i⟩ := univ_nonempty (α := n)
      exact hv i (norm_eq_zero.mp (h_eq_zero i (mem_univ i)))
    let c := u / (‖u‖ : ℂ)
    refine ⟨c, ?_, fun i => ?_⟩
    · calc ‖c‖ = ‖u‖ / ‖(‖u‖ : ℂ)‖ := by rw [norm_div]
      _ = 1 := by
        rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u),
          div_self (norm_ne_zero_iff.mpr hu)]
    · calc
        v i = ↑(‖v i‖) * (v i / ↑(‖v i‖)) := by
          rw [mul_div_cancel₀ _ (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hv i)))]
        _ = ↑(‖v i‖) * c := by
          have h_sum : ‖u‖ = ∑ i, ‖v i‖ := by simpa [u] using h_eq
          rw [aligned_of_triangle_eq (s := univ) rfl h_sum hu i (mem_univ i) (hv i)]
  · rintro ⟨c, hc, h_aligned⟩
    calc
      ‖∑ i, v i‖
          = ‖∑ i, (‖v i‖ : ℂ) * c‖ := by congr; ext i; exact h_aligned i
      _ = ‖(∑ i, ↑‖v i‖) * c‖ := by rw [Finset.sum_mul]
      _ = ‖∑ i, (‖v i‖ : ℂ)‖ * ‖c‖ := by rw [norm_mul]
      _ = ‖(↑(∑ i, ‖v i‖) : ℂ)‖ * ‖c‖ := by rw [ofReal_sum]
      _ = |∑ i, ‖v i‖| * ‖c‖ := by congr 1; exact norm_real _
      _ = (∑ i, ‖v i‖) * ‖c‖ := by
        rw [abs_of_nonneg (sum_nonneg fun i _ => norm_nonneg _)]
      _ = (∑ i, ‖v i‖) * 1 := by rw [hc]
      _ = ∑ i, ‖v i‖ := by rw [mul_one]

end Complex
