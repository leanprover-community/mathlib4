/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Hilbert polynomials

Given any polynomial `p : ℤ[X]` and `d : ℕ`, there exists some `h : ℚ[X]` such that for any
large enough `n : ℕ`, `(PowerSeries.coeff ℤ n) (p * (@invOneSubPow ℤ _ d))` is equal to
`h.eval (n : ℚ)`. This `h` is called the Hilbert polynomial with respect to `p` and
`d` (`Polynomial.hilbert p d`).
-/

open BigOperators
open PowerSeries

namespace Polynomial

/--
A polynomial which helps make it easier to define the Hilbert polynomial. Look at the
theorem `Polynomial.preHilbert_eq_choose_sub_add`, which states that for any `d k n : ℕ`
with `k ≤ n`, `(preHilbert d k).eval (n : ℚ) = Nat.choose (n - k + d) d`.
-/
noncomputable def preHilbert (d k : ℕ) : Polynomial ℚ :=
  (d.factorial : ℚ)⁻¹ • (∏ i : Finset.range d, (X - (C (k : ℚ)) + (C (i : ℚ)) + 1))

theorem preHilbert_eq_choose_sub_add (d k n : ℕ) (hkn : k ≤ n):
    (preHilbert d k).eval (n : ℚ) = Nat.choose (n - k + d) d := by
  rw [preHilbert]; simp only [Finset.univ_eq_attach, map_natCast, eval_smul, smul_eq_mul]
  rw [eval_prod, @Finset.prod_attach ℚ ℕ _ (Finset.range d) (fun j => eval n (X - (@Nat.cast
    (Polynomial ℚ) NonAssocSemiring.toNatCast k) + (@Nat.cast (Polynomial ℚ)
    NonAssocSemiring.toNatCast j) + 1))]
  simp only [eval_add, eval_sub, eval_X, eval_nat_cast, eval_one]
  rw [Nat.add_choose, Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial_add _ _) (λ h ↦ by
    simp only [Nat.cast_mul, mul_eq_zero, Nat.cast_eq_zero] at h;
    exact Or.elim h (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)), Nat.cast_mul,
    div_mul_eq_div_div, mul_comm, div_eq_mul_inv]
  simp only [mul_eq_mul_right_iff, _root_.inv_eq_zero, Nat.cast_eq_zero]
  · left; rw [← Nat.cast_div (Nat.factorial_dvd_factorial <| Nat.le_add_right (n - k) d) (by
    simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.factorial_ne_zero (n - k)),
      ← Nat.ascFactorial_eq_div]
    induction d with
    | zero => simp only [Nat.zero_eq, Finset.range_zero, Finset.prod_empty, Nat.ascFactorial_zero,
        Nat.cast_one]
    | succ d hd => rw [Finset.prod_range_succ, hd, add_assoc, add_comm (@Nat.cast ℚ
        Semiring.toNatCast d), ← add_assoc, mul_comm, ← Nat.cast_sub hkn, ← Nat.cast_add_one,
        ← Nat.cast_add, ← Nat.cast_mul, ← Nat.ascFactorial_succ]

/--
Given `p : Polynomial ℤ` and `d : ℕ`, the Hilbert polynomial of `p` and `d`.
Look at `Polynomial.coeff_mul_invOneSubPow_eq_hilbert_eval`, which says that
`(PowerSeries.coeff ℤ n) (p * (@invOneSubPow' ℤ _ d))` is equal to
`(Polynomial.hilbert p d).eval (n : ℚ)` for any large enough `n : ℕ`.
-/
noncomputable def hilbert (p : Polynomial ℤ) (d : ℕ) : Polynomial ℚ :=
  ∑ i in Finset.range (natDegree p + 1), (coeff p i) • preHilbert d i

/--
Given `p : Polynomial ℤ` and `d : ℕ`. The key property of the Hilbert polynomial with respect to
`p` and `d`, which says that for any term of `p * (@invOneSubPow ℤ _ d)` whose degree is large
enough, its coefficient can be obtained by evaluating the Hilbert polynomial.
-/
theorem coeff_mul_invOneSubPow_eq_hilbert_eval
    (p : Polynomial ℤ) (d n : ℕ) (hn : Polynomial.natDegree p ≤ n) :
    (PowerSeries.coeff ℤ n) (p * (@invOneSubPow ℤ _ d)) = (hilbert p d).eval (n : ℚ) := by
  rw [show p.ToPowerSeries = (Finset.sum (Finset.range (natDegree p + 1)) (fun (i : ℕ) =>
    (coeff p i) • (X ^ i)) : Polynomial ℤ).ToPowerSeries by
    simp only [zsmul_eq_mul, coe_inj]; exact as_sum_range_C_mul_X_pow p, invOneSubPow, hilbert]
  simp only [zsmul_eq_mul]; rw [eval_finset_sum]; simp only [eval_mul, eval_int_cast]
  rw [(Finset.sum_eq_sum_iff_of_le (λ i hi ↦ by
    simp only [Subtype.forall, Finset.mem_range] at *; rw [preHilbert_eq_choose_sub_add
    d i n <| Nat.le_trans (Nat.le_of_lt_succ hi) hn])).2 <| λ i hi ↦ by
    simp only [Subtype.forall, Finset.mem_range, mul_eq_mul_left_iff, Int.cast_eq_zero] at *;
    exact Or.intro_left _ <| preHilbert_eq_choose_sub_add d i n <|
    Nat.le_trans (Nat.le_of_lt_succ hi) hn, PowerSeries.coeff_mul]
  simp only [coeff_coe, finset_sum_coeff, coeff_intCast_mul, Int.cast_id, coeff_X_pow, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range, coeff_mk, ite_mul, zero_mul,
    Int.cast_sum, Int.cast_ite, Int.cast_mul, Int.cast_ofNat, Int.cast_zero]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, show Nat.succ n =
    (natDegree p + 1) + ((Nat.succ n) - (natDegree p + 1)) by
    simp only [Nat.succ_sub_succ_eq_sub]; rw [add_assoc, add_comm, add_assoc,
    Nat.sub_add_cancel hn]; exact Nat.succ_eq_one_add n, Finset.sum_range_add]
  simp only [Nat.succ_sub_succ_eq_sub, add_lt_iff_neg_left, not_lt_zero', ↓reduceIte,
    Finset.sum_const_zero, add_zero]
  exact (Finset.sum_eq_sum_iff_of_le <| λ i hi ↦ by
    simp only [Finset.mem_range] at hi; simp only [hi, ↓reduceIte, mul_eq_mul_left_iff,
    Nat.cast_inj, Int.cast_eq_zero]; rw [add_comm]).2 <| λ i hi ↦ by
    simp only [Finset.mem_range] at hi; simp only [hi, ↓reduceIte]; rw [add_comm]

end Polynomial
