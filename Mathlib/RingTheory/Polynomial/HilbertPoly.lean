/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FieldSimp

/-!
# Hilbert polynomials

In this file, we formalise the following statement: if `F` is a field with characteristic `0`, then
given any `p : F[X]` and `d : ℕ`, there exists some `h : F[X]` such that for any large enough
`n : ℕ`, `h(n)` is equal to the coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.
This `h` is unique and is denoted as `Polynomial.hilbertPoly p d`.

For example, given `d : ℕ`, the power series expansion of `1/(1-X)ᵈ⁺¹` in `F[X]` is
`Σₙ ((d + n).choose d)Xⁿ`, which equals `Σₙ ((n + 1)···(n + d)/d!)Xⁿ` and hence
`Polynomial.hilbertPoly (1 : F[X]) d` is the polynomial `(n + 1)···(n + d)/d!`. Note that
if `d! = 0` in `F`, then the polynomial `(n + 1)···(n + d)/d!` no longer works, so we do not
want the characteristic of `F` to be divisible by `d!`. As `Polynomial.hilbertPoly` may take
any `p : F[X]` and `d : ℕ` as its inputs, it is necessary for us to assume that `CharZero F`.

## Main definitions

* `Polynomial.hilbertPoly p d`. Given a field `F`, a polynomial `p : F[X]` and a natural number `d`,
  if `F` is of characteristic `0`, then `Polynomial.hilbertPoly p d : F[X]` is the polynomial whose
  value at `n` equals the coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.

## TODO

* Hilbert polynomials of finitely generated graded modules over Noetherian rings.
-/

open Nat PowerSeries

variable (F : Type*) [Field F]

namespace Polynomial

/--
For any field `F` and natural numbers `d` and `k`, `Polynomial.preHilbertPoly F d k`
is defined as `(d.factorial : F)⁻¹ • ((ascPochhammer F d).comp (X - (C (k : F)) + 1))`.
This is the most basic form of Hilbert polynomials. `Polynomial.preHilbertPoly ℚ d 0`
is exactly the Hilbert polynomial of the polynomial ring `ℚ[X_0,...,X_d]` viewed as
a graded module over itself. In fact, `Polynomial.preHilbertPoly F d k` is the
same as `Polynomial.hilbertPoly ((X : F[X]) ^ k) (d + 1)` for any field `F` and
`d k : ℕ` (see the lemma `Polynomial.hilbertPoly_X_pow_succ`). See also the lemma
`Polynomial.preHilbertPoly_eq_choose_sub_add`, which states that if `CharZero F`,
then for any `d k n : ℕ` with `k ≤ n`, `(Polynomial.preHilbertPoly F d k).eval (n : F)`
equals `(n - k + d).choose d`.
-/
noncomputable def preHilbertPoly (d k : ℕ) : F[X] :=
  (d.factorial : F)⁻¹ • ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1))

lemma preHilbertPoly_eq_choose_sub_add [CharZero F] (d : ℕ) {k n : ℕ} (hkn : k ≤ n):
    (preHilbertPoly F d k).eval (n : F) = (n - k + d).choose d := by
  have : ((d ! : ℕ) : F) ≠ 0 := by norm_cast; positivity
  calc
  _ = (↑d !)⁻¹ * eval (↑(n - k + 1)) (ascPochhammer F d) := by simp [cast_sub hkn, preHilbertPoly]
  _ = (n - k + d).choose d := by
    rw [ascPochhammer_nat_eq_natCast_ascFactorial];
    field_simp [ascFactorial_eq_factorial_mul_choose]

variable {F}

/--
`Polynomial.hilbertPoly p 0 = 0`; for any `d : ℕ`, `Polynomial.hilbertPoly p (d + 1)`
is defined as `∑ i in p.support, (p.coeff i) • Polynomial.preHilbertPoly F d i`. If
`M` is a graded module whose Poincaré series can be written as `p(X)/(1 - X)ᵈ` for some
`p : ℚ[X]` with integer coefficients, then `Polynomial.hilbertPoly p d` is the Hilbert
polynomial of `M`. See also `Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval`,
which says that `PowerSeries.coeff F n (p * (PowerSeries.invOneSubPow F d))` equals
`(Polynomial.hilbertPoly p d).eval (n : F)` for any large enough `n : ℕ`.
-/
noncomputable def hilbertPoly (p : F[X]) : (d : ℕ) → F[X]
  | 0 => 0
  | d + 1 => ∑ i in p.support, (p.coeff i) • preHilbertPoly F d i

variable (F) in
lemma hilbertPoly_zero_nat (d : ℕ) : hilbertPoly (0 : F[X]) d = 0 := by
  delta hilbertPoly; induction d with
  | zero => simp only
  | succ d _ => simp only [coeff_zero, zero_smul, Finset.sum_const_zero]

lemma hilbertPoly_poly_zero (p : F[X]) : hilbertPoly p 0 = 0 := rfl

lemma hilbertPoly_poly_succ (p : F[X]) (d : ℕ) :
    hilbertPoly p (d + 1) = ∑ i in p.support, (p.coeff i) • preHilbertPoly F d i := rfl

variable (F) in
lemma hilbertPoly_X_pow_succ (d k : ℕ) :
    hilbertPoly ((X : F[X]) ^ k) (d + 1) = preHilbertPoly F d k := by
  delta hilbertPoly; simp

/--
The key property of Hilbert polynomials. If `F` is a field with characteristic `0`, `p : F[X]` and
`d : ℕ`, then for any large enough `n : ℕ`, `(Polynomial.hilbertPoly p d).eval (n : F)` equals the
coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.
-/
theorem coeff_mul_invOneSubPow_eq_hilbertPoly_eval
    [CharZero F] {p : F[X]} (d : ℕ) {n : ℕ} (hn : p.natDegree < n) :
    PowerSeries.coeff F n (p * (invOneSubPow F d)) = (hilbertPoly p d).eval (n : F) := by
  delta hilbertPoly; induction d with
  | zero => simp only [invOneSubPow_zero, Units.val_one, mul_one, coeff_coe, eval_zero]
            exact coeff_eq_zero_of_natDegree_lt hn
  | succ d hd =>
      simp only [eval_finset_sum, eval_smul, smul_eq_mul]
      rw [← Finset.sum_coe_sort]
      have h_le (i : p.support) : (i : ℕ) ≤ n :=
        le_trans (le_natDegree_of_ne_zero <| mem_support_iff.1 i.2) hn.le
      have h (i : p.support) : eval ↑n (preHilbertPoly F d ↑i) = (n + d - ↑i).choose d := by
        rw [preHilbertPoly_eq_choose_sub_add _ _ (h_le i), Nat.sub_add_comm (h_le i)]
      simp_rw [h]
      rw [Finset.sum_coe_sort _ (fun x => (p.coeff ↑x) * (_ + d - ↑x).choose _),
        PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ (zero_lt_succ d)]
      simp only [coeff_coe, coeff_mk]
      symm
      refine Finset.sum_subset_zero_on_sdiff (fun s hs ↦ ?_) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      · rw [Finset.mem_range_succ_iff]
        exact h_le ⟨s, hs⟩
      · simp only [Finset.mem_sdiff, mem_support_iff, not_not] at hx
        rw [hx.2, zero_mul]
      · rw [add_comm, Nat.add_sub_assoc (h_le ⟨x, hx⟩), succ_eq_add_one, add_tsub_cancel_right]

end Polynomial
