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
This `h` is unique and is denoted as `Polynomial.hilbert p d`.

## Main definitions

* `Polynomial.hilbert p d`. Given a field `F`, a polynomial `p : F[X]` and a natural number `d`, if
  `F` is of characteristic `0`, then `Polynomial.hilbert p d : F[X]` is the polynomial whose value
  at `n` equals the coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.

## TODO

* Hilbert polynomials of finitely generated graded modules over Noetherian rings.
-/

open BigOperators Nat Polynomial PowerSeries

variable (F : Type*) [Field F]

namespace Polynomial

/--
For any field `F` and natrual numbers `d` and `k`, `Polynomial.preHilbert F d k` is defined as
`(d.factorial : F)⁻¹ • ((ascPochhammer F d).comp (X - (C (k : F)) + 1))`. This is the most basic
form of Hilbert polynomials. `Polynomial.preHilbert ℚ d 0` is exactly the Hilbert polynomial of
the polynomial ring `ℚ[X_0,...,X_d]` viewed as a graded module over itself. See also the theorem
`Polynomial.preHilbert_eq_choose_sub_add`, which states that if `CharZero F`, then for any
`d k n : ℕ` with `k ≤ n`, `(Polynomial.preHilbert F d k).eval (n : F) = (n - k + d).choose d`.
-/
noncomputable def preHilbert (d k : ℕ) : F[X] :=
  (d.factorial : F)⁻¹ • ((ascPochhammer F d).comp (X - (C (k : F)) + 1))

theorem preHilbert_eq_choose_sub_add [CharZero F] (d k n : ℕ) (hkn : k ≤ n):
    (preHilbert F d k).eval (n : F) = (n - k + d).choose d := by
  have : ((d ! : ℕ) : F) ≠ 0 := by norm_cast; positivity
  calc
  _ = (↑d !)⁻¹ * eval (↑(n - k + 1)) (ascPochhammer F d) := by simp [cast_sub hkn, preHilbert]
  _ = (n - k + d).choose d := by
    rw [ascPochhammer_nat_eq_natCast_ascFactorial];
    field_simp [ascFactorial_eq_factorial_mul_choose]

variable {F} in
/--
`Polynomial.hilbert p 0 = 0`; for any `d : ℕ`, `Polynomial.hilbert p (d + 1)` is
defined as `∑ i in p.support, (p.coeff i) • Polynomial.preHilbert F d i`. If `M` is
a graded module whose Poincaré series can be written as `p(X)/(1 - X)ᵈ` for some
`p : ℚ[X]` with integer coefficients, then `Polynomial.hilbert p d` is the Hilbert
polynomial of `M`. See also `Polynomial.coeff_mul_invOneSubPow_eq_hilbert_eval`,
which says that `PowerSeries.coeff F n (p * (PowerSeries.invOneSubPow F d))` is
equal to `(Polynomial.hilbert p d).eval (n : F)` for any large enough `n : ℕ`.
-/
noncomputable def hilbert (p : F[X]) : (d : ℕ) → F[X]
  | 0 => 0
  | d + 1 => ∑ i in p.support, (p.coeff i) • preHilbert F d i

lemma hilbert_zero (d : ℕ) : hilbert (0 : F[X]) d = 0 := by
  delta hilbert; induction d with
  | zero => simp only
  | succ d _ => simp only [coeff_zero, zero_smul, Finset.sum_const_zero]

end Polynomial

namespace PowerSeries

variable {F} in
/--
The key property of Hilbert polynomials. If `F` is a field with characteristic `0`, `p : F[X]` and
`d : ℕ`, then for any large enough `n : ℕ`, `(Polynomial.hilbert p d).eval (n : F)` is equal to the
coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.
-/
theorem coeff_mul_invOneSubPow_eq_hilbert_eval
    [CharZero F] (p : F[X]) (d n : ℕ) (hn : p.natDegree < n) :
    coeff F n (p * (invOneSubPow F d)) = (hilbert p d).eval (n : F) := by
  delta hilbert; induction d with
  | zero => simp only [invOneSubPow_zero, Units.val_one, mul_one, coeff_coe, eval_zero]
            exact coeff_eq_zero_of_natDegree_lt hn
  | succ d hd =>
      simp only [eval_finset_sum, eval_smul, smul_eq_mul]; rw [← Finset.sum_coe_sort]
      simp_rw [show (i : p.support) → eval ↑n (preHilbert F d ↑i) = (n + d - ↑i).choose d by
        intro i; rw [preHilbert_eq_choose_sub_add _ _ _ _ <| le_trans (le_natDegree_of_ne_zero
        <| mem_support_iff.1 i.2) (le_of_lt hn)]; rw [Nat.sub_add_comm];
        exact le_trans (le_natDegree_of_ne_zero <| mem_support_iff.1 i.2) (le_of_lt hn)]
      rw [Finset.sum_coe_sort _ (fun x => (p.coeff ↑x) * (_ + d - ↑x).choose _),
        coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ (zero_lt_succ d)]
      simp only [coeff_coe, coeff_mk]
      exact Eq.symm <| Finset.sum_subset_zero_on_sdiff (fun s hs => Finset.mem_range_succ_iff.mpr
        <| le_trans (le_natDegree_of_ne_zero <| mem_support_iff.1 hs) (le_of_lt hn)) (fun x hx => by
        simp only [Finset.mem_sdiff, mem_support_iff, not_not] at hx; rw [hx.2, zero_mul])
        (fun x hx => by rw [add_comm, Nat.add_sub_assoc <| le_trans (le_natDegree_of_ne_zero <|
        mem_support_iff.1 hx) (le_of_lt hn), succ_eq_add_one, add_tsub_cancel_right])

end PowerSeries
