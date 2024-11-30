/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
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

open Nat PowerSeries

namespace Polynomial

section greatestFactorOneSubNotDvd

variable {R : Type*} [CommRing R] (p : R[X]) (hp : p ≠ 0) (d : ℕ)

/--
Given a polynomial `p`, the factor `f` of `p` such that the product of `f` and
`(1 - X : R[X]) ^ p.rootMultiplicity 1` equals `p`. We define this here because if `p` is divisible
by `1 - X`, then the expression `p/(1 - X)ᵈ` can be reduced. We want to construct the Hilbert
polynomial based on the most reduced form of the fraction `p/(1 - X)ᵈ`. Later we will see that this
method of construction makes it much easier to calculate the specific degree of the Hilbert
polynomial.
-/
noncomputable def greatestFactorOneSubNotDvd : R[X] :=
  ((- 1 : R[X]) ^ p.rootMultiplicity 1) *
  (exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1).choose

local notation "gFOSND" => greatestFactorOneSubNotDvd

theorem pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq :
    ((1 - X : R[X]) ^ p.rootMultiplicity 1) * greatestFactorOneSubNotDvd p hp = p := by
  rw [greatestFactorOneSubNotDvd, ← mul_assoc, ← mul_pow]
  simp only [mul_neg, mul_one, neg_sub, map_one]
  exact id (exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1).choose_spec.1.symm

theorem greatestFactorOneSubNotDvd_ne_zero :
    greatestFactorOneSubNotDvd p hp ≠ 0 := fun h0 => by
  let hpow := pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq p hp
  rw [h0, mul_zero] at hpow; exact hp <| id hpow.symm

theorem natDegree_greatestFactorOneSubNotDvd_le [Nontrivial R] [NoZeroDivisors R] :
    (greatestFactorOneSubNotDvd p hp).natDegree ≤ p.natDegree := by
  have : p.natDegree = ((1 - X : R[X]) ^ p.rootMultiplicity 1 * gFOSND p hp).natDegree := by
    rw [pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq]
  rw [this, natDegree_mul]
  · exact (gFOSND p hp).natDegree.le_add_left (natDegree ((1 - X) ^ p.rootMultiplicity 1))
  · exact pow_ne_zero _ <| fun h0 => by
      let this : (1 - X : R[X]).coeff 0 = 0 := by rw [h0]; simp only [coeff_zero];
      simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this
  exact greatestFactorOneSubNotDvd_ne_zero p hp

theorem natDegree_pow_rootMultiplicity_sub_mul_greatestFactorOneSubNotDvd_le
    [Nontrivial R] [NoZeroDivisors R] (hp1 : d ≤ p.rootMultiplicity 1) :
    ((1 - X) ^ ((p.rootMultiplicity 1) - d) * greatestFactorOneSubNotDvd p hp).natDegree
    ≤ p.natDegree := by
  have : (1 - X : R[X]) ≠ 0 :=  fun h0 => by
    let h : (1 - X : R[X]).coeff 0 = 0 := by rw [h0, coeff_zero];
    simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at h
  rw [show p.natDegree = ((((1 - X : R[X]) ^ (p.rootMultiplicity 1 - d + d))) *
    (gFOSND p hp)).natDegree by rw [← Nat.eq_add_of_sub_eq hp1 rfl,
    pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq], pow_add, mul_assoc,
    mul_comm ((1 - X) ^ d), ← mul_assoc, natDegree_mul, natDegree_mul, natDegree_mul]
  · simp only [natDegree_pow, le_add_iff_nonneg_right, zero_le]
  · exact pow_ne_zero _ this
  · exact greatestFactorOneSubNotDvd_ne_zero p hp
  · rw [mul_ne_zero_iff]; exact ⟨pow_ne_zero _ this, greatestFactorOneSubNotDvd_ne_zero p hp⟩
  · exact pow_ne_zero _ this
  · exact pow_ne_zero _ this
  · exact greatestFactorOneSubNotDvd_ne_zero p hp

end greatestFactorOneSubNotDvd

variable (F : Type*) [Field F]

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

variable {F}

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

variable (F) in
lemma hilbert_zero (d : ℕ) : hilbert (0 : F[X]) d = 0 := by
  delta hilbert; induction d with
  | zero => simp only
  | succ d _ => simp only [coeff_zero, zero_smul, Finset.sum_const_zero]

/--
The key property of Hilbert polynomials. If `F` is a field with characteristic `0`, `p : F[X]` and
`d : ℕ`, then for any large enough `n : ℕ`, `(Polynomial.hilbert p d).eval (n : F)` is equal to the
coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.
-/
theorem coeff_mul_invOneSubPow_eq_hilbert_eval
    [CharZero F] (p : F[X]) (d n : ℕ) (hn : p.natDegree < n) :
    PowerSeries.coeff F n (p * (invOneSubPow F d)) = (hilbert p d).eval (n : F) := by
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
        PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ (zero_lt_succ d)]
      simp only [coeff_coe, coeff_mk]
      exact Eq.symm <| Finset.sum_subset_zero_on_sdiff (fun s hs => Finset.mem_range_succ_iff.mpr
        <| le_trans (le_natDegree_of_ne_zero <| mem_support_iff.1 hs) (le_of_lt hn)) (fun x hx => by
        simp only [Finset.mem_sdiff, mem_support_iff, not_not] at hx; rw [hx.2, zero_mul])
        (fun x hx => by rw [add_comm, Nat.add_sub_assoc <| le_trans (le_natDegree_of_ne_zero <|
        mem_support_iff.1 hx) (le_of_lt hn), succ_eq_add_one, add_tsub_cancel_right])

lemma hilbert_succ [CharZero F] (p : F[X]) (d : ℕ) :
    hilbert (p * (1 - X)) (d + 1) = hilbert p d := by
  have (n : Set.Ioi (p * (1 - X)).natDegree) :
      (hilbert (p * (1 - X)) (d + 1)).eval (n : F) = (hilbert p d).eval (n : F) := by
    by_cases hp : p = 0
    · simp only [hp, zero_mul, hilbert_zero]
    · rw [← coeff_mul_invOneSubPow_eq_hilbert_eval, ← coeff_mul_invOneSubPow_eq_hilbert_eval]
      · apply PowerSeries.ext_iff.1 <| by
          simp only [coe_mul, mul_assoc, mul_eq_mul_left_iff, coe_eq_zero_iff, hp]
          rw [invOneSubPow_eq_inv_one_sub_pow, pow_add, ← invOneSubPow_eq_inv_one_sub_pow,
            ← invOneSubPow_eq_inv_one_sub_pow, mul_comm, Units.val_mul, mul_assoc]
          simp only [coe_sub, coe_one, coe_X, ne_eq, Units.ne_zero, not_false_eq_true, mul_eq_left₀,
            or_false]
          exact Units.mul_eq_one_iff_inv_eq.mpr (pow_one (1 - PowerSeries.X))
      · exact lt_of_add_right_lt <| le_of_eq_of_le (congr_arg succ <| natDegree_mul hp <|
          ne_zero_of_natDegree_gt <| lt_of_lt_of_eq one_pos (show ((1 : F[X]) - X).natDegree = 1 by
          rw [← natDegree_neg, neg_sub]; exact natDegree_X_sub_C 1).symm).symm <| Set.mem_Ici.1 n.2
      · exact Set.mem_Ici.1 n.2
  exact eq_of_infinite_eval_eq _ _ <| fun hfin => Set.Infinite.image (Set.injOn_of_injective
    cast_injective) (Set.Ioi_infinite _) (Set.Finite.subset hfin <| show Nat.cast '' _ ⊆ _ by
    intro x hx; rcases hx with ⟨n, hn1, hn2⟩; rw [← hn2]; exact this ⟨n, hn1⟩)

theorem exists_unique_hilbert [CharZero F] (p : F[X]) (d : ℕ) :
    ∃! (h : F[X]), (∃ (N : ℕ), (∀ (n : ℕ) (_ : N < n),
    PowerSeries.coeff F n (p * (invOneSubPow F d)) = h.eval (n : F))) :=
  ⟨hilbert p d, ⟨p.natDegree, fun n hn => coeff_mul_invOneSubPow_eq_hilbert_eval p d n hn⟩,
  fun q ⟨N, hqN⟩ => eq_of_infinite_eval_eq q (hilbert p d) <| fun hfin =>
  Set.Infinite.image (Set.injOn_of_injective Nat.cast_injective)
  (Set.Ioi_infinite (max N p.natDegree)) <| Set.Finite.subset hfin <| fun x hx => by
  simp only [Set.mem_image, Set.mem_Ioi, sup_lt_iff, Set.mem_setOf_eq] at hx ⊢;
  rcases hx with ⟨n, ⟨h1, h2⟩, h3⟩;
  rw [← h3, ← coeff_mul_invOneSubPow_eq_hilbert_eval p d n h2, hqN n h1]⟩

end Polynomial
