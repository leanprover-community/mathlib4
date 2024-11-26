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

/-!
# Hilbert polynomials

In this file, we formalise the following statement: given any `p : ℤ[X]` and `d : ℕ`, there exists
some `h : ℚ[X]` such that for any large enough `n : ℕ`, `h(n)` is equal to the coefficient of `Xⁿ`
in the power series expansion of `p/(1 - X)ᵈ`. This `h` is unique and is called the
Hilbert polynomial of `p` and `d` (`Polynomial.hilbert p d`).

## Main definitions

* `Polynomial.hilbert p d`. If `p : ℤ[X]` and `d : ℕ` then `Polynomial.hilbert p d : ℚ[X]`
  is the polynomial whose value at `n` equals the coefficient of `Xⁿ` in the power series
  expansion of `p/(1 - X)ᵈ`

## TODO

* Prove that `Polynomial.hilbert p d : ℚ[X]` is the polynomial whose value at `n` equals the
  coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`

* Hilbert polynomials of graded modules.
-/

open BigOperators Nat PowerSeries

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

/--
A polynomial which makes it easier to define the Hilbert polynomial. See also the theorem
`Polynomial.preHilbert_eq_choose_sub_add`, which states that for any `d k n : ℕ` with `k ≤ n`,
`(Polynomial.preHilbert d k).eval (n : ℚ) = (n - k + d).choose d`.
-/
noncomputable def preHilbert (d k : ℕ) : ℚ[X] :=
  (d.factorial : ℚ)⁻¹ • ((ascPochhammer ℚ d).comp (X - (C (k : ℚ)) + 1))

local notation "gFOSND" => greatestFactorOneSubNotDvd

theorem preHilbert_eq_choose_sub_add (d k n : ℕ) (hkn : k ≤ n):
    (preHilbert d k).eval (n : ℚ) = (n - k + d).choose d := by
  rw [preHilbert, eval_smul, eval_comp, map_natCast, eval_add, eval_sub, eval_X, eval_natCast,
    eval_one, smul_eq_mul, ← cast_sub hkn, ← cast_add_one, ← ascPochhammer_eval_cast,
    ascPochhammer_nat_eq_ascFactorial, ascFactorial_eq_factorial_mul_choose, cast_mul,
    ← mul_assoc, ← div_eq_inv_mul, div_self (cast_ne_zero.2 (factorial_ne_zero d)), one_mul]

/--
Given `p : ℤ[X]` and `d : ℕ`, the Hilbert polynomial of `p` and `d`.
See also `Polynomial.coeff_mul_invOneSubPow_eq_hilbert_eval`, which says
that `PowerSeries.coeff ℤ n (p * (invOneSubPow ℤ d))` is equal to
`(Polynomial.hilbert p d).eval (n : ℚ)` for any large enough `n : ℕ`.
-/
noncomputable def hilbert (p : ℤ[X]) (d : ℕ) : ℚ[X] :=
  if h : p = 0 then 0
  else if d ≤ p.rootMultiplicity 1 then 0
  else ∑ i in Finset.range ((greatestFactorOneSubNotDvd p h).natDegree + 1),
  ((greatestFactorOneSubNotDvd p h).coeff i) * preHilbert (d - (p.rootMultiplicity 1) - 1) i

/--
Given `p : ℤ[X]` and `d : ℕ`. The key property of the Hilbert polynomial with respect to
`p` and `d`, which says that for any term of `p * (invOneSubPow ℤ d)` whose degree is
large enough, its coefficient can be obtained by evaluating the Hilbert polynomial.
-/
theorem coeff_mul_invOneSubPow_eq_hilbert_eval (p : ℤ[X]) (d n : ℕ) (hn : p.natDegree < n) :
    PowerSeries.coeff ℤ n (p * (@invOneSubPow ℤ _ d)) = (hilbert p d).eval (n : ℚ) := by
  rw [hilbert]; by_cases h : p = 0
  · simp only [h, coe_zero, zero_mul, map_zero, Int.cast_zero, reduceDIte, eval_zero]
  · simp only [h, reduceDIte, zsmul_eq_mul]
    have coe_one_sub : (1 - X : ℤ[X]).toPowerSeries = 1 - (PowerSeries.X : ℤ⟦X⟧) := by
      simp only [coe_sub, coe_one, coe_X]
    by_cases h1 : d ≤ p.rootMultiplicity 1
    · simp only [h1, reduceIte, eval_zero, Int.cast_eq_zero]
      rw [← pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq p h, mul_comm, coe_mul,
        ← mul_assoc, coe_pow, coe_one_sub, ← Nat.sub_add_cancel h1, mul_comm (invOneSubPow ℤ d).val,
        pow_add, mul_assoc (_ ^ _), ← invOneSubPow_inv_eq_one_sub_pow ℤ d, Units.inv_eq_val_inv,
        Units.inv_mul, mul_one, ← coe_one_sub, ← coe_pow, ← coe_mul, coeff_coe]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
        (natDegree_pow_rootMultiplicity_sub_mul_greatestFactorOneSubNotDvd_le p h d h1) hn)
    · simp only [h1, reduceIte]
      rw [coe_inj.2 (pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq p h).symm, coe_mul,
        mul_comm ((_ : ℤ[X]) ^ _).toPowerSeries, mul_assoc, invOneSubPow_eq_inv_one_sub_pow,
        ← Nat.add_sub_of_le (Nat.le_of_not_ge h1), pow_add, Units.val_mul, ← mul_assoc
        ((_ : ℤ[X]) ^ _).toPowerSeries, coe_pow, coe_one_sub, ← invOneSubPow_eq_inv_one_sub_pow,
        ← invOneSubPow_inv_eq_one_sub_pow, Units.inv_eq_val_inv, add_tsub_cancel_left,
        ← invOneSubPow_eq_inv_one_sub_pow, invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ <|
        zero_lt_sub_of_lt <| gt_of_not_le h1, Units.inv_mul, one_mul, coe_inj.2 <|
        as_sum_range_C_mul_X_pow _, eval_finset_sum]
      simp only [eq_intCast, eval_mul]
      rw [PowerSeries.coeff_mul, ← Finset.sum_coe_sort _ (fun _ => eval .. * _)]
      simp_rw [show ∀ (x : Finset.range _), eval _ (preHilbert (d - rootMultiplicity 1 p - 1) _) =
        _ by intro x; rw [preHilbert_eq_choose_sub_add]; exact Nat.le_trans (Nat.le_of_lt_succ
        (lt_add_one_of_le (Finset.mem_range_succ_iff.1 x.2))) (le_trans
        (natDegree_greatestFactorOneSubNotDvd_le p h) (le_of_lt hn))]
      rw [Finset.sum_coe_sort _ (fun x => eval _ (@Int.cast ℚ[X] ..) *
        (n - x + (d - rootMultiplicity 1 p - 1)).choose (d - rootMultiplicity 1 p - 1))]
      simp only [coeff_coe, finset_sum_coeff, coeff_intCast_mul, Int.cast_id, coeff_X_pow, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range, coeff_mk, ite_mul, zero_mul,
        Int.cast_sum, Int.cast_ite, Int.cast_mul, Int.cast_ofNat, Int.cast_zero]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Eq.symm <| add_sub_of_le <|
        succ_le_succ <| le_trans (natDegree_greatestFactorOneSubNotDvd_le p h) (le_of_lt hn),
        Finset.sum_range_add]
      simp only [succ_sub_succ_eq_sub, add_lt_iff_neg_left, not_lt_zero', reduceIte,
        Finset.sum_const_zero, add_zero]
      exact (Finset.sum_eq_sum_iff_of_le (fun i hi => by
        simp only [Finset.mem_range] at hi; simp only [hi, reduceIte];
        rw [Int.cast_natCast, eval_intCast, add_comm])).2 (fun i hi => by
        rw [Finset.mem_range] at hi; simp only [hi, reduceIte]; rw [add_comm];
        simp only [Int.cast_natCast, eval_intCast])

/--
The Hilbert polynomial is unique. In other words, for any `h : ℚ[X]`, if `h`
satisfies the key property of the Hilbert polynomial (i.e. for any large enough
`n : ℕ`, `PowerSeries.coeff ℤ n (p * (invOneSubPow ℤ d)) = h.eval (n : ℚ)`),
then `h` is the Hilbert polynomial.
-/
theorem exists_unique_hilbert (p : Polynomial ℤ) (d : ℕ) :
    ∃! (h : ℚ[X]), (∃ (N : ℕ), (∀ (n : ℕ) (_ : N < n),
    PowerSeries.coeff ℤ n (p * (invOneSubPow ℤ d)) = h.eval (n : ℚ))) :=
  ⟨hilbert p d, ⟨p.natDegree, fun n hn => coeff_mul_invOneSubPow_eq_hilbert_eval p d n hn⟩,
  fun q ⟨N, hqN⟩ => eq_of_infinite_eval_eq q (hilbert p d) <| fun hfin => Set.Infinite.image
  (Set.injOn_of_injective Nat.cast_injective) (Set.Ioi_infinite (max N p.natDegree)) <|
  Set.Finite.subset hfin <| show @Nat.cast ℚ _ '' (Set.Ioi (max N p.natDegree)) ⊆
  (@setOf ℚ fun x => q.eval x = (hilbert p d).eval x) by
  intro x hx; simp only [Set.mem_image, Set.mem_Ioi, max_lt_iff, Set.mem_setOf_eq] at hx ⊢;
  rcases hx with ⟨n, ⟨h1, h2⟩, h3⟩; rw [← h3, ← coeff_mul_invOneSubPow_eq_hilbert_eval p d n h2];
  exact (Rat.ext (congrArg Rat.num (hqN n h1)) (congrArg Rat.den (hqN n h1))).symm⟩

theorem leadingCoeff_ascPochhammer (R : Type*) [Semiring R] [Nontrivial R] (n : ℕ) :
    leadingCoeff (ascPochhammer R n) = 1 := by
  induction n with
  | zero => simp only [ascPochhammer_zero, monic_one, Monic.leadingCoeff]
  | succ n hn =>
      rw [ascPochhammer_succ_right, leadingCoeff_mul']
      · rw [hn, one_mul, ← C_eq_natCast, leadingCoeff_X_add_C]
      · rw [hn, one_mul, ← C_eq_natCast, leadingCoeff_X_add_C]; exact one_ne_zero

/--
This theorem tells us the specific degree of any non-zero Hilbert polynomial.
-/
theorem natDegree_hilbert (p : ℤ[X]) (d : ℕ) (hh : hilbert p d ≠ 0) :
    (hilbert p d).natDegree = d - p.rootMultiplicity 1 - 1 := by
  by_cases h : p = 0
  · exfalso; rw [hilbert] at hh; simp only [h, reduceDIte, ne_eq, not_true_eq_false] at hh
  · by_cases h1 : d ≤ p.rootMultiplicity 1
    · rw [hilbert] at hh
      simp only [h1, reduceIte, dite_eq_ite, ite_self, ne_eq, not_true_eq_false] at hh
    · rw [hilbert]; apply natDegree_eq_of_le_of_coeff_ne_zero _ _
      · simp only [h, reduceDIte, h1, reduceIte]
        apply natDegree_sum_le_of_forall_le _ _ _
        · intro i _; apply le_trans natDegree_mul_le _
          · simp only [natDegree_intCast, zero_add]
            apply le_trans (natDegree_smul_le _ _) _
            · rw [natDegree_comp, ascPochhammer_natDegree, add_comm_sub, show 1 - _ = C (1 - i : ℚ)
                by simp only [map_sub, map_one], natDegree_add_C, natDegree_X, mul_one]
      · simp only [h, reduceDIte, h1, reduceIte, finset_sum_coeff, coeff_intCast_mul, preHilbert,
          coeff_smul, map_natCast, smul_eq_mul]
        have (x : ℕ) : ((ascPochhammer ℚ (d - rootMultiplicity 1 p - 1)).comp
            (X - (x : ℚ[X]) + 1)).coeff (d - rootMultiplicity 1 p - 1) = 1 := by
          rw [sub_add, show x - 1 = C (x - 1 : ℚ) by simp only [map_natCast, map_sub, map_one]]
          have : ((ascPochhammer ℚ (d - rootMultiplicity 1 p - 1)).comp
              (X - C ((x : ℚ) - 1))).coeff (d - rootMultiplicity 1 p - 1) = ((ascPochhammer ℚ
              (d - rootMultiplicity 1 p - 1)).comp (X - C ((x : ℚ) - 1))).coeff ((ascPochhammer ℚ
              (d - rootMultiplicity 1 p - 1)).comp (X - C ((x : ℚ) - 1))).natDegree := by
            rw [natDegree_comp, ascPochhammer_natDegree, natDegree_X_sub_C, mul_one]
          rw [this, coeff_natDegree, leadingCoeff_comp <| ne_of_eq_of_ne (natDegree_X_sub_C _)
            one_ne_zero, leadingCoeff_ascPochhammer, one_mul, leadingCoeff_X_sub_C, one_pow]
        simp_rw [this]
        rw [mul_one, ← Finset.sum_mul, show ∑ x in _, @Int.cast ℚ _ _ = (gFOSND p h).eval 1 by
          rw [eval_eq_sum_range]; simp only [one_pow, mul_one, Int.cast_sum], ne_eq,
          _root_.mul_eq_zero, inv_eq_zero, cast_eq_zero, not_or, greatestFactorOneSubNotDvd]
        constructor
        · simp only [eval_mul, eval_pow, eval_neg, eval_one, _root_.mul_eq_zero, pow_eq_zero_iff',
            neg_eq_zero, one_ne_zero, false_and, Int.cast_eq_zero, false_or]
          exact (not_iff_not.2 dvd_iff_isRoot).1
            (exists_eq_pow_rootMultiplicity_mul_and_not_dvd p h 1).choose_spec.2
        · exact Nat.factorial_ne_zero _

end Polynomial
