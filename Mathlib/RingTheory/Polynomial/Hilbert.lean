/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Hilbert polynomials

Given any `p : ℤ[X]` and `d : ℕ`, there exists some `h : ℚ[X]` such that for any
large enough `n : ℕ`, `PowerSeries.coeff ℤ n (p * (@invOneSubPow ℤ _ d))` is equal
to `h.eval (n : ℚ)`. This `h` is unique and is called the Hilbert polynomial with
respect to `p` and `d + 1` (`Polynomial.hilbert p d`).
-/

open BigOperators
open PowerSeries

namespace Polynomial

section greatestFactorOneSubNotDvd

variable {R : Type*} [CommRing R] [NeZero (1 : R)] [NoZeroDivisors R]
variable (p : R[X]) (hp : p ≠ 0) (d : ℕ)

/--
Given a polynomial `p`, the greatest factor of `p` that is not divided by `1 - X`.
-/
noncomputable def greatestFactorOneSubNotDvd : R[X] :=
  ((- 1 : R[X]) ^ p.rootMultiplicity 1) *
  (exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1).choose

local notation "gFOSND" => greatestFactorOneSubNotDvd

omit [NeZero (1 : R)] [NoZeroDivisors R] in
theorem pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq :
    ((1 - X : R[X]) ^ p.rootMultiplicity 1) * greatestFactorOneSubNotDvd p hp = p := by
  rw [greatestFactorOneSubNotDvd, ← mul_assoc, ← mul_pow]
  simp only [mul_neg, mul_one, neg_sub, map_one]
  exact id (exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1).choose_spec.1.symm

omit [NeZero (1 : R)] [NoZeroDivisors R] in
theorem greatestFactorOneSubNotDvd_ne_zero :
    greatestFactorOneSubNotDvd p hp ≠ 0 := fun h0 => by
  let hpow := pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq p hp
  rw [h0, mul_zero] at hpow; exact hp <| id hpow.symm

theorem natDegree_greatestFactorOneSubNotDvd_le :
    (greatestFactorOneSubNotDvd p hp).natDegree ≤ p.natDegree := by
  have : p.natDegree = ((1 - X : R[X]) ^ p.rootMultiplicity 1 * gFOSND p hp).natDegree := by
    rw [pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq]
  rw [this, natDegree_mul]
  exact (gFOSND p hp).natDegree.le_add_left (natDegree ((1 - X) ^ p.rootMultiplicity 1))
  exact pow_ne_zero _ <| fun h0 => by
    let this : (1 - X : R[X]).coeff 0 = 0 := by rw [h0]; simp only [coeff_zero];
    simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this
  exact greatestFactorOneSubNotDvd_ne_zero p hp

theorem natDegree_pow_rootMultiplicity_sub_mul_greatestFactorOneSubNotDvd_le
    (hp1 : d + 1 ≤ p.rootMultiplicity 1) :
    ((1 - X) ^ ((p.rootMultiplicity 1) - (d + 1)) * greatestFactorOneSubNotDvd p hp).natDegree
    ≤ p.natDegree := by
  let this := pow_ne_zero (p.rootMultiplicity 1 - (d + 1)) <| fun (h0 : (1 - X : R[X]) = 0) => by
    let this : (1 - X : R[X]).coeff 0 = 0 := by rw [h0, coeff_zero];
    simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this
  rw [show p.natDegree = (((1 - X : R[X]) ^ (p.rootMultiplicity 1 - (d + 1) + (d + 1))) *
    gFOSND p hp).natDegree by rw [← Nat.eq_add_of_sub_eq hp1 rfl,
    pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq], pow_add, mul_assoc,
    mul_comm ((1 - X) ^ (d + 1)), ← mul_assoc, natDegree_mul, natDegree_mul, natDegree_mul]
  simp only [natDegree_pow, le_add_iff_nonneg_right, zero_le]
  · exact this
  · exact greatestFactorOneSubNotDvd_ne_zero p hp
  · rw [mul_ne_zero_iff]; exact ⟨this, greatestFactorOneSubNotDvd_ne_zero p hp⟩
  · exact pow_ne_zero _ <| fun h0 => by
      let this : (1 - X : R[X]).coeff 0 = 0 := by rw [h0, coeff_zero];
      simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this
  · exact this
  · exact greatestFactorOneSubNotDvd_ne_zero p hp

end greatestFactorOneSubNotDvd

/--
A polynomial which makes it easier to define the Hilbert polynomial. Look at the theorem
`Polynomial.preHilbert_eq_choose_sub_add`, which states that for any `d k n : ℕ` with `k ≤ n`,
`(Polynomial.preHilbert d k).eval (n : ℚ) = Nat.choose (n - k + d) d`.
-/
noncomputable def preHilbert (d k : ℕ) : ℚ[X] :=
  (d.factorial : ℚ)⁻¹ • (∏ i : Finset.range d, (X - (C (k : ℚ)) + (C (i : ℚ)) + 1))

local notation "gFOSND" => greatestFactorOneSubNotDvd

theorem preHilbert_eq_choose_sub_add (d k n : ℕ) (hkn : k ≤ n):
    (preHilbert d k).eval (n : ℚ) = Nat.choose (n - k + d) d := by
  rw [preHilbert]; simp only [Finset.univ_eq_attach, map_natCast, eval_smul, smul_eq_mul]
  rw [eval_prod, @Finset.prod_attach ℕ ℚ _ (Finset.range d)
    (fun j => eval n (X - (@Nat.cast ℚ[X] _ k) + (@Nat.cast ℚ[X] _ j) + 1))]
  simp only [eval_add, eval_sub, eval_X, eval_one]
  rw [Nat.add_choose, Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial_add _ _) (fun h => by
    simp only [Nat.cast_mul, mul_eq_zero, Nat.cast_eq_zero] at h; exact Or.elim h
      (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)), Nat.cast_mul, div_mul_eq_div_div,
      mul_comm, div_eq_mul_inv]
  simp only [mul_eq_mul_right_iff, _root_.inv_eq_zero, Nat.cast_eq_zero]
  · left
    rw [← Nat.cast_div (Nat.factorial_dvd_factorial <| Nat.le_add_right (n - k) d) <| by
      simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.factorial_ne_zero (n - k),
      ← Nat.ascFactorial_eq_div]
    induction d with
    | zero => simp only [Nat.zero_eq, Finset.range_zero, Finset.prod_empty, Nat.ascFactorial_zero,
        Nat.cast_one]
    | succ d hd => rw [Finset.prod_range_succ, hd, add_comm d, mul_comm, eval_natCast,
        ← Nat.cast_sub hkn, eval_natCast, ← Nat.cast_add, ← Nat.cast_add_one, ← Nat.cast_mul,
        ← Nat.succ_eq_one_add, Nat.ascFactorial_succ, add_assoc, add_comm d, ← add_assoc]

/--
Given `p : ℤ[X]` and `d : ℕ`, the Hilbert polynomial of `p` and `d`.
Look at `Polynomial.coeff_mul_invOneSubPow_eq_hilbert_eval`, which says
that `PowerSeries.coeff ℤ n (p * (@invOneSubPow ℤ _ d))` is equal to
`(Polynomial.hilbert p d).eval (n : ℚ)` for any large enough `n : ℕ`.
-/
noncomputable def hilbert (p : ℤ[X]) (d : ℕ) : ℚ[X] :=
  if h : p = 0 then 0
  else if d + 1 ≤ p.rootMultiplicity 1 then 0
  else ∑ i in Finset.range ((greatestFactorOneSubNotDvd p h).natDegree + 1),
  ((greatestFactorOneSubNotDvd p h).coeff i) • preHilbert (d - p.rootMultiplicity 1) i

/--
Given `p : ℤ[X]` and `d : ℕ`. The key property of the Hilbert polynomial with respect to
`p` and `d`, which says that for any term of `p * (@invOneSubPow ℤ _ d)` whose degree is
large enough, its coefficient can be obtained by evaluating the Hilbert polynomial.
-/
theorem coeff_mul_invOneSubPow_eq_hilbert_eval (p : ℤ[X]) (d n : ℕ) (hn : p.natDegree < n) :
    PowerSeries.coeff ℤ n (p * (@invOneSubPow ℤ _ d)) = (hilbert p d).eval (n : ℚ) := by
  rw [hilbert]; by_cases h : p = 0
  · simp only [h, coe_zero, zero_mul, ↓reduceDIte, eval_zero, Int.cast_eq_zero]; rfl
  · simp only [h, ↓reduceDIte, zsmul_eq_mul]
    have coe_one_sub : (1 - X : ℤ[X]).ToPowerSeries = 1 - (PowerSeries.X : ℤ⟦X⟧) :=
      PowerSeries.ext_iff.2 fun i => by_cases (fun (hi : i = 0) => by
      simp only [hi, coeff_coe, coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero,
      map_sub, PowerSeries.coeff_one, ↓reduceIte, coeff_zero_X]) (fun hi => by
      simp only [coeff_coe, coeff_sub, map_sub, PowerSeries.coeff_one, hi, ↓reduceIte,
      zero_sub]; rw [Polynomial.coeff_one]; simp only [hi, ↓reduceIte, zero_sub, neg_inj];
      rw [Polynomial.coeff_X, PowerSeries.coeff_X]; exact by_cases (fun (hi : i = 1) => by
      simp only [hi]) (fun hi => by simp only [hi]; exact if_neg <| Ne.symm hi))
    by_cases h1 : d + 1 ≤ p.rootMultiplicity 1
    · simp only [h1, ↓reduceIte, eval_zero, Int.cast_eq_zero]
      rw [← pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq p h, mul_comm, coe_mul,
        ← mul_assoc, coe_pow, coe_one_sub, ← @Nat.sub_add_cancel (p.rootMultiplicity 1)
        (d + 1) h1, mul_comm (invOneSubPow d).val, pow_add, mul_assoc ((1 - PowerSeries.X) ^
        (p.rootMultiplicity 1 - (d + 1)))]
      erw [(invOneSubPow d).inv_val]
      rw [mul_one, ← coe_one_sub, ← coe_pow, ← coe_mul, coeff_coe]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
        (natDegree_pow_rootMultiplicity_sub_mul_greatestFactorOneSubNotDvd_le p h d h1) hn)
    · simp only [h1, ↓reduceIte]
      rw [coe_inj.2 (pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq p h).symm, coe_mul,
        mul_comm ((1 - X : ℤ[X]) ^ p.rootMultiplicity 1).ToPowerSeries, mul_assoc,
        invOneSubPow_eq_inv_one_sub_pow, show d + 1 = p.rootMultiplicity 1 +
        (d - p.rootMultiplicity 1 + 1) by rw [← Nat.sub_add_comm <| Nat.not_lt.mp h1,
        Nat.add_sub_of_le <| Nat.le_of_not_ge h1], pow_add, Units.val_mul, ← mul_assoc
        ((1 - X : ℤ[X]) ^ rootMultiplicity 1 p).ToPowerSeries, coe_pow, coe_one_sub,
        ← invOneSubPow_eq_inv_one_sub_pow, Units.inv_mk, Units.val_pow_eq_pow_val,
        ← mul_pow, Units.mkOfMulEqOne, mul_comm (1 - PowerSeries.X),
        PowerSeries.mk_one_mul_one_sub_eq_one, one_pow, one_mul, invOneSubPow,
        show (gFOSND p h).ToPowerSeries = (Finset.sum (Finset.range ((gFOSND p h).natDegree + 1))
        (fun (i : ℕ) => ((gFOSND p h).coeff i) • (X ^ i)) : ℤ[X]).ToPowerSeries by
        simp only [zsmul_eq_mul, coe_inj]; exact as_sum_range_C_mul_X_pow (gFOSND p h)]
      simp only [zsmul_eq_mul]; rw [eval_finset_sum]; simp only [eval_mul]
      rw [(Finset.sum_eq_sum_iff_of_le (fun i hi => by
        simp only [Subtype.forall, Finset.mem_range] at *; rw [preHilbert_eq_choose_sub_add
        (d - p.rootMultiplicity 1) i n <| Nat.le_trans (Nat.le_of_lt_succ hi) (le_trans
        (natDegree_greatestFactorOneSubNotDvd_le p h) (le_of_lt hn))])).2 <| fun i hi => by
        simp only [Subtype.forall, Finset.mem_range, mul_eq_mul_left_iff, Int.cast_eq_zero] at *;
        exact Or.intro_left _ <| preHilbert_eq_choose_sub_add (d - p.rootMultiplicity 1) i n <|
        Nat.le_trans (Nat.le_of_lt_succ hi) (le_trans (natDegree_greatestFactorOneSubNotDvd_le p h)
        (le_of_lt hn)), PowerSeries.coeff_mul]
      simp only [coeff_coe, finset_sum_coeff, coeff_intCast_mul, Int.cast_id, coeff_X_pow, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range, coeff_mk, ite_mul, zero_mul,
        Int.cast_sum, Int.cast_ite, Int.cast_mul, Int.cast_ofNat, Int.cast_zero]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        show n.succ = (gFOSND p h).natDegree + 1 + (n.succ - ((gFOSND p h).natDegree + 1)) by
        simp only [Nat.succ_sub_succ_eq_sub]; rw [add_assoc, add_comm, add_assoc,
        Nat.sub_add_cancel (le_trans (natDegree_greatestFactorOneSubNotDvd_le p h) (le_of_lt hn))];
        exact n.succ_eq_one_add, Finset.sum_range_add]
      simp only [Nat.succ_sub_succ_eq_sub, add_lt_iff_neg_left, not_lt_zero', ↓reduceIte,
        Finset.sum_const_zero, add_zero]
      rw [Finset.sum_eq_sum_iff_of_le]
      · intro i hi
        simp only [Finset.mem_range] at hi
        simp only [hi, mul_eq_mul_left_iff]
        rw [add_comm]
        simp only [↓reduceIte, Int.cast_natCast, eval_intCast]
      · intro i hi
        simp only [Finset.mem_range] at hi
        simp only [hi, ↓reduceIte, Int.cast_natCast, eval_intCast]
        rw [add_comm]

end Polynomial
