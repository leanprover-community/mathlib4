/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Hilbert polynomials

Given any `p : ℤ[X]` and `d : ℕ`, there exists some `h : ℚ[X]` such that for any
large enough `n : ℕ`, `PowerSeries.coeff ℤ n (p * (@invOneSubPow ℤ _ d))` is equal
to `h.eval (n : ℚ)`. This `h` is unique and is called the Hilbert polynomial with
respect to `p` and `d` (`Polynomial.hilbert p d`).
-/

open BigOperators
open PowerSeries

namespace Polynomial

section greatestFactorOneSubNotDvd

variable {R : Type _} [CommRing R] [NeZero (1 : R)] [NoZeroDivisors R]
variable (p : R[X]) (hp : p ≠ 0) (d : ℕ)

/--
Given a polynomial `p`, the greatest factor of `p` that is not divided by `1 - X`.
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
  rw [eval_prod, @Finset.prod_attach ℚ ℕ _ (Finset.range d)
    (fun j => eval n (X - (@Nat.cast ℚ[X] _ k) + (@Nat.cast ℚ[X] _ j) + 1))]
  simp only [eval_add, eval_sub, eval_X, eval_nat_cast, eval_one]
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
    | succ d hd => rw [Finset.prod_range_succ, hd, add_assoc, add_comm (@Nat.cast ℚ _ d),
        ← add_assoc, mul_comm, ← Nat.cast_sub hkn, ← Nat.cast_add_one, ← Nat.cast_add,
        ← Nat.cast_mul, ← Nat.ascFactorial_succ]

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
  · simp only [h, coe_zero, zero_mul, ↓reduceDite, eval_zero, Int.cast_eq_zero]; rfl
  · simp only [h, ↓reduceDite, zsmul_eq_mul]
    have coe_one_sub : (1 - X : ℤ[X]).ToPowerSeries = 1 - (PowerSeries.X : ℤ⟦X⟧) := by
      rw [PowerSeries.ext_iff]; exact fun i => by_cases (fun (hi : i = 0) => by
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
        (p.rootMultiplicity 1 - (d + 1))), one_sub_pow_mul_invOneSubPow_val_eq_one, mul_one,
        ← coe_one_sub, ← coe_pow, ← coe_mul, coeff_coe]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
        (natDegree_pow_rootMultiplicity_sub_mul_greatestFactorOneSubNotDvd_le p h d h1) hn)
    · simp only [h1, ↓reduceIte]
      rw [coe_inj.2 (pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq p h).symm, coe_mul,
        mul_comm ((1 - X : ℤ[X]) ^ p.rootMultiplicity 1).ToPowerSeries, mul_assoc,
        invOneSubPow_eq_inv_one_sub_pow, show d + 1 = p.rootMultiplicity 1 +
        (d - p.rootMultiplicity 1 + 1) by rw [← Nat.sub_add_comm <| Nat.not_lt.mp h1,
        Nat.add_sub_of_le <| Nat.le_of_not_ge h1], pow_add, Units.val_mul, ← mul_assoc
        ((1 - X : ℤ[X]) ^ rootMultiplicity 1 p).ToPowerSeries, coe_pow, coe_one_sub,
        ← invOneSubPow_eq_inv_one_sub_pow]
      simp only [Units.inv_mk, Units.val_pow_eq_pow_val]
      rw [← mul_pow, mul_invOfUnit _ _ <| by simp only [map_sub, map_one,
        constantCoeff_X, sub_zero, Units.val_one], one_pow, one_mul, invOneSubPow,
        show (gFOSND p h).ToPowerSeries = (Finset.sum (Finset.range ((gFOSND p h).natDegree + 1))
        (fun (i : ℕ) => ((gFOSND p h).coeff i) • (X ^ i)) : ℤ[X]).ToPowerSeries by
        simp only [zsmul_eq_mul, coe_inj]; exact as_sum_range_C_mul_X_pow (gFOSND p h)]
      simp only [zsmul_eq_mul]; rw [eval_finset_sum]; simp only [eval_mul, eval_int_cast]
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
      exact (Finset.sum_eq_sum_iff_of_le <| fun i hi => by
        simp only [Finset.mem_range] at hi; simp only [hi, ↓reduceIte, mul_eq_mul_left_iff,
        Nat.cast_inj, Int.cast_eq_zero]; rw [add_comm]).2 <| fun i hi => by
        simp only [Finset.mem_range] at hi; simp only [hi, ↓reduceIte]; rw [add_comm]

/--
The Hilbert polynomial is unique. In other words, for any `h : ℚ[X]`, if `h`
satisfies the key property of the Hilbert polynomial (i.e. for any large enough
`n : ℕ`, `PowerSeries.coeff ℤ n (p * (@invOneSubPow ℤ _ d)) = h.eval (n : ℚ)`),
then `h` is the Hilbert polynomial.
-/
theorem exists_unique_hilbert (p : Polynomial ℤ) (d : ℕ) :
    ∃! (h : ℚ[X]), (∃ (N : ℕ), (∀ (n : ℕ) (_ : N < n),
    PowerSeries.coeff ℤ n (p * (@invOneSubPow ℤ _ d)) = h.eval (n : ℚ))) :=
  ⟨hilbert p d, ⟨p.natDegree, fun n hn => coeff_mul_invOneSubPow_eq_hilbert_eval p d n hn⟩,
  fun q ⟨N, hqN⟩ => eq_of_infinite_eval_eq q (hilbert p d) <| fun hfin => Set.Infinite.image
  (Set.injOn_of_injective Nat.cast_injective _) (Set.Ioi_infinite (max N p.natDegree)) <|
  Set.Finite.subset hfin <| show @Nat.cast ℚ _ '' (Set.Ioi (max N p.natDegree)) ⊆
  (@setOf ℚ fun x => q.eval x = (hilbert p d).eval x) by
  intro x hx; simp only [Set.mem_image, Set.mem_Ioi, max_lt_iff, Set.mem_setOf_eq] at hx ⊢;
  rcases hx with ⟨n, ⟨h1, h2⟩, h3⟩; rw [← h3, ← coeff_mul_invOneSubPow_eq_hilbert_eval p d n h2];
  exact (Rat.ext (congrArg Rat.num (hqN n h1)) (congrArg Rat.den (hqN n h1))).symm⟩

lemma prod_sub_rootMultiplicity_coeff_eq_one (p : ℤ[X]) (d x : ℕ) :
    coeff (∏ x1 in Finset.attach (Finset.range (d - p.rootMultiplicity 1)),
    (X - (x : ℚ[X]) + ↑↑x1 + 1)) (d - p.rootMultiplicity 1) = 1 := by
  let hcoeff := @coeff_prod_of_natDegree_le ℚ ({ x // x ∈ Finset.range
    (d - p.rootMultiplicity 1) }) (Finset.attach (Finset.range (d - p.rootMultiplicity 1))) _
    (fun x1 => X - (x : ℚ[X]) + ↑↑x1 + 1) 1 <| show ∀ x1 ∈ Finset.attach
    (Finset.range (d - p.rootMultiplicity 1)), natDegree (X - (x : ℚ[X]) + ↑↑x1 + 1) ≤ 1 by
    intro x1 _; exact le_trans (natDegree_add_le _ _) <| by
      simp only [natDegree_one, ge_iff_le, zero_le, max_eq_left];
      exact le_trans (natDegree_add_le _ _) <| by
        simp only [natDegree_nat_cast, ge_iff_le, zero_le, max_eq_left];
        exact le_trans (natDegree_sub_le _ _) <| by
          simp only [natDegree_X, natDegree_nat_cast, ge_iff_le, zero_le, max_eq_left, le_refl]
  simp only [Finset.card_attach, Finset.card_range, mul_one, coeff_add, coeff_sub, coeff_X_one,
    coeff_nat_cast_ite, one_ne_zero, ↓reduceIte, CharP.cast_eq_zero, sub_zero, add_zero,
    Finset.prod_const] at hcoeff
  rw [hcoeff, Polynomial.coeff_one]; simp only [one_ne_zero, ↓reduceIte, add_zero, one_pow]

/--
This theorem tells us the specific degree of any non-zero Hilbert polynomial.
-/
theorem natDegree_hilbert (p : ℤ[X]) (d : ℕ) (hh : hilbert p d ≠ 0) :
    (hilbert p d).natDegree = d - p.rootMultiplicity 1 := by
  by_cases h : p = 0
  · exfalso; rw [hilbert] at hh; simp only [h, ↓reduceDite, ne_eq, not_true_eq_false] at hh
  · by_cases h1 : d + 1 ≤ p.rootMultiplicity 1
    · rw [hilbert] at hh
      simp only [h1, ↓reduceIte, dite_eq_ite, ite_self, ne_eq, not_true_eq_false] at hh
    · refine' natDegree_eq_of_le_of_coeff_ne_zero _ _
      · rw [hilbert]; simp only [h, ↓reduceDite, h1, ↓reduceIte, zsmul_eq_mul]
        refine' @natDegree_sum_le_of_forall_le ℕ (Finset.range (natDegree (gFOSND p h) + 1)) ℚ _
          (d - p.rootMultiplicity 1) (fun x => (@Int.cast ℚ[X] _ ((gFOSND p h).coeff x)) *
          preHilbert (d - p.rootMultiplicity 1) x) _
        · intro i _
          refine' le_trans (@natDegree_mul_le ℚ _ (@Int.cast ℚ[X] _ (coeff (gFOSND p h) i))
            (preHilbert (d - p.rootMultiplicity 1) i)) _
          · simp only [natDegree_int_cast, zero_add]; rw [preHilbert]
            refine' le_trans (natDegree_smul_le (@Inv.inv ℚ _
              (d - p.rootMultiplicity 1).factorial) _) _
            · refine' le_trans (natDegree_prod_le (@Finset.attach ℕ (Finset.range
                (d - p.rootMultiplicity 1))) _) _
              · have : ∀ x ∈ Finset.attach (Finset.range (d - p.rootMultiplicity 1)),
                    natDegree (X - (i : ℚ[X]) + ↑↑x + 1) ≤ 1 :=
                  fun x _ => le_trans (natDegree_add_le _ _) <| by
                  simp only [natDegree_one, ge_iff_le, zero_le, max_eq_left];
                  exact le_trans (natDegree_add_le _ _) <| by
                    simp only [natDegree_nat_cast, ge_iff_le, zero_le, max_eq_left];
                    exact le_trans (natDegree_sub_le _ _) <| by simp only [natDegree_X,
                      natDegree_nat_cast, ge_iff_le, zero_le, max_eq_left, le_refl]
                exact le_trans (Finset.sum_le_sum this) <| by simp only [Finset.sum_const,
                  Finset.card_attach, Finset.card_range, smul_eq_mul, mul_one, le_refl]
      · rw [hilbert]
        simp only [h, ↓reduceDite, h1, ↓reduceIte, zsmul_eq_mul, finset_sum_coeff,
          coeff_intCast_mul, ne_eq]
        simp_rw [preHilbert, coeff_smul]
        simp only [Finset.univ_eq_attach, map_natCast, smul_eq_mul]
        simp_rw [prod_sub_rootMultiplicity_coeff_eq_one p]; rw [← Finset.sum_mul]
        simp only [mul_one, mul_eq_zero, _root_.inv_eq_zero, Nat.cast_eq_zero]; rw [not_or]
        constructor
        · rw [show ∑ i in Finset.range ((gFOSND p h).natDegree + 1), @Int.cast ℚ _
            ((gFOSND p h).coeff i) = (gFOSND p h).eval 1 by rw [eval_eq_sum_range]; simp only
            [one_pow, mul_one, Int.cast_sum]]
          intro h'; simp only [Int.cast_eq_zero] at h'; rw [greatestFactorOneSubNotDvd] at h'
          simp only [map_one, eval_mul, eval_pow, eval_neg, eval_one, Int.reduceNeg, mul_eq_zero,
            pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, rootMultiplicity_eq_zero_iff,
            IsRoot.def, not_forall, exists_prop, false_and, false_or] at h'
          let this := (exists_eq_pow_rootMultiplicity_mul_and_not_dvd p h 1).choose_spec.2
          rw [dvd_iff_isRoot] at this; exact this h'
        · exact Nat.factorial_ne_zero _

end Polynomial
