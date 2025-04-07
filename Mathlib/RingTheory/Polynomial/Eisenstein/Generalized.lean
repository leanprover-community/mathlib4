/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.ZMod.QuotientRing

/-! # A generalized Eisenstein criterion

`Polynomial.generalizedEisenstein` :
  Let `R` be an integral domain, `P` a prime ideal of `R` and
  let `K` be the field of fractions o f `R ⧸ P`.
  Let `q : R[X]` be a monic polynomial which is irreducible in `K[X]`.
  Let `f : R[X]` be a monic polynomial of strictly positive degree
  whose image in `K[X]` is a power of `q`.
  Assume moreover that `f.modByMonic q` is not zero in `(R ⧸ (P ^ 2))[X]`.
  Then `f` is irreducible.

The Eisenstein criterion is the particular case where `q := X`.

The case of a polynomial `q := X - a` is interesting,
then the mod `P ^ 2` hypothesis can rephrased as saying
that `f.derivative.eval a ∉ P ^ 2`. (TODO)
The case of cyclotomic polynomials of prime index `p` could be proved directly
using that result, taking `a = 1`; the derivative is `p`.

We give a (possibly non convincing) application to the irreducibility
of the polynomial `X ^ 4 - 10 * X + 1` in `ℤ[X]`.
One argues modulo `3`, with `q := X ^ 2 + 1`.

## Remark

The result can also be generalized to the case where
the leading coefficients of `f` and `q` do not belong to `P`.
(By localization at `P`, make these coefficients invertible.)
There are two obstructions, though :

* Usually, one will only obtain irreducibility in `F[X]`, where `F` is the field
of fractions of `R`. (If `R` is a UFD, this will be close to what is wanted,
but not in general.)

* The mod `P ^ 2` hypothesis will have to be rephrased to a condition
in the second symbolic power of `P`. When `P` is a maximal ideal,
that symbolic power coincides with `P ^ 2`, but not in general.

-/

open Polynomial Ideal.Quotient

theorem Ideal.IsPrime.mul_not_mem
    {R : Type*} [CommRing R] {P : Ideal R} (hP : P.IsPrime) {a b : R}
    (ha : a ∉ P) (hb : b ∉ P) : a * b ∉ P := fun h ↦
  hb ((hP.mem_or_mem h).resolve_left ha)

namespace Polynomial

variable {R : Type*} [CommRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  {P : Ideal R}
  {K : Type*} [Field K] [Algebra R K] [Algebra (R ⧸ P) K]
    [IsScalarTower R (R ⧸ P) K] [IsFractionRing (R ⧸ P) K]
  {q : R[X]}

theorem exists_C_leadingCoeff_mul_pow_of_dvd_pow
    {q : K[X]} (hq : Irreducible q) (hq' : Monic q)
    {f : K[X]} {n : ℕ} (hn : f ∣ q ^ n) :
    ∃ m, f = C f.leadingCoeff * q ^ m := by
  obtain ⟨m, hm, hf⟩ := (dvd_prime_pow hq.prime _).mp hn
  use m
  obtain ⟨u, hu⟩ := hf
  rw [mul_comm, eq_comm, ← Units.inv_mul_eq_iff_eq_mul] at hu
  rw [← hu, leadingCoeff_mul]
  congr
  simp only [leadingCoeff_pow, hq', Monic.leadingCoeff, one_pow, mul_one]
  obtain ⟨a, ha, ha'⟩ := Polynomial.isUnit_iff.mp (u⁻¹).isUnit
  rw [← ha', leadingCoeff_C]

theorem exists_eq_C_leadingCoeff_mul_pow_add
    (hq_irr : Irreducible (q.map (algebraMap R K))) (hq_monic : q.Monic)
    {f : R[X]} {n : ℕ}
    (map_dvd_pow_q : f.map (algebraMap R K) ∣ q.map (algebraMap R K) ^ n)
    (_ : f.leadingCoeff ∉ P) :
    ∃ m r, f = C f.leadingCoeff * q ^ m + r ∧ map (algebraMap R (R ⧸P)) r = 0 := by
  obtain ⟨m, hm⟩ := exists_C_leadingCoeff_mul_pow_of_dvd_pow hq_irr
     (hq_monic.map (algebraMap R K)) map_dvd_pow_q
  use m, f - C f.leadingCoeff * q ^ m, by ring
  rw [Polynomial.map_sub, sub_eq_zero]
  apply (map_injective_iff (algebraMap (R ⧸ P) K)).mpr (FaithfulSMul.algebraMap_injective _ _)
  simp only  [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  rw  [hm, Polynomial.map_mul, map_C, Polynomial.map_pow]
  congr
  rw [← leadingCoeff_map_of_leadingCoeff_ne_zero, hm, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_pow, hq_monic.map, one_pow, mul_one]
  rwa [IsScalarTower.algebraMap_apply R (R ⧸ P) K, ne_eq,
    FaithfulSMul.algebraMap_eq_zero_iff, Ideal.Quotient.algebraMap_eq, eq_zero_iff_mem]

/-- A generalized Eisenstein criterion -/
theorem generalizedEisenstein [IsDomain R] (hP : P.IsPrime)
    (hq_irr : Irreducible (q.map (algebraMap R K))) (hq_monic : q.Monic)
    {f : R[X]} {p : ℕ}
    (hfd0 : 0 < natDegree f) (hf_monic : f.Monic)
    (hfmodP : f.map (algebraMap R K) = q.map (algebraMap R K) ^ p)
    (hfmodP2 : (f.modByMonic q).map (mk (P ^ 2)) ≠ 0) : Irreducible f where
  not_unit := mt degree_eq_zero_of_isUnit fun h => by
      simp_all [lt_irrefl, natDegree_pos_iff_degree_pos]
    isUnit_or_isUnit' g h h_eq := by
      have hgP' : IsUnit g.leadingCoeff := by
        apply isUnit_of_mul_isUnit_left (y  := h.leadingCoeff)
        simp [← leadingCoeff_mul, ← h_eq, hf_monic]
      have hgP : g.leadingCoeff ∉ P :=
        fun hgP ↦ hP.ne_top (Ideal.eq_top_of_isUnit_mem P hgP hgP')
      have hhP' : IsUnit h.leadingCoeff := by
        apply isUnit_of_mul_isUnit_right (x  := g.leadingCoeff)
        simp [← leadingCoeff_mul, ← h_eq, hf_monic]
      have hhP : h.leadingCoeff ∉ P :=
        fun hhP ↦ hP.ne_top (Ideal.eq_top_of_isUnit_mem P hhP hhP')
      obtain ⟨m, r, hg, hr⟩ := exists_eq_C_leadingCoeff_mul_pow_add hq_irr hq_monic
        (by rw [← hfmodP, h_eq, Polynomial.map_mul]; apply dvd_mul_right) hgP
      obtain ⟨n, s, hh, hs⟩ := exists_eq_C_leadingCoeff_mul_pow_add hq_irr hq_monic
        (by rw [← hfmodP, h_eq, Polynomial.map_mul]; apply dvd_mul_left) hhP
      by_cases hm : m = 0
      · rw [hm, pow_zero, mul_one] at hg
        left
        suffices g.natDegree = 0 by
          obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp this
          apply IsUnit.map
          rwa [leadingCoeff_C] at hgP'
        by_contra hg'
        apply hgP
        rw [hg, leadingCoeff, coeff_add, ← hg, coeff_C, if_neg hg', zero_add,
          ← eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq P, ← coeff_map, hr, coeff_zero]
      by_cases hn : n = 0
      · rw [hn, pow_zero, mul_one] at hh
        right
        suffices h.natDegree = 0 by
          obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp this
          apply IsUnit.map
          rwa [leadingCoeff_C] at hhP'
        by_contra hh'
        apply hhP
        rw [hh, leadingCoeff, coeff_add, ← hh, coeff_C, if_neg hh', zero_add,
          ← eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq P, ← coeff_map, hs, coeff_zero]
      have : f %ₘ q = (r * s) %ₘ q := by
        rw [h_eq, hg, hh]
        simp only [add_mul, mul_add, map_add, ← modByMonicHom_apply]
        simp only [← add_assoc, modByMonicHom_apply]
        convert zero_add _
        convert zero_add _
        · convert zero_add _
          · rw [modByMonic_eq_zero_iff_dvd hq_monic]
            exact ((dvd_pow_self q hn).mul_left _).mul_left _
          · symm
            rw [modByMonic_eq_zero_iff_dvd hq_monic]
            simp only [← mul_assoc]
            exact (dvd_pow_self q hn).mul_left _
        · symm
          rw [modByMonic_eq_zero_iff_dvd hq_monic]
          exact (dvd.mul_left _ _).mul.right _ 
          -- was:  apply Dvd.dvd.mul_right; apply Dvd.dvd.mul_left
          exact dvd_pow_self q hm
      exfalso
      apply hfmodP2
      simp only [ext_iff, ← coeff_map, eq_zero_iff_mem]
      rw [← ext_iff, this, map_modByMonic _ hq_monic]
      convert zero_modByMonic _
      ext n
      rw [coeff_map, coeff_mul, map_sum, coeff_zero]
      apply Finset.sum_eq_zero
      intro x hx
      rw [eq_zero_iff_mem, pow_two]
      apply Ideal.mul_mem_mul
      · rw [← eq_zero_iff_mem, ← coeff_map, ← Ideal.Quotient.algebraMap_eq P, hr, coeff_zero]
      · rw [← eq_zero_iff_mem, ← coeff_map, ← Ideal.Quotient.algebraMap_eq P, hs, coeff_zero] }

example : Irreducible (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]) := by
  set P : Ideal ℤ := Ideal.span {3}
  have hP' : P.IsMaximal := by
    apply PrincipalIdealRing.isMaximal_of_irreducible
    refine Prime.irreducible Int.prime_three
  have hP : P.IsPrime := hP'.isPrime
  letI : Field (ℤ ⧸ P) := Ideal.Quotient.field P
  set q : ℤ [X] := X ^ 2 + 1 with hq_eq
  let K := ℤ ⧸ P
  have hq_monic : q.Monic := leadingCoeff_X_pow_add_one (by norm_num)
  have hq_deg : (X ^ 2 + 1 : K[X]).natDegree = 2 := by
    simp only [← C_1, Polynomial.natDegree_X_pow_add_C]
  have hq_irr : Irreducible (q.map (algebraMap ℤ K)) := by
    have : map (algebraMap ℤ K) q = X ^ 2 + 1 := by simp [q]
    rw [this]
    have mod3 : ∀ u : ZMod 3, u ^ 2 + 1 ≠ 0 := by decide
    rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three]
    · apply Multiset.eq_zero_of_forall_not_mem
      intro a
      simp only [mem_roots', ne_eq, IsRoot.def, eval_add, eval_pow, eval_X, eval_one, not_and]
      intro _
      let u := Int.quotientSpanNatEquivZMod 3 a
      have : a ^ 2 + 1 = (Int.quotientSpanNatEquivZMod 3).symm (u ^ 2 + 1) := by simp [u]
      rw [this]
      rw [← ne_eq, RingEquiv.map_ne_zero_iff (Int.quotientSpanNatEquivZMod 3).symm]
      apply mod3
    · rw [hq_deg]
    · rw [hq_deg]; norm_num
  set f : ℤ[X] := X ^ 4 - 10 * X ^ 2 + 1 with hf_eq
  have hdeg_f : f.natDegree = 4 := by
    simp [hf_eq]
    conv_rhs => rw [← natDegree_X_pow (R := ℤ) 4]
    apply natDegree_eq_of_degree_eq
    rw [sub_add]
    apply degree_sub_eq_left_of_degree_lt
    apply lt_of_le_of_lt (degree_sub_le _ _)
    rw [← map_ofNat C, degree_mul, degree_C, degree_X_pow]
    simp; norm_num; norm_num
  have hlC_f : f.Monic := by
    suffices coeff (1 : ℤ[X]) 4 = 0 by
      simp [Monic, leadingCoeff, hdeg_f, f, this]
    rw [← C_1, coeff_C, if_neg (by norm_num)]
  have hfq : f = q ^ 2 - 12 * q + 12 := by ring
  apply generalizedEisenstein hP (K := K) hq_irr hq_monic (p := 2)
    (by rw [hdeg_f]; norm_num) hlC_f
  · simp only [hfq, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_mul, ← map_ofNat C, Polynomial.map_C]
    have : (algebraMap ℤ K) (12) = 0 := by
      rw [IsScalarTower.algebraMap_eq ℤ (ℤ ⧸ P) K, RingHom.comp_apply]
      convert map_zero _
      simp only [Ideal.Quotient.algebraMap_eq P, eq_zero_iff_mem, P, Ideal.mem_span_singleton]
      · norm_num
      · exact Submodule.Quotient.instZeroQuotient P
      · exact AddMonoidHomClass.toZeroHomClass
    rw [this]
    simp
  · suffices f %ₘ q = 12 by
      rw [this]
      rw [← map_ofNat C, Polynomial.map_C, ne_eq, C_eq_zero, eq_zero_iff_mem]
      simp [P, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [hfq]
    rw [← modByMonicHom_apply, LinearMap.map_add]
    convert zero_add _
    · rw [← LinearMap.mem_ker, mem_ker_modByMonic hq_monic]
      rw [pow_two, ← sub_mul]
      apply dvd_mul_left
    · symm
      simp only [modByMonicHom_apply, Polynomial.modByMonic_eq_self_iff hq_monic, f, P]
      apply Polynomial.degree_lt_degree
      suffices q.natDegree = 2 by
        simp only [this, natDegree_ofNat, f, P, K, q]
        norm_num
      rw [hq_eq]
      simp only [← C_1, Polynomial.natDegree_X_pow_add_C]

end Polynomial
