/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic.ComputeDegree

/-! # A generalized Eisenstein criterion

`Polynomial.generalizedEisenstein` :
  Let `R` be an integral domain and `K` an `R`-algebra which is a field.
  Let `q : R[X]` be a monic polynomial which is irreducible in `K[X]`.
  Let `f : R[X]` be a monic polynomial of strictly positive degree
  whose image in `K[X]` is a power of `q`.
  Assume moreover that `f.modByMonic q` is not zero in `(R ⧸ (P ^ 2))[X]`,
  where `P` is the kernel of `algebraMap R K`.
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

namespace Polynomial

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

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

theorem exists_eq_C_leadingCoeff_mul_pow_add {q f : R[X]} {n : ℕ}
    (hq_irr : Irreducible (q.map (algebraMap R K))) (hq_monic : q.Monic)
    (map_dvd_pow_q : f.map (algebraMap R K) ∣ q.map (algebraMap R K) ^ n)
    (hf_lC : algebraMap R K f.leadingCoeff ≠ 0) :
    ∃ m r, f = C f.leadingCoeff * q ^ m + r ∧ map (algebraMap R K) r = 0 := by
  obtain ⟨m, hm⟩ := exists_C_leadingCoeff_mul_pow_of_dvd_pow hq_irr
     (hq_monic.map (algebraMap R K)) map_dvd_pow_q
  use m, f - C f.leadingCoeff * q ^ m, by ring
  rw [Polynomial.map_sub, sub_eq_zero]
  rw [hm]
  simp only [Polynomial.map_mul, map_C, Polynomial.map_pow]
  congr
  rwa [← leadingCoeff_map_of_leadingCoeff_ne_zero]

/-- A generalized Eisenstein criterion

  Let `R` be an integral domain and `K` an `R`-algebra which is a field.
  Let `q : R[X]` be a monic polynomial which is irreducible in `K[X]`.
  Let `f : R[X]` be a monic polynomial of strictly positive degree
  whose image in `K[X]` is a power of `q`.
  Assume moreover that `f.modByMonic q` is not zero in `(R ⧸ (P ^ 2))[X]`,
  where `P` is the kernel of `algebraMap R K`.
  Then `f` is irreducible. -/
theorem generalizedEisenstein [IsDomain R] {q f : R[X]} {p : ℕ}
    (hq_irr : Irreducible (q.map (algebraMap R K))) (hq_monic : q.Monic)
    (hfd0 : 0 < natDegree f) (hf_monic : f.Monic)
    (hfmodP : f.map (algebraMap R K) = q.map (algebraMap R K) ^ p)
    (hfmodP2 : (f.modByMonic q).map (mk ((RingHom.ker (algebraMap R K)) ^ 2)) ≠ 0) :
    Irreducible f where
  not_unit := mt degree_eq_zero_of_isUnit fun h => by
    simp_all [lt_irrefl, natDegree_pos_iff_degree_pos]
  isUnit_or_isUnit' g h h_eq := by
    set P : Ideal R := RingHom.ker (algebraMap R K)
    have hP : P.IsPrime := RingHom.ker_isPrime (algebraMap R K)
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
    have (g : R[X]) (hg_div : g ∣ f) : ∃ m r, g = C g.leadingCoeff * q ^ m + r ∧
          r.map (algebraMap R K) = 0 ∧ (m = 0 → IsUnit g) := by
      have hgP : IsUnit g.leadingCoeff := by
        apply isUnit_of_dvd_unit (y := f.leadingCoeff)
        exact leadingCoeff_dvd_leadingCoeff hg_div
        simp [hf_monic]
      have hgP' : g.leadingCoeff ∉ P := fun h ↦ hP.ne_top (P.eq_top_of_isUnit_mem h hgP)
      obtain ⟨m, r, hg, hr⟩ := exists_eq_C_leadingCoeff_mul_pow_add hq_irr hq_monic
        (by rw [← hfmodP]; exact map_dvd (algebraMap R K) hg_div) hgP'
      use m, r, hg, hr
      intro hm
      rw [hm, pow_zero, mul_one] at hg
      suffices g.natDegree = 0 by
        obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp this
        apply IsUnit.map
        rwa [leadingCoeff_C] at hgP
      by_contra hg'
      apply hgP'
      rw [hg, leadingCoeff, coeff_add, ← hg, coeff_C, if_neg hg', zero_add,
        RingHom.mem_ker, ← coeff_map, hr, coeff_zero]
    obtain ⟨m, r, hg, hr, hm0⟩ := this g (h_eq ▸ dvd_mul_right g h)
    obtain ⟨n, s, hh, hs, hn0⟩ := this h (h_eq ▸ dvd_mul_left h g)
    by_cases hm : m = 0
    · left; exact hm0 hm
    by_cases hn : n = 0
    · right; exact hn0 hn
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
        exact ((dvd_pow_self q hm).mul_left _).mul_right _
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
    · rw [RingHom.mem_ker, ← coeff_map, hr, coeff_zero]
    · rw [RingHom.mem_ker, ← coeff_map, hs, coeff_zero]

example : Irreducible (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set q : ℤ [X] := X ^ 2 + 1 with hq_eq
  let K := ZMod 3
  have h3 : RingHom.ker (algebraMap ℤ K) = Ideal.span {3} := by
    ext a
    rw [algebraMap_int_eq, ZMod.ker_intCastRingHom, Nat.cast_ofNat]
  have hq_monic : q.Monic := leadingCoeff_X_pow_add_one (by norm_num)
  have hq_deg : q.natDegree = 2 := by simp only [q]; compute_degree!
  have hq_deg' : (q.map (algebraMap ℤ K)).natDegree = 2 := by
    rw [natDegree_map_of_leadingCoeff_ne_zero, hq_deg]
    simp [q]
  have hq_irr : Irreducible (q.map (algebraMap ℤ K)) := by
    rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three]
    · apply Multiset.eq_zero_of_forall_not_mem
      intro a
      simp only [algebraMap_int_eq, Polynomial.map_add, Polynomial.map_pow, map_X,
        Polynomial.map_one, mem_roots', ne_eq, IsRoot.def, eval_add, eval_pow, eval_X, eval_one,
        not_and, q, K]
      intro _
      revert a
      decide
    · rw [hq_deg']
    · rw [hq_deg']; norm_num
  set f : ℤ[X] := X ^ 4 - 10 * X ^ 2 + 1 with hf_eq
  have hdeg_f : f.natDegree = 4 := by simp only [hf_eq, K, q]; compute_degree!
  have hlC_f : f.Monic := by
    simp only [Monic, leadingCoeff, hdeg_f, f]
    compute_degree!
  have hfq : f = q ^ 2 - 12 * q + 12 := by ring
  apply generalizedEisenstein (K := K) hq_irr hq_monic (p := 2)
    (by rw [hdeg_f]; norm_num) hlC_f
  · simp only [hfq, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_mul, ← map_ofNat C, Polynomial.map_C]
    have : (algebraMap ℤ K) (12) = 0 := by
      rw [← RingHom.mem_ker, h3, Ideal.mem_span_singleton]
      norm_num
    rw [this]
    simp
  · suffices f %ₘ q = 12 by
      rw [this]
      rw [← map_ofNat C, Polynomial.map_C, ne_eq, C_eq_zero, eq_zero_iff_mem]
      rw [h3, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      norm_num
    rw [hfq]
    rw [← modByMonicHom_apply, LinearMap.map_add]
    convert zero_add _
    · rw [← LinearMap.mem_ker, mem_ker_modByMonic hq_monic]
      rw [pow_two, ← sub_mul]
      apply dvd_mul_left
    · symm
      simp only [modByMonicHom_apply, Polynomial.modByMonic_eq_self_iff hq_monic, f]
      apply Polynomial.degree_lt_degree
      suffices q.natDegree = 2 by
        simp only [this, natDegree_ofNat, f, K, q]
        norm_num
      rw [hq_eq]
      simp only [← C_1, Polynomial.natDegree_X_pow_add_C]

end Polynomial
