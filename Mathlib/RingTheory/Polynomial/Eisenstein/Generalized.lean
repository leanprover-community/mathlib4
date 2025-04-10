/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.CharP.Quotient
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Polynomial.Content

/-! # A generalized Eisenstein criterion

`Polynomial.generalizedEisenstein` :
  Let `R` be an integral domain
  and let `K` an `R`-algebra which is a field
  Let `q : R[X]` be a monic polynomial which is prime in `K[X]`.
  Let `f : R[X]` be a polynomial of strictly positive degree
  satisfying the following properties:
  * the image of `f` in `K[X]` is a power of `q`.
  * the leading coefficient of `f` is not zero in `K`
  * the polynomial `f` is primitive.
  Assume moreover that `f.modByMonic q` is not zero in `(R ⧸ (P ^ 2))[X]`,
  where `P` is the kernel of `algebraMap R K`.
  Then `f` is irreducible.

The Eisenstein criterion is the particular case where `q := X`.

The case of a polynomial `q := X - a` is interesting,
then the mod `P ^ 2` hypothesis can rephrased as saying
that `f.derivative.eval a ∉ P ^ 2`. (TODO)
The case of cyclotomic polynomials of prime index `p`
could be proved directly using that result, taking `a = 1`.

We give in `Archive.Examples.Eisenstein` an explicit example
of application of this criterion.

## TODO

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

namespace Polynomial

open Ideal.Quotient Ideal RingHom

variable {R : Type*} [CommRing R] [IsDomain R]
  {K : Type*}
  -- [CommRing K] [IsDomain K] [Algebra R K]
  [Field K] [Algebra R K]

private lemma generalizedEisenstein_aux {q f g : R[X]} {p : ℕ}
    (hq_irr : Irreducible (q.map (algebraMap R K))) (hq_monic : q.Monic)
    (hf_lC : algebraMap R K f.leadingCoeff ≠ 0)
    (hf_prim : f.IsPrimitive)
    (hfmodP : f.map (algebraMap R K) =
      C (algebraMap R K f.leadingCoeff) * q.map (algebraMap R K) ^ p)
    (hg_div : g ∣ f) :
    ∃ m r, g = C g.leadingCoeff * q ^ m + r ∧
          r.map (algebraMap R K) = 0 ∧ (m = 0 → IsUnit g) := by
  set P := ker (algebraMap R K)
  have hP : P.IsPrime := ker_isPrime (algebraMap R K)
  have hgP : g.leadingCoeff ∉ P := by
    simp only [mem_ker, P]
    obtain ⟨h, rfl⟩ := hg_div
    simp only [leadingCoeff_mul, map_mul, ne_eq, mul_eq_zero, not_or] at hf_lC
    exact hf_lC.1
  have map_dvd_pow_q :
      g.map  (algebraMap R K) ∣ q.map (algebraMap R K) ^ p := by
    rw [← IsUnit.dvd_mul_left _, ← hfmodP]
    · exact Polynomial.map_dvd _ hg_div
    · simp_all
  obtain ⟨m, hm, hf⟩ := (dvd_prime_pow hq_irr.prime _).mp map_dvd_pow_q
  set r := g - C g.leadingCoeff * q ^ m
  have hg : g = C g.leadingCoeff * q ^ m + r := by ring
  have hr : r.map (algebraMap R K) = 0 := by
    obtain ⟨u, hu⟩ := hf.symm
    obtain ⟨a, ha, ha'⟩ := Polynomial.isUnit_iff.mp u.isUnit
    suffices C (algebraMap R K g.leadingCoeff) = u by
      simp [r, ← this, Polynomial.map_sub, ← hu, Polynomial.map_mul, map_C,
        Polynomial.map_pow, sub_eq_zero, mul_comm]
    rw [← leadingCoeff_map_of_leadingCoeff_ne_zero _ hgP, ← hu, ← ha',
      leadingCoeff_mul, leadingCoeff_C, (hq_monic.map _).pow m, one_mul]
  use m, r, hg, hr
  intro hm
  rw [isPrimitive_iff_isUnit_of_C_dvd] at hf_prim
  rw [hm, pow_zero, mul_one] at hg
  suffices g.natDegree = 0 by
    obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp this
    apply IsUnit.map
    apply hf_prim
    rwa [leadingCoeff_C] at hgP
  by_contra hg'
  apply hgP
  rw [hg, leadingCoeff, coeff_add, ← hg, coeff_C, if_neg hg', zero_add,
    mem_ker, ← coeff_map, hr, coeff_zero]

 /-- A generalized Eisenstein criterion

  Let `R` be an integral domain and `K` an `R`-algebra which is a domain.
  Let `q : R[X]` be a monic polynomial which is prime in `K[X]`.
  Let `f : R[X]` be a primitive polynomial of strictly positive degree
  whose leading coefficient is not zero in `K`
  and such that the image `f` in `K[X]` is a power of `q`.
  Assume moreover that `f.modByMonic q` is not zero in `(R ⧸ (P ^ 2))[X]`,
  where `P` is the kernel of `algebraMap R K`.
  Then `f` is irreducible. -/
theorem generalizedEisenstein {q f : R[X]} {p : ℕ}
    (hq_irr : Irreducible (q.map (algebraMap R K))) (hq_monic : q.Monic)
    (hf_prim : f.IsPrimitive)
    (hfd0 : 0 < natDegree f)
    (hfP : algebraMap R K f.leadingCoeff ≠ 0)
    (hfmodP : f.map (algebraMap R K) =
      C (algebraMap R K f.leadingCoeff) * q.map (algebraMap R K) ^ p)
    (hfmodP2 : (f.modByMonic q).map (mk ((ker (algebraMap R K)) ^ 2)) ≠ 0) :
    Irreducible f where
  not_unit := mt degree_eq_zero_of_isUnit fun h => by
    simp_all [lt_irrefl, natDegree_pos_iff_degree_pos]
  isUnit_or_isUnit' g h h_eq := by
    -- We have to show that factorizations `f = g * h` are trivial
    set P : Ideal R := ker (algebraMap R K)
    have hP : P.IsPrime := ker_isPrime (algebraMap R K)
    obtain ⟨m, r, hg, hr, hm0⟩ :=
      generalizedEisenstein_aux hq_irr hq_monic hfP hf_prim hfmodP (h_eq ▸ dvd_mul_right g h)
    obtain ⟨n, s, hh, hs, hn0⟩ :=
      generalizedEisenstein_aux hq_irr hq_monic hfP hf_prim hfmodP (h_eq ▸ dvd_mul_left h g)
    by_cases hm : m = 0
    -- If `m = 0`, `generalizedEisenstein_aux` shows that `g` is a unit.
    · left; exact hm0 hm
    by_cases hn : n = 0
    -- If `n = 0`, `generalizedEisenstein_aux` shows that `h` is a unit.
    · right; exact hn0 hn
    -- Otherwise, we will get a contradiction by showing that `f %ₘ q` is zero mod `P ^ 2`.
    exfalso
    apply hfmodP2
    suffices f %ₘ q = (r * s) %ₘ q by
      -- Since the coefficients of `r` and `s` are in `P`, those of `r * s` are in `P ^ 2`
      simp only [ext_iff, ← coeff_map, eq_zero_iff_mem]
      rw [← ext_iff, this, map_modByMonic _ hq_monic]
      convert zero_modByMonic _
      ext n
      rw [coeff_map, coeff_mul, map_sum, coeff_zero]
      apply Finset.sum_eq_zero
      intro x hx
      rw [eq_zero_iff_mem, pow_two]
      apply mul_mem_mul
      · rw [mem_ker, ← coeff_map, hr, coeff_zero]
      · rw [mem_ker, ← coeff_map, hs, coeff_zero]
    -- It remains to prove the equality `f %ₘ q = (r * s) %ₘ q`, which is straightforward
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

end Polynomial
