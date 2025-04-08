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
  Let `R` be an integral domain
  and let `K` an `R`-algebra which is a an integral domain.
  Let `q : R[X]` be a monic polynomial which is prime in `K[X]`.
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

open Polynomial Ideal.Quotient Ideal RingHom

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]
  {K : Type*} [CommRing K] [IsDomain K] [Algebra R K]

private lemma generalizedEisenstein_aux {q f g : R[X]} {p : ℕ}
    (hq_irr : Prime (q.map (algebraMap R K))) (hq_monic : q.Monic)
    (hf_monic : f.Monic) (hfmodP : f.map (algebraMap R K) = q.map (algebraMap R K) ^ p)
    (hg_div : g ∣ f) :
    ∃ m r, g = C g.leadingCoeff * q ^ m + r ∧
          r.map (algebraMap R K) = 0 ∧ (m = 0 → IsUnit g) := by
  set P := ker (algebraMap R K)
  have hP : P.IsPrime := ker_isPrime (algebraMap R K)
  have hgP : IsUnit g.leadingCoeff := by
    apply isUnit_of_dvd_unit (y := f.leadingCoeff)
    exact leadingCoeff_dvd_leadingCoeff hg_div
    simp [hf_monic]
  have hgP' : g.leadingCoeff ∉ P := fun h ↦ hP.ne_top (P.eq_top_of_isUnit_mem h hgP)
  have map_dvd_pow_q : g.map  (algebraMap R K) ∣ q.map (algebraMap R K) ^ p := by
    rw [← hfmodP]
    exact Polynomial.map_dvd _ hg_div
  obtain ⟨m, hm, hf⟩ := (dvd_prime_pow hq_irr _).mp map_dvd_pow_q
  set r := g - C g.leadingCoeff * q ^ m
  have hg : g = C g.leadingCoeff * q ^ m + r := by ring
  have hr : r.map (algebraMap R K) = 0 := by
    obtain ⟨u, hu⟩ := hf.symm
    obtain ⟨a, ha, ha'⟩ := Polynomial.isUnit_iff.mp u.isUnit
    suffices C (algebraMap R K g.leadingCoeff) = u by
      simp [r, ← this, Polynomial.map_sub, ← hu, Polynomial.map_mul, map_C,
        Polynomial.map_pow, sub_eq_zero, mul_comm]
    rw [← leadingCoeff_map_of_leadingCoeff_ne_zero _ hgP', ← hu, ← ha',
      leadingCoeff_mul, leadingCoeff_C, (hq_monic.map _).pow m, one_mul]
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
    mem_ker, ← coeff_map, hr, coeff_zero]

 /-- A generalized Eisenstein criterion

  Let `R` be an integral domain and `K` an `R`-algebra which is a field.
  Let `q : R[X]` be a monic polynomial which is prime in `K[X]`.
  Let `f : R[X]` be a monic polynomial of strictly positive degree
  whose image in `K[X]` is a power of `q`.
  Assume moreover that `f.modByMonic q` is not zero in `(R ⧸ (P ^ 2))[X]`,
  where `P` is the kernel of `algebraMap R K`.
  Then `f` is irreducible. -/
theorem generalizedEisenstein {q f : R[X]} {p : ℕ}
    (hq_irr : Prime (q.map (algebraMap R K))) (hq_monic : q.Monic)
    (hfd0 : 0 < natDegree f) (hf_monic : f.Monic)
    (hfmodP : f.map (algebraMap R K) = q.map (algebraMap R K) ^ p)
    (hfmodP2 : (f.modByMonic q).map (mk ((ker (algebraMap R K)) ^ 2)) ≠ 0) :
    Irreducible f where
  not_unit := mt degree_eq_zero_of_isUnit fun h => by
    simp_all [lt_irrefl, natDegree_pos_iff_degree_pos]
  isUnit_or_isUnit' g h h_eq := by
    -- We have to show that factorizations `f = g * h` are trivial
    set P : Ideal R := ker (algebraMap R K)
    have hP : P.IsPrime := ker_isPrime (algebraMap R K)
    obtain ⟨m, r, hg, hr, hm0⟩ :=
      generalizedEisenstein_aux hq_irr hq_monic hf_monic hfmodP (h_eq ▸ dvd_mul_right g h)
    obtain ⟨n, s, hh, hs, hn0⟩ :=
      generalizedEisenstein_aux hq_irr hq_monic hf_monic hfmodP (h_eq ▸ dvd_mul_left h g)
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

-- move
theorem CharP.ker_intAlgebraMap_eq_span
    {R : Type*} [Ring R] (p : ℕ) [CharP R p] :
    RingHom.ker (algebraMap ℤ R) = Ideal.span {(p : ℤ)} := by
  ext a
  simp [CharP.intCast_eq_zero_iff R p, Ideal.mem_span_singleton]

example : Irreducible (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]) := by
  -- We will apply the generalized Eisenstein criterion with `q = X ^ 2 + 1` and `K = ZMod 3`.
  set f : ℤ[X] := X ^ 4 - 10 * X ^ 2 + 1 with hf_eq
  have hdeg_f : f.natDegree = 4 := by unfold f; compute_degree!
  set q : ℤ [X] := X ^ 2 + 1 with hq_eq
  have hq_deg : q.natDegree = 2 := by unfold q; compute_degree!
  have hq_monic : q.Monic := by unfold q; monicity!
  have hfq : f = q ^ 2 - 12 * q + 12 := by ring
   -- On the other hand, `f %ₘ q = 12`, which is not a multiple of `9`.
  apply generalizedEisenstein (K := ZMod 3) (q := q) (p := 2)
  · set q₃ : (ZMod 3)[X] := X ^ 2 + 1
    have hdeg_q₃ : q₃.natDegree = 2 := by unfold q₃; compute_degree!
    suffices Irreducible q₃ by simpa [q] using this.prime
    apply irreducible_of_degree_le_three_of_not_isRoot
      (by simp_all) (by simp_all [q₃]; decide)
  · unfold q; monicity!
  · simp_all
  · unfold f; monicity!
  · rw [hfq, ← sub_eq_zero]
    have : (12 : (ZMod 3)[X]) = 0 := by apply CharP.ofNat_eq_zero' _ 3 12; norm_num
    simp [q, this]
  · suffices f %ₘ q = 12 by
      rw [this, ← map_ofNat C, Polynomial.map_C, ne_eq, C_eq_zero, eq_zero_iff_mem,
      CharP.ker_intAlgebraMap_eq_span 3, span_singleton_pow, mem_span_singleton]
      norm_num
    rw [hfq, ← modByMonicHom_apply, LinearMap.map_add]
    convert zero_add _
    · rw [← LinearMap.mem_ker, mem_ker_modByMonic hq_monic]
      rw [pow_two, ← sub_mul]
      apply dvd_mul_left
    · symm
      simp only [modByMonicHom_apply, Polynomial.modByMonic_eq_self_iff hq_monic, f]
      rw [show q.degree = 2 by unfold q; compute_degree!]
      rw [show degree _ = 0 by compute_degree!]
      norm_num

end Polynomial
