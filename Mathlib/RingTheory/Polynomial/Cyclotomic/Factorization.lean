/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Factorization of cyclotomic polynomials over finite fields

We compute the degree of the irreducible factors of the `n`-th cyclotomic polynomial over a finite
field of characteristic `p`, where `p` and `n` are coprime.

## Main results

* `Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible` : Let `K` be a finite field of cardinality
  `p ^ f` and let `P` be an irreducible factor of the `n`-th cyclotomic polynomial over `K`, where
  `p` and `n` are coprime. Then the degree of `P` is the multiplicative order of `p ^ f` modulo `n`.

-/

namespace Polynomial

variable {K : Type*} [Field K] [Fintype K] {p f n : ℕ} {P : K[X]}
  (hK : Fintype.card K = p ^ f) (hn : p.Coprime n)

open ZMod AdjoinRoot FiniteField Multiset

include hK

private lemma f_ne_zero : f ≠ 0 := fun h0 ↦ not_subsingleton K <|
    Fintype.card_le_one_iff_subsingleton.mp <| by simpa [h0] using hK.le

variable [hp : Fact p.Prime]

/-- The degree of an irreducible monic factor of the `n`-th cyclotomic polynomial over a finite
  field. This is a special case of `natDegree_of_dvd_cyclotomic_of_irreducible` below. -/
private theorem natDegree_of_dvd_cyclotomic_of_irreducible_of_monic (hP : P ∣ cyclotomic n K)
    (hPirr : Irreducible P) (hPmo : P.Monic) :
    P.natDegree = orderOf (unitOfCoprime _ (hn.pow_left f)) := by
  have : Fact (Irreducible P) := ⟨hPirr⟩
  have := hPmo.finite_adjoinRoot
  have : Finite (AdjoinRoot P) := Module.finite_of_finite K
  have hζ : IsPrimitiveRoot (root P) n := by
    have : NeZero (n : AdjoinRoot P) := by
      suffices NeZero (n : K) by
        simpa using NeZero.of_injective (algebraMap K (AdjoinRoot P)).injective
      have := charP_of_card_eq_prime_pow hK
      exact ⟨fun h0 ↦ Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p, hp.out, dvd_pow_self p (f_ne_zero hK), (CharP.cast_eq_zero_iff K p n).mp h0⟩
          (hn.pow_left f)⟩
    simpa [← isRoot_cyclotomic_iff] using (isRoot_root P).dvd
      (by simpa using map_dvd (algebraMap K (AdjoinRoot P)) hP)
  let pB := powerBasis hPirr.ne_zero
  rw [← powerBasis_dim hPirr.ne_zero, ← pB.finrank, ← orderOf_frobeniusAlgEquivOfAlgebraic]
  have hζ' := isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, pos_of_ne_zero (fun h0 ↦ by simp [h0, hp.out.ne_one] at hn),
      hζ.pow_eq_one⟩
  refine dvd_antisymm
    (orderOf_dvd_iff_pow_eq_one.mpr <| AlgEquiv.coe_algHom_injective <| pB.algHom_ext ?_)
    (orderOf_dvd_iff_pow_eq_one.mpr <| Units.ext ?_)
  · simp only [AlgHom.coe_coe, AlgEquiv.coe_pow, AlgEquiv.one_apply,
      coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, hK]
    nth_rewrite 2 [← pow_one pB.gen]
    rw [powerBasis_gen hPirr.ne_zero, hζ'.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf,
      ← natCast_eq_natCast_iff]
    simpa only [Nat.cast_pow, Nat.cast_one, coe_unitOfCoprime, Units.val_one,
      Units.val_pow_eq_pow_val] using Units.val_inj.mpr <| pow_orderOf_eq_one
      (unitOfCoprime _ (hn.pow_left f))
  · let φ := frobeniusAlgEquivOfAlgebraic K (AdjoinRoot P)
    have : (φ ^ orderOf φ) (root P) = root P := by simp [pow_orderOf_eq_one φ]
    simp only [AlgEquiv.coe_pow, φ, coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, hK] at this
    rw [Units.val_one, ← Nat.cast_one, Units.val_pow_eq_pow_val, coe_unitOfCoprime,
      ← Nat.cast_pow, natCast_eq_natCast_iff, hζ.eq_orderOf, ← hζ'.pow_eq_pow_iff_modEq, this,
      pow_one]

/-- Let `K` be a finite field of cardinality `p ^ f` and let `P` be an irreducible factor of the
  `n`-th cyclotomic polynomial over `K`, where `p` and `n` are coprime. Then the degree of `P` is
  the multiplicative order of `p ^ f` modulo `n`. -/
theorem natDegree_of_dvd_cyclotomic_of_irreducible (hP : P ∣ cyclotomic n K)
    (hPirr : Irreducible P) : P.natDegree = orderOf (unitOfCoprime _ (hn.pow_left f)) := by
  obtain ⟨A, hA⟩ := hP
  have hQ : P * C P.leadingCoeff⁻¹ ∣ cyclotomic n K := by
    refine ⟨A * C P.leadingCoeff, ?_⟩
    calc
      _ = P * A := hA
      _ = P * (C P.leadingCoeff⁻¹ * C P.leadingCoeff) * A := by
        simp [← C_mul, leadingCoeff_ne_zero.mpr hPirr.ne_zero]
      _ = _ := by ring
  simpa [← natDegree_mul_leadingCoeff_self_inv P] using
    natDegree_of_dvd_cyclotomic_of_irreducible_of_monic hK hn hQ
    (irreducible_mul_leadingCoeff_inv.mpr hPirr) (monic_mul_leadingCoeff_inv hPirr.ne_zero)

open UniqueFactorizationMonoid in
/-- Let `K` be a finite field of cardinality `p ^ f` and let `P` be a factor of the `n`-th
  cyclotomic polynomial over `K`, where `p` and `n` are coprime. If the degree of `P` is
  the multiplicative order of `p ^ f` modulo `n` then `P` is irreducible. -/
theorem irreducible_of_dvd_cyclotomic_of_natDegree (hP : P ∣ cyclotomic n K)
    (hPdeg : P.natDegree = orderOf (unitOfCoprime _ (hn.pow_left f))) : Irreducible P := by
  classical
  have hP0 : P ≠ 0 := ne_zero_of_dvd_ne_zero (cyclotomic_ne_zero n K) hP
  obtain ⟨Q, HQ⟩ := exists_mem_normalizedFactors hP0 <| not_isUnit_of_natDegree_pos _ <|
    pos_of_ne_zero <| fun h ↦ orderOf_eq_zero_iff.mp (h ▸ hPdeg.symm) <| isOfFinOrder_of_finite ..
  refine (associated_of_dvd_of_natDegree_le (dvd_of_mem_normalizedFactors HQ) hP0 ?_).irreducible
    (irreducible_of_normalized_factor Q HQ)
  rw [hPdeg, ← natDegree_of_dvd_cyclotomic_of_irreducible hK hn ?_
    (irreducible_of_normalized_factor Q HQ)]
  exact dvd_of_mem_normalizedFactors <| mem_of_le
    ((dvd_iff_normalizedFactors_le_normalizedFactors hP0 (cyclotomic_ne_zero n K)).mp hP) HQ

omit hK in
/-- Let `P` be a factor of the `n`-th cyclotomic polynomial over `ZMod p`, where `p` does not divide
  `n`. If the degree of `P` is the multiplicative order of `p` modulo `n` then `P` is
  irreducible. -/
theorem _root_.ZMod.irreducible_of_dvd_cyclotomic_of_natDegree {P : (ZMod p)[X]} (hpn : ¬p ∣ n)
    (hP : P ∣ cyclotomic n (ZMod p))
    (hPdeg : P.natDegree = orderOf (unitOfCoprime _ (hp.1.coprime_iff_not_dvd.mpr hpn))) :
    Irreducible P :=
  Polynomial.irreducible_of_dvd_cyclotomic_of_natDegree (f := 1) (p := p) (by simp)
    (by simpa using hp.1.coprime_iff_not_dvd.mpr hpn) hP (by simpa)

open UniqueFactorizationMonoid Nat

variable [DecidableEq K]

theorem natDegree_of_mem_normalizedFactors_cyclotomic
    (hP : P ∈ normalizedFactors (cyclotomic n K)) :
    P.natDegree = orderOf (unitOfCoprime _ (hn.pow_left f)) :=
  natDegree_of_dvd_cyclotomic_of_irreducible hK hn (dvd_of_mem_normalizedFactors hP)
    (irreducible_of_normalized_factor P hP)

/-- Let `K` be a finite field of cardinality `p ^ f` and let `P` be an irreducible factor of the
  `n`-th cyclotomic polynomial over `K`, where `p` and `n` are coprime. This result computes the
  number of distinct irreducible factors of `cyclotomic n K`. -/
theorem normalizedFactors_cyclotomic_card : (normalizedFactors (cyclotomic n K)).toFinset.card =
    φ n / orderOf (unitOfCoprime _ (hn.pow_left f)) := by
  have h := prod_normalizedFactors (cyclotomic_ne_zero n K)
  have : ∀ P ∈ normalizedFactors (cyclotomic n K),
      P.natDegree = orderOf (unitOfCoprime _ (hn.pow_left f)) := fun P hP ↦
    natDegree_of_mem_normalizedFactors_cyclotomic hK hn hP
  have H := natDegree_eq_of_degree_eq <| degree_eq_degree_of_associated h
  rw [natDegree_cyclotomic, natDegree_multiset_prod _ (zero_notMem_normalizedFactors _),
    map_congr rfl this] at H
  simp only [map_const', sum_replicate, smul_eq_mul] at H
  rw [← H, mul_div_left _ (orderOf_pos _), toFinset_card_of_nodup]
  refine nodup_iff_count_le_one.mpr (fun P ↦ ?_)
  by_contra! H
  have : NeZero (n : K) := by
    refine ⟨fun H ↦ ?_⟩
    have := charP_of_card_eq_prime_pow hK
    exact hp.out.coprime_iff_not_dvd.mp ((coprime_pow_left_iff
      (pos_of_ne_zero <| f_ne_zero hK) _ _).mp (hn.pow_left f))
        ((CharP.cast_eq_zero_iff K p _).mp H)
  have hP : P ∈ normalizedFactors (cyclotomic n K) := count_pos.mp (by omega)
  refine (prime_of_normalized_factor _ hP).not_unit (squarefree_cyclotomic n K P ?_)
  have : {P, P} ≤ normalizedFactors (cyclotomic n K) := by
    refine le_iff_count.mpr (fun Q ↦ ?_)
    by_cases hQ : Q = P
    · simp only [hQ, insert_eq_cons, count_cons_self, nodup_singleton, mem_singleton,
        count_eq_one_of_mem, reduceAdd]
      cutsat
    · simp [hQ]
  have := prod_dvd_prod_of_le this
  simp only [insert_eq_cons, prod_cons, prod_singleton] at this
  exact this.trans h.dvd

end Polynomial
