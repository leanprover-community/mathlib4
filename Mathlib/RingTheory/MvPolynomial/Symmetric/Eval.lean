/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Evaluating symmetric polynomials

## Main declarations

* `sum_map_aroots_aeval_mem_range_algebraMap`: Given `k` a multiple of `p.leadingCoeff` and
  `e ≥ q.natDegree`, `k ^ e • ∑ i ∈ p.aroots A, q.aeval i` lies in the base ring.
* `MvPolynomial.symmetricSubalgebra.aevalMultiset` evaluates a symmetric polynomial at the elements
  of a multiset.
* `MvPolynomial.symmetricSubalgebra.sumPolynomial` maps `X` to `∑ i, X i`.

These are used in the proof of Lindemann-Weierstrass.
-/

@[expose] public section

open Finset
open scoped Polynomial

variable {σ τ R S A : Type*}

namespace MvPolynomial.symmetricSubalgebra

section CommSemiring

variable [Fintype σ] [Fintype τ] [CommRing R] [CommSemiring S] [Algebra R S]

variable (σ R) in
/-- `aevalMultiset` evaluates a symmetric polynomial at the elements of `s`. -/
noncomputable
def aevalMultiset (m : Multiset S) : symmetricSubalgebra σ R →ₐ[R] S :=
  (aeval (fun i : Fin (Fintype.card σ) ↦ m.esymm (i + 1))).comp
    (esymmAlgEquiv (σ := σ) R rfl).symm

theorem aevalMultiset_apply (m : Multiset S) (p : symmetricSubalgebra σ R) :
    aevalMultiset σ R m p =
      aeval (fun i : Fin _ ↦ m.esymm (i + 1)) ((esymmAlgEquiv σ R rfl).symm p) := rfl

theorem aevalMultiset_esymm (m : Multiset S) (i : Fin (Fintype.card σ)) :
    aevalMultiset σ R m ⟨esymm σ R (i + 1), esymm_isSymmetric σ R _⟩ = m.esymm (i + 1) := by
  simp [aevalMultiset_apply, esymmAlgEquiv_symm_apply]

theorem aevalMultiset_map (f : σ → S) (p : symmetricSubalgebra σ R) :
    aevalMultiset σ R (Finset.univ.val.map f) p = aeval f (p : MvPolynomial σ R) := by
  rw [aevalMultiset_apply]
  conv_rhs =>
    rw [← AlgEquiv.apply_symm_apply (esymmAlgEquiv σ R rfl) p]
  simp_rw [esymmAlgEquiv_apply, esymmAlgHom_apply, ← aeval_esymm_eq_multiset_esymm σ R,
    ← comp_aeval, AlgHom.coe_comp, Function.comp_apply]

theorem aevalMultiset_map_of_card_eq (f : τ → S) (p : symmetricSubalgebra σ R)
    (h : Fintype.card σ = Fintype.card τ) :
    aevalMultiset σ R (Finset.univ.val.map f) p =
      aeval (f ∘ Fintype.equivOfCardEq h) (p : MvPolynomial σ R) := by
  rw [← aevalMultiset_map (f ∘ Fintype.equivOfCardEq h) p,
    ← Multiset.map_map f (Fintype.equivOfCardEq h)]
  congr
  refine (congr_arg Finset.val (Finset.map_univ_equiv (Fintype.equivOfCardEq h)).symm).trans ?_
  rw [Finset.map_val, Equiv.coe_toEmbedding]

end CommSemiring

section CommRing

variable [Fintype σ] [Fintype τ] [CommRing R] [CommRing S] [Algebra R S]
  [CommRing A] [IsDomain A] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

variable (σ R) in
private noncomputable
def scaleAEvalRoots (q : S[X]) : symmetricSubalgebra σ R →ₐ[R] S :=
  letI f1 := (aeval (fun i : Fin (Fintype.card σ) ↦ q.leadingCoeff ^ (i : ℕ) * (-1) ^ (i + 1 : ℕ) *
    q.coeff (q.natDegree - (i + 1))))
  letI f2 := (esymmAlgEquiv (σ := σ) R rfl).symm
  f1.comp f2

private theorem scaleAEvalRoots_apply {q : S[X]} {p : symmetricSubalgebra σ R} :
    scaleAEvalRoots σ R q p =
      aeval (fun i : Fin _ ↦ q.leadingCoeff ^ (i : ℕ) * (-1) ^ (↑i + 1 : ℕ) *
        q.coeff (q.natDegree - (i + 1))) ((esymmAlgEquiv σ R rfl).symm p) :=
  rfl

private theorem scaleAEvalRoots_esymm {q : S[X]} {i : Fin (Fintype.card σ)} :
    scaleAEvalRoots σ R q ⟨esymm σ R (i + 1), esymm_isSymmetric σ R _⟩ =
      q.leadingCoeff ^ (i : ℕ) * (-1) ^ (i + 1 : ℕ) * q.coeff (q.natDegree - (i + 1)) := by
  simp [scaleAEvalRoots_apply, esymmAlgEquiv_symm_apply]

private theorem scaleAEvalRoots_eq_aevalMultiset {q : S[X]} {p : symmetricSubalgebra σ R}
    (inj : Function.Injective (algebraMap S A)) (h : Fintype.card σ ≤ q.natDegree)
    (hroots : Multiset.card (q.map (algebraMap S A)).roots = q.natDegree) :
    algebraMap S A (scaleAEvalRoots σ R q p) =
      aevalMultiset σ R ((q.map (algebraMap S A)).roots.map (fun x ↦ q.leadingCoeff • x)) p := by
  rw [scaleAEvalRoots_apply]
  trans aeval (fun i : Fin _ ↦ algebraMap S A (q.leadingCoeff ^ (i + 1 : ℕ)) *
    (q.map (algebraMap S A)).roots.esymm (↑i + 1))
      ((esymmAlgEquiv σ R rfl).symm p)
  · simp_rw [← aeval_algebraMap_apply, Function.comp_def, map_mul, ← Polynomial.coeff_map]
    congr
    funext i
    have hroots' :
        Multiset.card (q.map (algebraMap S A)).roots = (q.map (algebraMap S A)).natDegree := by
      rw [hroots, Polynomial.natDegree_map_eq_of_injective inj]
    rw [Polynomial.coeff_eq_esymm_roots_of_card hroots',
      Polynomial.natDegree_map_eq_of_injective inj, Polynomial.leadingCoeff_map_of_injective inj,
      ← mul_assoc, mul_left_comm, ← mul_assoc, ← mul_assoc, mul_assoc _ _ (_ ^ _),
      pow_add q.leadingCoeff, mul_comm _ (_ ^ 1), pow_one, map_mul]
    swap
    · rw [Polynomial.natDegree_map_eq_of_injective inj]
      exact tsub_le_self
    have h : ↑i + 1 ≤ Polynomial.natDegree q := Nat.add_one_le_iff.mpr (i.2.trans_le h)
    congr 1
    · simp_rw [mul_right_eq_self₀, map_pow, map_neg, map_one, tsub_tsub_cancel_of_le h, ← mul_pow,
        neg_one_mul, neg_neg, one_pow, true_or]
    · rw [tsub_tsub_cancel_of_le h]
  · simp_rw [← Algebra.smul_def, Multiset.pow_smul_esymm, ← aevalMultiset_apply]

variable (σ) in
/-- `sumPolynomial σ p` is the map sending `X` to `∑ i, X i`. -/
noncomputable
def sumPolynomial (p : R[X]) : symmetricSubalgebra σ R :=
  ⟨∑ i, Polynomial.aeval (X i) p, fun e ↦ by
    simp_rw [map_sum, rename, ← Polynomial.aeval_algHom_apply, aeval_X, (· ∘ ·)]
    rw [← Equiv.sum_comp e (fun i ↦ Polynomial.aeval (X i) p)]⟩

theorem coe_sumPolynomial (p : R[X]) :
    (sumPolynomial σ p : MvPolynomial σ R) = ∑ i, Polynomial.aeval (X i) p := rfl

theorem aevalMultiset_sumPolynomial
    {m : Multiset S} {p : R[X]} (hm : Multiset.card m = Fintype.card σ) :
    aevalMultiset σ R m (sumPolynomial σ p) = (m.map (fun x ↦ Polynomial.aeval x p)).sum := by
  have eq_univ_map : m = Finset.univ.val.map (fun i : Fin m.toList.length ↦ m.toList.get i) := by
    have toFinset_finRange : ∀ n, (List.finRange n).toFinset = Finset.univ :=
      fun n ↦ Finset.eq_univ_iff_forall.mpr fun x ↦ List.mem_toFinset.mpr <| List.mem_finRange x
    have : (Finset.univ.val : Multiset (Fin m.toList.length)) = List.finRange m.toList.length := by
      rw [← toFinset_finRange, List.toFinset_val, List.dedup_eq_self.mpr]
      exact List.nodup_finRange _
    rw [this, Multiset.map_coe]
    conv_lhs => rw [← m.coe_toList]
    refine congr_arg _ (List.ext_get ?_ (fun n h₁ h₂ ↦ ?_))
    · rw [List.length_map, List.length_finRange]
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange, Fin.cast_mk]
  conv_lhs => rw [eq_univ_map]
  rw [aevalMultiset_map_of_card_eq]
  swap
  · rw [Fintype.card_fin, Multiset.length_toList, hm]
  rw [coe_sumPolynomial, map_sum]
  simp_rw [← Polynomial.aeval_algHom_apply, aeval_X, (· ∘ ·)]
  generalize_proofs h
  trans ∑ x : Fin m.toList.length, (Polynomial.aeval (m.toList.get x)) p
  · rw [← Equiv.sum_comp (Fintype.equivOfCardEq h)]
  · rw [Finset.sum_eq_multiset_sum]
    conv_rhs => rw [eq_univ_map, Multiset.map_map, Function.comp_def]

end CommRing

end MvPolynomial.symmetricSubalgebra

namespace Polynomial

/-- Given `k` a multiple of `p.leadingCoeff` and `e ≥ q.natDegree`,
`k ^ e • ∑ i ∈ p.aroots A, q.aeval i` lies in the base ring. -/
theorem sum_map_aroots_aeval_mem_range_algebraMap {R A : Type*}
    [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
    (p : R[X]) (k : R) (e : ℕ) (q : R[X]) (hk : p.leadingCoeff ∣ k) (he : q.natDegree ≤ e)
    (inj : Function.Injective (algebraMap R A))
    (card_aroots : (p.aroots A).card = p.natDegree) :
    k ^ e • ((p.aroots A).map (q.aeval ·)).sum ∈ Set.range (algebraMap R A) := by
  obtain ⟨k', rfl⟩ := hk; let k := p.leadingCoeff * k'
  have :
    (fun x : A => k ^ e • q.aeval x) =
      (fun x => aeval x (∑ i ∈ range (e + 1), monomial i (k' ^ i * k ^ (e - i) * q.coeff i))) ∘
        fun x => p.leadingCoeff • x := by
    funext x; rw [Function.comp_apply]
    simp_rw [map_sum, aeval_eq_sum_range' (Nat.lt_add_one_iff.mpr he), aeval_monomial, smul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [← Algebra.smul_def, smul_pow, smul_smul, smul_smul, mul_comm (_ * _) (_ ^ _), ← mul_assoc,
      ← mul_assoc, ← mul_pow, ← pow_add,
      add_tsub_cancel_of_le (Nat.lt_add_one_iff.mp (mem_range.mp hi))]
  rw [Multiset.smul_sum, Multiset.map_map, Function.comp_def, this,
    ← Multiset.map_map _ fun x => p.leadingCoeff • x]
  have h1 : ((p.aroots A).map fun x => p.leadingCoeff • x).card =
      Fintype.card (Fin (p.aroots A).card) := by
    rw [Multiset.card_map, Fintype.card_fin]
  have h2 : Fintype.card (Fin (p.aroots A).card) ≤ p.natDegree := by
    rw [Fintype.card_fin]; exact (card_roots' _).trans natDegree_map_le
  rw [← MvPolynomial.symmetricSubalgebra.aevalMultiset_sumPolynomial h1,
    ← MvPolynomial.symmetricSubalgebra.scaleAEvalRoots_eq_aevalMultiset inj h2 card_aroots]
  exact Set.mem_range_self _

end Polynomial
