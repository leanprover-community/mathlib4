/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Algebra.Polynomial.Splits

import Mathlib.Data.Multiset.Fintype
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Evaluating symmetric polynomials

## Main declarations

* `pow_smul_sum_map_aroots_aeval_mem_range_algebraMap`: Given `k` a multiple of `p.leadingCoeff` and
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
    ← Multiset.map_map f (Fintype.equivOfCardEq h), Multiset.map_univ_val_equiv]

variable (σ) in
/-- `sumPolynomial σ p` is the map sending `X` to `∑ i, X i`. -/
noncomputable
def sumPolynomial (p : R[X]) : symmetricSubalgebra σ R :=
  ⟨∑ i, Polynomial.aeval (X i) p, fun e ↦ by
    simp_rw [map_sum, rename_eq_aeval, ← Polynomial.aeval_algHom_apply, aeval_X, (· ∘ ·)]
    rw [← Equiv.sum_comp e (fun i ↦ Polynomial.aeval (X i) p)]⟩

theorem coe_sumPolynomial (p : R[X]) :
    (sumPolynomial σ p : MvPolynomial σ R) = ∑ i, Polynomial.aeval (X i) p := rfl

theorem aevalMultiset_sumPolynomial
    {m : Multiset S} {p : R[X]} (hm : Multiset.card m = Fintype.card σ) :
    aevalMultiset σ R m (sumPolynomial σ p) = (m.map (fun x ↦ Polynomial.aeval x p)).sum := by
  classical
  conv_lhs => rw [← Multiset.map_univ_coe m]
  rw [aevalMultiset_map_of_card_eq _ _ (by simpa using hm.symm), coe_sumPolynomial, map_sum]
  simp_rw [← Polynomial.aeval_algHom_apply, aeval_X, (· ∘ ·)]
  rw [Equiv.sum_comp _ (fun x : m.ToType ↦ p.aeval x.fst), Finset.sum_eq_multiset_sum,
    ← Function.comp_def (p.aeval ·) (fun x : m.ToType ↦ x.fst), ← Multiset.map_map,
    Multiset.map_univ_coe]

theorem aevalMultiset_mem (B : Subalgebra R S)
    {m : Multiset S} {p : symmetricSubalgebra σ R}
    (h : ∀ i < Fintype.card σ, m.esymm (i + 1) ∈ B) :
    aevalMultiset σ R m p ∈ B := by
  rw [aevalMultiset_apply, MvPolynomial.aeval_def]
  exact MvPolynomial.eval₂_mem (fun _ _ ↦ B.algebraMap_mem _) fun i ↦ h _ i.2

end CommSemiring

section CommRing

variable [Fintype σ] [CommRing R] [CommRing S] [Algebra R S]
  [CommRing A] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

theorem esymm_map_smul_aroots_mem_range_algebraMap [IsDomain A] {q : S[X]} {r : ℕ}
    (hsplit : (q.map (algebraMap S A)).Splits) :
    ((q.aroots A).map (q.leadingCoeff • ·)).esymm r ∈ Set.range (algebraMap S A) := by
  rw [← Algebra.mem_bot, ← Multiset.pow_smul_esymm]
  obtain rfl | hr0 := eq_or_ne r 0
  · simp
  obtain hr | hr := lt_or_ge q.natDegree r
  · simp [Multiset.esymm_of_card_lt ((Polynomial.card_roots_map_le_natDegree _).trans_lt hr)]
  obtain hlc | hlc := eq_or_ne (algebraMap S A q.leadingCoeff) 0
  · simp [Algebra.smul_def, map_pow, hlc, zero_pow hr0]
  have : q.leadingCoeff ^ r • (q.aroots A).esymm r =
      q.leadingCoeff ^ (r - 1) • ((-1) ^ r * (q.map (algebraMap S A)).coeff (q.natDegree - r)) := by
    have : (-1) ^ r * (q.map (algebraMap S A)).coeff (q.natDegree - r) =
        (q.map (algebraMap S A)).leadingCoeff * (q.aroots A).esymm r := by
      rw [Polynomial.coeff_eq_esymm_roots_of_card hsplit.natDegree_eq_card_roots.symm,
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlc,
        Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlc,
        tsub_tsub_cancel_of_le hr,
        ← mul_assoc, mul_left_comm, ← mul_pow, ← pow_two, neg_one_sq, one_pow, mul_one]
      rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlc]
      exact Nat.sub_le _ _
    rw [this, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlc,
      ← Algebra.smul_def, smul_smul, pow_sub_one_mul hr0]
  rw [this]
  exact SMulMemClass.smul_mem _ (mul_mem (pow_mem (by simp) _) (by simp))

theorem aevalMultiset_map_aroots_mem_range_algebraMap [IsDomain A]
    {q : S[X]} {p : symmetricSubalgebra σ R}
    (hsplit : (q.map (algebraMap S A)).Splits) :
    aevalMultiset σ R ((q.aroots A).map (q.leadingCoeff • ·)) p ∈ Set.range (algebraMap S A) :=
  aevalMultiset_mem (IsScalarTower.toAlgHom R S A).range
    fun _ _ ↦ esymm_map_smul_aroots_mem_range_algebraMap hsplit

end CommRing

end MvPolynomial.symmetricSubalgebra

namespace Polynomial

open MvPolynomial.symmetricSubalgebra

variable {R A : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A] (p : R[X]) (q : R[X])

/-- `p.leadingCoeff ^ q.natDegree • ∑ i ∈ p.aroots A, q.aeval i` lies in the base ring. -/
theorem leadingCoeff_pow_natDegree_smul_sum_map_aroots_aeval_mem_range_algebraMap
    (hsplit : (p.map (algebraMap R A)).Splits) :
    p.leadingCoeff ^ q.natDegree • ((p.aroots A).map (q.aeval ·)).sum ∈
      Set.range (algebraMap R A) := by
  have : (fun x : A ↦ p.leadingCoeff ^ q.natDegree • q.aeval x) =
      ((q.scaleRoots p.leadingCoeff).aeval ·) ∘ (p.leadingCoeff • ·) :=
    _root_.funext fun x ↦ (scaleRoots_aeval_smul _ _).symm
  rw [Multiset.smul_sum, Multiset.map_map, Function.comp_def, this,
    ← Multiset.map_map _ fun x => p.leadingCoeff • x]
  rw [← aevalMultiset_sumPolynomial (σ := Fin (p.aroots A).card) (by simp)]
  exact aevalMultiset_map_aroots_mem_range_algebraMap hsplit

/-- Given `k` a multiple of `p.leadingCoeff` and `e ≥ q.natDegree`,
`k ^ e • ∑ i ∈ p.aroots A, q.aeval i` lies in the base ring. -/
theorem pow_smul_sum_map_aroots_aeval_mem_range_algebraMap
    (k : R) (e : ℕ) (hk : p.leadingCoeff ∣ k) (he : q.natDegree ≤ e)
    (hsplit : (p.map (algebraMap R A)).Splits) :
    k ^ e • ((p.aroots A).map (q.aeval ·)).sum ∈ Set.range (algebraMap R A) := by
  obtain ⟨k, rfl⟩ := hk; obtain ⟨e, rfl⟩ := le_iff_exists_add.mp he
  have : (p.leadingCoeff * k) ^ (q.natDegree + e) =
      (p.leadingCoeff * k) ^ e * k ^ q.natDegree * p.leadingCoeff ^ q.natDegree := by
    ring
  rw [this, mul_smul, ← Algebra.mem_bot]
  apply SMulMemClass.smul_mem
  rw [Algebra.mem_bot]
  exact leadingCoeff_pow_natDegree_smul_sum_map_aroots_aeval_mem_range_algebraMap _ _ hsplit

end Polynomial
