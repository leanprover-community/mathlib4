/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Vieta

/-!
TODO
-/

open scoped BigOperators Polynomial

namespace List

variable {R S : Type*}
variable [Monoid R] [Monoid S] [MulAction S R] [IsScalarTower S R R] [SMulCommClass S R R]

@[simp] lemma prod_map_smul (l : List R) (s : S) :
    (l.map (s • ·)).prod = s ^ l.length • l.prod := by
  induction' l with hd tl ih
  · simp
  · simp [ih, pow_add, smul_mul_smul, pow_mul_comm', pow_succ]

end List

namespace Multiset

section

variable {R S : Type*}
variable [CommMonoid R] [Monoid S] [MulAction S R] [IsScalarTower S R R] [SMulCommClass S R R]

@[simp] lemma prod_map_smul (m : Multiset R) (s : S) :
    (m.map (s • ·)).prod = s ^ card m • m.prod :=
  Quot.induction_on m <| by simp

end

variable {R S : Type*}
variable [CommSemiring R] [Monoid S] [DistribMulAction S R] [IsScalarTower S R R]
  [SMulCommClass S R R]

lemma pow_smul_esymm (s : S) (n : ℕ) (m : Multiset R) :
    s ^ n • m.esymm n = (m.map (s • ·)).esymm n := by
  rw [esymm, smul_sum, map_map]
  trans ((powersetCard n m).map (fun x : Multiset R ↦ s ^ card x • x.prod)).sum
  · refine congr_arg _ (map_congr rfl (fun x hx ↦ ?_))
    rw [Function.comp_apply, (mem_powersetCard.1 hx).2]
  · simp_rw [← prod_map_smul, esymm, powersetCard_map, map_map, (· ∘ ·)]

end Multiset

namespace MvPolynomial

variable {σ τ R S A : Type*}

section CommSemiring

namespace symmetricSubalgebra

variable (σ R)
variable [Fintype σ] [Fintype τ] [CommRing R] [CommSemiring S] [Algebra R S]

noncomputable
def aevalMultiset (m : Multiset S) :
    symmetricSubalgebra σ R →ₐ[R] S :=
  (aeval (fun i : Fin (Fintype.card σ) ↦ m.esymm (i + 1))).comp
    (equiv_symmetricSubalgebra (σ := σ) R rfl).symm

variable {σ R}

lemma aevalMultiset_apply (m : Multiset S) (p : symmetricSubalgebra σ R) :
    aevalMultiset σ R m p =
      aeval (fun i : Fin _ ↦ m.esymm (i + 1)) ((equiv_symmetricSubalgebra R rfl).symm p) := rfl

theorem aevalMultiset_map (f : σ → S) (p : symmetricSubalgebra σ R) :
    aevalMultiset σ R (Finset.univ.val.map f) p = aeval f (p : MvPolynomial σ R) := by
  rw [aevalMultiset_apply]
  conv_rhs =>
    rw [← AlgEquiv.apply_symm_apply (equiv_symmetricSubalgebra R rfl) p]
  simp_rw [equiv_symmetricSubalgebra_symm_apply, equiv_symmetricSubalgebra_apply, esymmAlgHom_apply,
    ← aeval_esymm_eq_multiset_esymm σ R, ← comp_aeval, AlgHom.coe_comp, Function.comp_apply]

theorem aevalMultiset_map' (f : τ → S) (p : symmetricSubalgebra σ R)
    (h : Fintype.card σ = Fintype.card τ) :
    aevalMultiset σ R (Finset.univ.val.map f) p =
      aeval (f ∘ Fintype.equivOfCardEq h) (p : MvPolynomial σ R) := by
  rw [← aevalMultiset_map (f ∘ Fintype.equivOfCardEq h) p,
    ← Multiset.map_map f (Fintype.equivOfCardEq h)]
  congr
  refine (congr_arg Finset.val (Finset.map_univ_equiv (Fintype.equivOfCardEq h)).symm).trans ?_
  rw [Finset.map_val, Equiv.coe_toEmbedding]

end symmetricSubalgebra

end CommSemiring

section CommRing
variable [Fintype σ] [Fintype τ] [CommRing R] [CommRing S] [Algebra R S]
  [CommRing A] [IsDomain A] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

namespace symmetricSubalgebra

variable (σ R)

noncomputable
def scaleAEvalRoots (q : S[X]) :
    symmetricSubalgebra σ R →ₐ[R] S :=
  (aeval (fun i : Fin (Fintype.card σ) ↦ q.leadingCoeff ^ (i : ℕ) * (-1) ^ (i + 1 : ℕ) *
    q.coeff (q.natDegree - (i + 1)))).comp (equiv_symmetricSubalgebra (σ := σ) R rfl).symm

variable {σ R}

lemma scaleAEvalRoots_apply (q : S[X]) (p : symmetricSubalgebra σ R) :
    scaleAEvalRoots σ R q p =
      aeval (fun i : Fin _ ↦ q.leadingCoeff ^ (i : ℕ) * (-1) ^ (↑i + 1 : ℕ) *
        q.coeff (q.natDegree - (i + 1))) ((equiv_symmetricSubalgebra R rfl).symm p) :=
  rfl

lemma scaleAEvalRoots_eq_aevalMultiset (q : S[X]) (p : symmetricSubalgebra σ R)
    (inj : Function.Injective (algebraMap S A)) (h : Fintype.card σ ≤ q.natDegree)
    (hroots : Multiset.card (q.map (algebraMap S A)).roots = q.natDegree) :
    algebraMap S A (scaleAEvalRoots σ R q p) =
      aevalMultiset σ R ((q.map (algebraMap S A)).roots.map (fun x ↦ q.leadingCoeff • x)) p := by
  rw [scaleAEvalRoots_apply]
  trans aeval (fun i : Fin _ ↦ algebraMap S A (q.leadingCoeff ^ (i + 1 : ℕ)) *
    (q.map (algebraMap S A)).roots.esymm (↑i + 1))
      ((equiv_symmetricSubalgebra R rfl).symm p)
  · simp_rw [← aeval_algebraMap_apply, (· ∘ ·), map_mul, ← Polynomial.coeff_map]
    congr
    funext i
    have hroots' :
        Multiset.card (q.map (algebraMap S A)).roots = (q.map (algebraMap S A)).natDegree := by
      rw [hroots, Polynomial.natDegree_map_eq_of_injective inj]
    rw [Polynomial.coeff_eq_esymm_roots_of_card hroots',
      Polynomial.natDegree_map_eq_of_injective inj, Polynomial.leadingCoeff_map' inj,
      ← mul_assoc, mul_left_comm, ← mul_assoc, ← mul_assoc, mul_assoc _ _ (_ ^ _),
      pow_add q.leadingCoeff, mul_comm _ (_ ^ 1), pow_one, map_mul]
    have h : ↑i + 1 ≤ Polynomial.natDegree q := Nat.add_one_le_iff.mpr (i.2.trans_le h)
    congr 1
    · rw [mul_right_eq_self₀, map_pow, map_neg, map_one,
        tsub_tsub_cancel_of_le h, ← mul_pow,
        neg_one_mul, neg_neg, one_pow, eq_self_iff_true, true_or]; trivial
    · rw [tsub_tsub_cancel_of_le h]
    · rw [Polynomial.natDegree_map_eq_of_injective inj]
      exact tsub_le_self
  · simp_rw [← Algebra.smul_def, Multiset.pow_smul_esymm, ← aevalMultiset_apply]

variable (σ)

noncomputable
def sumPolynomial (p : R[X]) : symmetricSubalgebra σ R :=
  ⟨∑ i, Polynomial.aeval (X i) p, fun e ↦ by
    simp_rw [map_sum, rename, ← Polynomial.aeval_algHom_apply, aeval_X, (· ∘ ·)]
    rw [← Equiv.sum_comp e (fun i ↦ Polynomial.aeval (X i) p)]⟩

lemma coe_sumPolynomial (p : R[X]) :
    (sumPolynomial σ p : MvPolynomial σ R) = ∑ i, Polynomial.aeval (X i) p := rfl

variable {σ}

lemma aevalMultiset_sumPolynomial
    (m : Multiset S) (p : R[X]) (hm : Multiset.card m = Fintype.card σ) :
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
    rw [List.get_map, List.get_finRange]
  conv_lhs => rw [eq_univ_map]
  rw [aevalMultiset_map']
  swap
  rw [Fintype.card_fin, Multiset.length_toList, hm]
  rw [coe_sumPolynomial, map_sum]
  simp_rw [← Polynomial.aeval_algHom_apply, aeval_X, (· ∘ ·)]
  generalize_proofs h
  trans ∑ x : Fin m.toList.length, (Polynomial.aeval (m.toList.get x)) p
  · rw [← Equiv.sum_comp (Fintype.equivOfCardEq h)]
  · rw [Finset.sum]
    apply congr_arg
    conv_rhs => rw [eq_univ_map, Multiset.map_map]

end symmetricSubalgebra

end CommRing

end MvPolynomial
