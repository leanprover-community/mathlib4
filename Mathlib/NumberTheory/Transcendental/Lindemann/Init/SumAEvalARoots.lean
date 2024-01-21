/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Eval

/-!
# The Lindemann-Weierstrass theorem
-/

open scoped BigOperators
open Finset Polynomial

theorem exists_sum_map_aroot_smul_eq {R S : Type*} [CommRing R] [Field S] [Algebra R S] (p : R[X])
    (k : R) (e : ℕ) (q : R[X]) (hk : p.leadingCoeff ∣ k) (he : q.natDegree ≤ e)
    (inj : Function.Injective (algebraMap R S))
    (card_aroots : Multiset.card (p.aroots S) = p.natDegree) :
    ∃ c, ((p.aroots S).map fun x => k ^ e • aeval x q).sum = algebraMap R S c := by
  obtain ⟨k', rfl⟩ := hk; let k := p.leadingCoeff * k'
  have :
    (fun x : S => k ^ e • aeval x q) =
      (fun x => aeval x (∑ i in range (e + 1), monomial i (k' ^ i * k ^ (e - i) * q.coeff i))) ∘
        fun x => p.leadingCoeff • x
  · funext x; rw [Function.comp_apply]
    simp_rw [map_sum, aeval_eq_sum_range' (Nat.lt_add_one_iff.mpr he), aeval_monomial, smul_sum]
    refine' sum_congr rfl fun i hi => _
    rw [← Algebra.smul_def, smul_pow, smul_smul, smul_smul, mul_comm (_ * _) (_ ^ _), ← mul_assoc,
      ← mul_assoc, ← mul_pow, ← pow_add,
      add_tsub_cancel_of_le (Nat.lt_add_one_iff.mp (mem_range.mp hi))]
  rw [this, ← Multiset.map_map _ fun x => p.leadingCoeff • x]
  have : Multiset.card ((p.aroots S).map fun x => p.leadingCoeff • x) =
      Fintype.card (Fin (Multiset.card (p.aroots S)))
  · rw [Multiset.card_map, Fintype.card_fin]
  rw [← MvPolynomial.symmetricSubalgebra.aevalMultiset_sumPolynomial _ _ this,
    ← MvPolynomial.symmetricSubalgebra.scaleAEvalRoots_eq_aevalMultiset]
  exact ⟨_, rfl⟩
  · exact inj
  · rw [Fintype.card_fin]; exact (card_roots' _).trans (natDegree_map_le _ _)
  · exact card_aroots
#align exists_sum_map_aroot_smul_eq exists_sum_map_aroot_smul_eq
