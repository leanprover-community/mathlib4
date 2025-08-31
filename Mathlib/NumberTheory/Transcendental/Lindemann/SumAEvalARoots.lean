/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Eval

/-!
# The Lindemann-Weierstrass theorem
-/

open Finset

namespace Polynomial

/-- Given `k` a multiple of `p.leadingCoeff` and `e ≥ q.natDegree`,
`∑ i ∈ p.aroots A, q.aeval i` lies in the base ring. -/
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
  rw [← MvPolynomial.symmetricSubalgebra.aevalMultiset_sumPolynomial _ _ h1,
    ← MvPolynomial.symmetricSubalgebra.scaleAEvalRoots_eq_aevalMultiset _ _ inj h2 card_aroots]
  exact Set.mem_range_self _

end Polynomial
