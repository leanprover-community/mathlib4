/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import Mathlib.RingTheory.CohenMacaulay.Basic

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

open RingTheory.Sequence IsLocalRing

lemma Ideal.ofList_height_eq_length_of_isRegular [IsLocalRing R] (rs : List R)
    (reg : IsWeaklyRegular R rs) (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    (Ideal.ofList rs).height = rs.length := by
  apply le_antisymm
  · classical
    have : (Ideal.ofList rs) ≠ ⊤ :=
      (lt_of_le_of_lt (span_le.mpr mem) IsPrime.ne_top'.lt_top).ne_top
    apply le_trans (Ideal.height_le_spanFinrank _ this)
    simp only [Nat.cast_le, ge_iff_le, Ideal.ofList, ← List.coe_toFinset]
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet rs.toFinset))
    rw [Set.ncard_coe_Finset]
    apply List.toFinset_card_le
  · generalize len : rs.length = n
    induction' n with n hn generalizing rs
    · simp
    · simp only [Nat.cast_add, Nat.cast_one, height, le_iInf_iff]
      intro p hp
      let _ := hp.1.1
      have : Ideal.ofList (rs.take n) ≤ p :=
        le_trans (Ideal.span_mono (fun r hr ↦ List.mem_of_mem_take hr)) hp.1.2
      rcases Ideal.exists_minimalPrimes_le this with ⟨q, hq, lep⟩
      have len' : (List.take n rs).length = n := by simp [len]
      have reg' : IsWeaklyRegular R (List.take n rs) := by
        apply (isWeaklyRegular_iff R (List.take n rs)).mpr fun i hi ↦ ?_
        have : (rs.take n).take i  = rs.take i := by
          rw [len'] at hi
          simp [List.take_take, len, le_of_lt hi]
        rw [List.getElem_take, this]
        exact reg.1 i (lt_of_lt_of_le hi (rs.length_take_le' n))
      let _ := hq.1.1
      have le := le_trans (hn (rs.take n) reg' (fun r hr ↦ mem r (List.mem_of_mem_take hr)) len')
        (Ideal.height_mono hq.1.2)
      rw [Ideal.height_eq_primeHeight] at le
      apply le_trans (add_le_add_right le 1) (Ideal.primeHeight_add_one_le_of_lt (lep.lt_of_ne _))
      by_contra eq
      have p_min : p ∈ (Module.annihilator R
        (R ⧸ Ideal.ofList (rs.take n) • (⊤ : Ideal R))).minimalPrimes := by
        simpa [← eq, Ideal.annihilator_quotient] using hq
      absurd Module.notMem_minimalPrimes_of_isSMulRegular (reg.1 n (by simp [len])) p_min
      apply hp.1.2 (Ideal.subset_span _)
      simp

lemma Ideal.maximalIdeal_mem_ofList_append_of_ofList_height_eq_length [IsLocalRing R] (rs : List R)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) (ht : (Ideal.ofList rs).height = rs.length) :
    ∃ rs' : List R, maximalIdeal R ∈ (Ideal.ofList (rs ++ rs')).minimalPrimes ∧
    rs.length + rs'.length = ringKrullDim R := by
  sorry

lemma RingTheory.Sequence.isRegular_of_maximalIdeal_mem_ofList_minimalPrimes
    [IsCohenMacaulayLocalRing R] (rs : List R)
    (mem : maximalIdeal R ∈ (Ideal.ofList rs).minimalPrimes) : IsWeaklyRegular R rs := by
  sorry
