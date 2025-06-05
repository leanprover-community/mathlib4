/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import Mathlib.RingTheory.CohenMacaulay.Basic

/-!

# CM Local Ring is Catenary

-/

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

open RingTheory.Sequence IsLocalRing

lemma Ideal.ofList_height_le_length [IsLocalRing R] (rs : List R)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) : (Ideal.ofList rs).height ≤ rs.length := by
  classical
  have : (Ideal.ofList rs) ≠ ⊤ :=
    (lt_of_le_of_lt (span_le.mpr mem) IsPrime.ne_top'.lt_top).ne_top
  apply le_trans (Ideal.height_le_spanFinrank _ this)
  simp only [Nat.cast_le, ge_iff_le, Ideal.ofList, ← List.coe_toFinset]
  apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet rs.toFinset))
  rw [Set.ncard_coe_Finset]
  apply List.toFinset_card_le

lemma Ideal.ofList_height_eq_length_of_isRegular [IsLocalRing R] (rs : List R)
    (reg : IsWeaklyRegular R rs) (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    (Ideal.ofList rs).height = rs.length := by
  apply le_antisymm (Ideal.ofList_height_le_length rs mem)
  generalize len : rs.length = n
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

omit [IsNoetherianRing R] in
lemma IsLocalRing.height_eq_height_maximalIdea_of_maximalIdeal_mem_minimalPrimes [IsLocalRing R]
    (I : Ideal R) (mem : maximalIdeal R ∈ I.minimalPrimes) :
    I.height = (maximalIdeal R).height := by
  rw [Ideal.height_eq_primeHeight (maximalIdeal R)]
  have : I.minimalPrimes = {maximalIdeal R} := by
    ext J
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · simp [Minimal.eq_of_le mem.out ⟨h.1.1, h.1.2⟩ (IsLocalRing.le_maximalIdeal h.1.1.ne_top)]
    · simpa [Set.mem_singleton_iff.mp h] using mem
  simp [Ideal.height, this]

lemma Ideal.maximalIdeal_mem_ofList_append_minimalPrimes_of_ofList_height_eq_length [IsLocalRing R]
    (rs : List R) (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) (ht : (Ideal.ofList rs).height = rs.length) :
    ∃ rs' : List R, maximalIdeal R ∈ (Ideal.ofList (rs ++ rs')).minimalPrimes ∧
    rs.length + rs'.length = ringKrullDim R := by
  have ne : ringKrullDim R ≠ ⊥ ∧ ringKrullDim R ≠ ⊤ :=
    finiteRingKrullDim_iff_ne_bot_and_top.mp inferInstance
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim R = d := by
    have : (ringKrullDim R).unbot ne.1 ≠ ⊤ := by
      rw [ne_eq, ← WithBot.coe_inj]
      simpa using ne.2
    rcases ENat.ne_top_iff_exists.mp this with ⟨d, hd⟩
    use d
    rw [← WithBot.coe_inj, WithBot.coe_unbot] at hd
    exact hd.symm
  generalize len : d - rs.length = k
  induction' k with k hk generalizing rs
  · have : Ideal.ofList rs ≤ maximalIdeal R := (span_le.mpr mem)
    have netop : Ideal.ofList rs ≠ ⊤ := (lt_of_le_of_lt this IsPrime.ne_top'.lt_top).ne_top
    have coe_eq : (d : WithBot ℕ∞) = (d : ℕ∞) := rfl
    have le : rs.length ≤ d := by
      simpa [ht, hd, coe_eq] using Ideal.height_le_ringKrullDim_of_ne_top netop
    rw [Nat.sub_eq_zero_iff_le] at len
    use []
    simp only [List.append_nil, le_antisymm le len, List.length_nil, CharP.cast_eq_zero, add_zero,
      hd, and_true]
    apply Ideal.mem_minimalPrimes_of_height_eq this
    rw [ht, le_antisymm le len, ← WithBot.coe_le_coe]
    simp [hd, coe_eq]
  · classical
    have : Ideal.ofList rs ≤ maximalIdeal R := (span_le.mpr mem)
    have netop : Ideal.ofList rs ≠ ⊤ := (lt_of_le_of_lt this IsPrime.ne_top'.lt_top).ne_top
    have coe_eq : (d : WithBot ℕ∞) = (d : ℕ∞) := rfl
    have le : rs.length ≤ d := by
      simpa [ht, hd, coe_eq] using Ideal.height_le_ringKrullDim_of_ne_top netop
    obtain ⟨x, hx, nmem⟩ : ∃ x ∈ maximalIdeal R, ∀ p ∈ (Ideal.ofList rs).minimalPrimes, x ∉ p := by
      have : ¬ (maximalIdeal R : Set R) ⊆ ⋃ p ∈ (Ideal.ofList rs).minimalPrimes, p := by
        by_contra subset
        rcases (Ideal.subset_union_prime_finite
          (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.ofList rs)) ⊤ ⊤
          (fun p mem _ _ ↦ mem.1.1)).mp subset with ⟨p, hp, le⟩
        let _ := hp.1.1
        have eq := Ideal.IsMaximal.eq_of_le inferInstance IsPrime.ne_top' le
        rw [← eq] at hp
        rw [IsLocalRing.height_eq_height_maximalIdea_of_maximalIdeal_mem_minimalPrimes _ hp,
          ← WithBot.coe_inj, IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hd] at ht
        simp only [coe_eq, WithBot.coe_inj, Nat.cast_inj] at ht
        simp [ht] at len
      rcases Set.not_subset.mp this with ⟨x, hx1, hx2⟩
      simp at hx2
      use x
      tauto
    have mem' : ∀ r ∈ rs ++ [x], r ∈ maximalIdeal R := by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      intro r hr
      rcases hr with mem_rs|eqx
      · exact mem r mem_rs
      · simpa [eqx] using hx
    have ht' : (ofList (rs ++ [x])).height = (rs ++ [x]).length := by
      apply le_antisymm (Ideal.ofList_height_le_length _ mem')
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.cast_add,
        Nat.cast_one, height, ofList_append, ofList_cons, ofList_nil, bot_le, sup_of_le_left,
        le_iInf_iff]
      intro p hp
      let _ := hp.1.1
      rcases Ideal.exists_minimalPrimes_le (sup_le_iff.mp hp.1.2).1 with ⟨q, hq, qle⟩
      let _ := hq.1.1
      have lt : q < p := lt_of_le_of_ne qle (ne_of_mem_of_not_mem'
          ((sup_le_iff.mp hp.1.2).2 (mem_span_singleton_self x)) (nmem q hq)).symm
      apply le_trans _ (Ideal.primeHeight_add_one_le_of_lt lt)
      simpa only [← ht, ← height_eq_primeHeight] using add_le_add_right (Ideal.height_mono hq.1.2) 1
    have len' : d - (rs ++ [x]).length = k := by
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add]
      omega
    rcases hk (rs ++ [x]) mem' ht' len' with ⟨rs', hrs', hlen⟩
    use x :: rs'
    rw [List.append_cons]
    refine ⟨hrs', ?_⟩
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, ← hlen, List.length_append,
      List.length_nil, zero_add]
    abel

open Pointwise in
lemma RingTheory.Sequence.isRegular_of_maximalIdeal_mem_ofList_minimalPrimes
    [IsCohenMacaulayLocalRing R] (rs : List R)
    (mem : maximalIdeal R ∈ (Ideal.ofList rs).minimalPrimes)
    (dim : rs.length = ringKrullDim R) : IsRegular R rs := by
  constructor
  · generalize len : rs.length = n
    induction' n with n hn generalizing R rs
    · simp [List.length_eq_zero_iff.mp len]
    · match rs with
      | [] => simp at len
      | x :: rs' =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at len
        have xreg : IsSMulRegular R x := by
          by_contra nreg
          have mem_ass : x ∈ {r : R | IsSMulRegular R r}ᶜ := nreg
          simp only [← biUnion_associatedPrimes_eq_compl_regular, exists_prop,
            associatedPrimes_self_eq_minimalPrimes, Set.mem_iUnion, SetLike.mem_coe] at mem_ass
          rcases mem_ass with ⟨p, min, xmem⟩
          --absurd xmem as `p` is minimal
          sorry
        have xmem : x ∈ maximalIdeal R := mem.1.2 (Ideal.subset_span (by simp))
        simp only [isWeaklyRegular_cons_iff, xreg, true_and]
        let R' := R ⧸ x • (⊤ : Ideal R)
        let _ := (quotient_regular_smul_top_isCohenMacaulay_iff_isCohenMacaulay R x xreg xmem).mp
            (by assumption)
        rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff R' R' rs']
        apply hn (rs'.map (algebraMap R R')) _ _ (by simpa using len)
        · rw [← Ideal.map_ofList]
          have surj : Function.Surjective (algebraMap R R') := Ideal.Quotient.mk_surjective

          sorry
        · simp only [List.length_cons, Nat.cast_add, Nat.cast_one, ←
            ringKrullDim_quotSMulTop_succ_eq_ringKrullDim xreg xmem] at dim
          simpa [List.length_map] using (withBotENat_add_coe_cancel _ _ 1).mp dim
  · simpa using (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' mem.1.2).symm
