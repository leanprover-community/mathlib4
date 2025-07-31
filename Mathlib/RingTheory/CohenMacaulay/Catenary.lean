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

open RingTheory.Sequence IsLocalRing Ideal

omit [IsNoetherianRing R] in
lemma Ideal.ofList_spanFinrank_le_length (rs : List R) :
  Submodule.spanFinrank (ofList rs) ≤ rs.length := by
  classical
  simp only [Ideal.ofList, ← List.coe_toFinset]
  apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet rs.toFinset))
  rw [Set.ncard_coe_finset]
  apply List.toFinset_card_le

lemma Ideal.ofList_height_le_length (rs : List R) (h : Ideal.ofList rs ≠ ⊤) :
    (Ideal.ofList rs).height ≤ rs.length := by
  apply le_trans (Ideal.height_le_spanFinrank _ h)
  exact (Nat.cast_le.mpr (ofList_spanFinrank_le_length rs))

lemma IsLocalRing.Ideal.ofList_height_le_length' [IsLocalRing R] (rs : List R)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) : (Ideal.ofList rs).height ≤ rs.length :=
  Ideal.ofList_height_le_length rs (lt_of_le_of_lt (span_le.mpr mem) IsPrime.ne_top'.lt_top).ne_top

lemma Ideal.ofList_height_eq_length_of_isWeaklyRegular (rs : List R) (reg : IsWeaklyRegular R rs)
    (h : Ideal.ofList rs ≠ ⊤) : (Ideal.ofList rs).height = rs.length := by
  apply le_antisymm (Ideal.ofList_height_le_length rs h)
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
        simp [List.take_take, le_of_lt hi]
      rw [List.getElem_take, this]
      exact reg.1 i (lt_of_lt_of_le hi (rs.length_take_le' n))
    let _ := hq.1.1
    have le := le_trans (hn (rs.take n) reg' (ne_top_of_le_ne_top h (Ideal.span_mono
      (fun r hr ↦ List.mem_of_mem_take hr))) len') (Ideal.height_mono hq.1.2)
    rw [Ideal.height_eq_primeHeight] at le
    apply le_trans (add_le_add_right le 1) (Ideal.primeHeight_add_one_le_of_lt (lep.lt_of_ne _))
    by_contra eq
    have p_min : p ∈ (Module.annihilator R
      (R ⧸ Ideal.ofList (rs.take n) • (⊤ : Ideal R))).minimalPrimes := by
      simpa [← eq, Ideal.annihilator_quotient] using hq
    absurd Module.notMem_minimalPrimes_of_isSMulRegular (reg.1 n (by simp [len])) p_min
    apply hp.1.2 (Ideal.subset_span _)
    simp

lemma Ideal.ofList_height_eq_length_of_isWeaklyRegular' [IsLocalRing R] (rs : List R)
    (reg : IsWeaklyRegular R rs) (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    (Ideal.ofList rs).height = rs.length :=
  Ideal.ofList_height_eq_length_of_isWeaklyRegular rs reg
    (lt_of_le_of_lt (span_le.mpr mem) IsPrime.ne_top'.lt_top).ne_top

omit [IsNoetherianRing R] in
lemma IsLocalRing.height_eq_height_maximalIdeal_of_maximalIdeal_mem_minimalPrimes [IsLocalRing R]
    (I : Ideal R) (mem : maximalIdeal R ∈ I.minimalPrimes) :
    I.height = (maximalIdeal R).height := by
  rw [Ideal.height_eq_primeHeight (maximalIdeal R)]
  have : I.minimalPrimes = {maximalIdeal R} := by
    ext J
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · simp [Minimal.eq_of_le mem.out ⟨h.1.1, h.1.2⟩ (IsLocalRing.le_maximalIdeal h.1.1.ne_top)]
    · simpa [Set.mem_singleton_iff.mp h] using mem
  simp [Ideal.height, this]

lemma maximalIdeal_mem_ofList_append_minimalPrimes_of_ofList_height_eq_length [IsLocalRing R]
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
        rw [IsLocalRing.height_eq_height_maximalIdeal_of_maximalIdeal_mem_minimalPrimes _ hp,
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
      apply le_antisymm (Ideal.ofList_height_le_length' _ mem')
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

lemma maximalIdeal_mem_minimalPrimes_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) (h : Function.Surjective f) {I : Ideal R}
    {J : Ideal S} (le : I ≤ J.comap f) (min : maximalIdeal R ∈ I.minimalPrimes) (ne : J ≠ ⊤) :
    maximalIdeal S ∈ J.minimalPrimes := by
  refine ⟨⟨Ideal.IsMaximal.isPrime' _, le_maximalIdeal ne⟩, fun q ⟨hq, Jle⟩ _ ↦ ?_⟩
  have eq_map : maximalIdeal S = Ideal.map f (maximalIdeal R) := by
    have := ((local_hom_TFAE f).out 0 4).mp (Function.Surjective.isLocalHom f h)
    rw [← Ideal.map_comap_of_surjective f h (maximalIdeal S), this]
  rw [eq_map, Ideal.map_le_iff_le_comap]
  exact min.2 ⟨q.comap_isPrime f, le_trans le (Ideal.comap_mono Jle)⟩
    (le_maximalIdeal_of_isPrime (q.comap f))

open Pointwise in
lemma isRegular_of_maximalIdeal_mem_ofList_minimalPrimes
    [IsCohenMacaulayLocalRing R] (rs : List R)
    (mem : maximalIdeal R ∈ (Ideal.ofList rs).minimalPrimes)
    (dim : rs.length = ringKrullDim R) : IsRegular R rs := by
  refine ⟨?_, by simpa using (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' mem.1.2).symm⟩
  generalize len : rs.length = n
  induction' n with n hn generalizing R rs
  · simp [List.length_eq_zero_iff.mp len]
  · match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      have xmem : x ∈ maximalIdeal R := mem.1.2 (Ideal.subset_span (by simp))
      let R' := R ⧸ x • (⊤ : Ideal R)
      have : Nontrivial R' :=
          Ideal.Quotient.nontrivial (by simpa [← Submodule.ideal_span_singleton_smul])
      have : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      let _ : IsLocalRing R' := IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
      have xreg : IsSMulRegular R x := by
        by_contra nreg
        have mem_ass : x ∈ {r : R | IsSMulRegular R r}ᶜ := nreg
        simp only [← biUnion_associatedPrimes_eq_compl_regular, Set.mem_iUnion, SetLike.mem_coe,
          exists_prop] at mem_ass
        rcases mem_ass with ⟨p, ass, xmem⟩
        let _ := (isCohenMacaulayLocalRing_iff R).mp (by assumption)
        have eq := ModuleCat.depth_eq_supportDim_of_cohenMacaulay (ModuleCat.of R R)
        rw [depth_eq_dim_quotient_associated_prime_of_isCohenMacaulay p (ModuleCat.of R R) ass,
          Module.supportDim_self_eq_ringKrullDim, WithBot.coe_unbot] at eq
        have : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial (Ideal.IsPrime.ne_top ass.1)
        have : IsLocalHom (Ideal.Quotient.mk p) :=
          IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
        let _ : IsLocalRing (R ⧸ p) :=
          IsLocalRing.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
        have mem_max : ∀ r ∈ rs'.map (algebraMap R (R ⧸ p)), r ∈ maximalIdeal (R ⧸ p) := by
          simp only [Ideal.Quotient.algebraMap_eq, List.mem_map,
            forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
          intro r hr
          exact map_nonunit (Ideal.Quotient.mk p) r (mem.1.2 (Ideal.subset_span (by simp [hr])))
        have netop : Ideal.ofList (rs'.map (algebraMap R (R ⧸ p))) ≠ ⊤ :=
          ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (Ideal.span_le.mpr mem_max)
        have le : Ideal.ofList (x :: rs') ≤
          (Ideal.ofList (rs'.map (algebraMap R (R ⧸ p)))).comap (Ideal.Quotient.mk p) := by
          rw [Ideal.span_le]
          intro r hr
          rcases List.mem_cons.mp hr with eqx|mem_rs'
          · apply Ideal.ker_le_comap
            simpa [eqx] using xmem
          · apply Ideal.subset_span
            simp only [Ideal.Quotient.algebraMap_eq, List.mem_map, Set.mem_setOf_eq]
            use r
        have max_mem := maximalIdeal_mem_minimalPrimes_of_surjective (Ideal.Quotient.mk p)
          Ideal.Quotient.mk_surjective le mem netop
        have := Ideal.ofList_height_le_length' (rs'.map (algebraMap R (R ⧸ p))) mem_max
        have coe_eq : ((rs'.length + 1 : ℕ) : WithBot ℕ∞) = ((rs'.length + 1 : ℕ) : ℕ∞) := rfl
        rw [height_eq_height_maximalIdeal_of_maximalIdeal_mem_minimalPrimes _ max_mem,
          ← WithBot.coe_le_coe, List.length_map, maximalIdeal_height_eq_ringKrullDim,
          ← eq, ← dim, List.length_cons, coe_eq, WithBot.coe_le_coe, ENat.coe_le_coe] at this
        simp at this
      simp only [isWeaklyRegular_cons_iff, xreg, true_and]
      have min : maximalIdeal R' ∈ (Ideal.ofList (rs'.map (algebraMap R R'))).minimalPrimes := by
        have le : Ideal.ofList (x :: rs') ≤
          (Ideal.ofList (rs'.map (algebraMap R R'))).comap (algebraMap R R') := by
          rw [Ideal.span_le]
          intro r hr
          rcases List.mem_cons.mp hr with eqx|mem_rs'
          · apply Ideal.ker_le_comap
            simpa [R', eqx, ← Submodule.ideal_span_singleton_smul x] using
              Ideal.mem_span_singleton_self x
          · apply Ideal.subset_span
            simp only [List.mem_map, Set.mem_setOf_eq]
            use r
        apply maximalIdeal_mem_minimalPrimes_of_surjective (algebraMap R R')
          Ideal.Quotient.mk_surjective le mem
        have mem_max : ∀ r ∈ rs'.map (algebraMap R R'), r ∈ maximalIdeal R' := by
          simpa only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] using
            fun r hr ↦ map_nonunit (Ideal.Quotient.mk (x • (⊤ : Ideal R))) r
            (mem.1.2 (Ideal.subset_span (by simp [hr])))
        exact ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (Ideal.span_le.mpr mem_max)
      let _ := (quotient_regular_smul_top_isCohenMacaulay_iff_isCohenMacaulay R x xreg xmem).mp
          (by assumption)
      rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff R' R' rs']
      apply hn (rs'.map (algebraMap R R')) min _ (by simpa using len)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, ←
        ringKrullDim_quotSMulTop_succ_eq_ringKrullDim xreg xmem] at dim
      simpa [List.length_map] using (withBotENat_add_coe_cancel _ _ 1).mp dim

lemma isRegular_of_ofList_height_eq_length_of_isCohenMacaulayLocalRing [IsCohenMacaulayLocalRing R]
    (rs : List R) (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) (ht : (Ideal.ofList rs).height = rs.length) :
    IsRegular R rs := by
  refine ⟨⟨fun i hi ↦ ?_⟩, ?_⟩
  · rcases maximalIdeal_mem_ofList_append_minimalPrimes_of_ofList_height_eq_length rs mem ht with
      ⟨rs', min, len⟩
    rw [← Nat.cast_add, ← List.length_append] at len
    have := (isRegular_of_maximalIdeal_mem_ofList_minimalPrimes _ min len).1.1 i
      (lt_of_lt_of_eq (Nat.lt_add_right rs'.length hi) List.length_append.symm)
    rw [List.take_append_of_le_length (le_of_lt hi)] at this
    simpa [List.getElem_append_left' hi rs'] using this
  · simpa using (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (span_le.mpr mem)).symm

lemma Ideal.depth_le_height [IsLocalRing R] (I : Ideal R) (netop : I ≠ ⊤) :
    I.depth (ModuleCat.of R R) ≤ I.height := by
  simp only [IsLocalRing.ideal_depth_eq_sSup_length_regular I netop (ModuleCat.of R R), exists_prop,
    sSup_le_iff, Set.mem_setOf_eq, forall_exists_index, and_imp]
  intro n rs reg mem len
  rw [← len, ← ofList_height_eq_length_of_isWeaklyRegular' rs reg.1
    (fun r hr ↦ le_maximalIdeal netop (mem r hr))]
  exact Ideal.height_mono (span_le.mpr mem)

lemma Ideal.exist_regular_sequence_length_eq_height [IsCohenMacaulayLocalRing R]
    (I : Ideal R) (netop : I ≠ ⊤) :
    ∃ rs : List R, IsRegular R rs ∧ (∀ r ∈ rs, r ∈ I) ∧ rs.length = I.height := by
  rcases Ideal.exists_spanRank_eq_and_height_eq I netop with ⟨J, le, rank, ht⟩
  simp only [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr
      ((isNoetherianRing_iff_ideal_fg R).mp (by assumption) J), Cardinal.nat_eq_ofENat] at rank
  obtain ⟨⟨s, span⟩, hs⟩ : ∃ s : { s : Finset R // Submodule.span R s = J}, s.1.card =
    Submodule.spanFinrank J := by
    have : {x | ∃ s : { s : Finset R // Submodule.span R s = J}, s.1.card = x}.Nonempty := by
      rcases (isNoetherianRing_iff_ideal_fg R).mp (by assumption) J with ⟨s, hs⟩
      use s.card, ⟨s, hs⟩
    simpa only [Submodule.spanFinrank_eq_iInf J, iInf, Set.range] using Nat.sInf_mem this
  simp only [← hs] at rank
  use s.toList
  simp only [Finset.mem_toList, Finset.length_toList, rank, and_true]
  refine ⟨?_, fun r hr ↦ le (le_of_eq span (Submodule.subset_span hr))⟩
  exact isRegular_of_ofList_height_eq_length_of_isCohenMacaulayLocalRing s.toList (fun r hr ↦
    le_maximalIdeal netop (le (le_of_eq span (Submodule.subset_span (Finset.mem_toList.mp hr)))))
    (by simp [Ideal.ofList, span, ← Ideal.submodule_span_eq, rank, ht])

lemma Ideal.depth_eq_height [IsCohenMacaulayLocalRing R] (I : Ideal R) (netop : I ≠ ⊤) :
    I.depth (ModuleCat.of R R) = I.height := by
  apply le_antisymm (I.depth_le_height netop)
  rw [IsLocalRing.ideal_depth_eq_sSup_length_regular I netop]
  apply le_sSup
  rcases Ideal.exist_regular_sequence_length_eq_height I netop with ⟨rs, reg, mem, len⟩
  use rs

omit [IsNoetherianRing R] in
lemma Ideal.primeHeight_eq_ringKrullDim_localization (p : Ideal R) [p.IsPrime]
    (R' : Type*) [CommRing R'] [Algebra R R'] [IsLocalization.AtPrime R' p] :
    p.primeHeight = ringKrullDim R' := by
  simp [Ideal.primeHeight, ringKrullDim, Order.krullDim_eq_of_orderIso
    (IsLocalization.AtPrime.primeSpectrumOrderIso R' p), ← Order.height_eq_krullDim_Iic]

lemma Ideal.primeHeight_add_ringKrullDim_quotient_eq_ringKrullDim [IsCohenMacaulayLocalRing R]
    (p : Ideal R) [p.IsPrime] : p.primeHeight + ringKrullDim (R ⧸ p) = ringKrullDim R := by
  rcases Ideal.exist_regular_sequence_length_eq_height p IsPrime.ne_top' with ⟨rs, reg, mem, len⟩
  have mem' := (fun r hr ↦ le_maximalIdeal_of_isPrime p (mem r hr))
  have CM := (quotient_regular_isCohenMacaulay_iff_isCohenMacaulay (ModuleCat.of R R) rs reg).mp
    ((isCohenMacaulayLocalRing_iff R).mp (by assumption))
  have ht_eq := Ideal.ofList_height_eq_length_of_isWeaklyRegular' rs reg.1 mem'
  rw [← Ideal.height_eq_primeHeight, ← len]
  rw [(isCohenMacaulayLocalRing_def R).mp (by assumption),
    ← depth_quotient_regular_sequence_add_length_eq_depth (ModuleCat.of R R) rs reg]
  have ass : p ∈ associatedPrimes R (R ⧸ ofList rs • (⊤ : Ideal R)) := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_mem_associatedPrimes
    simp only [smul_eq_mul, annihilator_quotient, mul_top]
    apply Ideal.mem_minimalPrimes_of_height_eq
    · exact (span_le.mpr mem)
    · simp [← len, ← ht_eq]
  let _ : Nontrivial (R ⧸ ofList rs • (⊤ : Ideal R)) := IsRegular.quot_ofList_smul_nontrivial reg ⊤
  rw [depth_eq_dim_quotient_associated_prime_of_isCohenMacaulay p
    (ModuleCat.of R (R ⧸ ofList rs • (⊤ : Ideal R))) ass]
  simp [add_comm]

omit [IsNoetherianRing R] in
lemma ringKrullDim_quotient_eq_iSup_quotient_minimalPrimes (I : Ideal R) :
    ringKrullDim (R ⧸ I) = ⨆ p ∈ I.minimalPrimes, ringKrullDim (R ⧸ p) := by
  apply le_antisymm
  · simp only [ringKrullDim_quotient, Order.krullDim, iSup_le_iff]
    intro sp
    let _ := sp.head.1.2
    rcases Ideal.exists_minimalPrimes_le ((PrimeSpectrum.mem_zeroLocus _ _).mp sp.head.2) with
      ⟨p, min, le⟩
    apply le_trans _ (le_biSup _ min)
    let sp' : LTSeries (PrimeSpectrum.zeroLocus (p : Set R)) := {
      length := sp.length
      toFun i := ⟨(sp.toFun i).1, le_trans le (Subtype.coe_le_coe.mpr (LTSeries.head_le sp i))⟩
      step i := sp.step i }
    convert le_iSup _ sp'
    rfl
  · simp only [iSup_le_iff]
    intro p hp
    exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hp.1.2)

lemma Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim [IsCohenMacaulayLocalRing R]
    (I : Ideal R) (netop : I ≠ ⊤) : I.height + ringKrullDim (R ⧸ I) = ringKrullDim R := by
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial netop
  rw [height, ringKrullDim_quotient_eq_iSup_quotient_minimalPrimes, iSup_subtype', iInf_subtype']
  let min := (Subtype (Membership.mem I.minimalPrimes))
  have fin : Finite min := finite_minimalPrimes_of_isNoetherianRing R I
  have non : Nonempty min :=  Ideal.nonempty_minimalPrimes netop
  apply le_antisymm
  · let f : min → WithBot ℕ∞ := fun x ↦ ringKrullDim (R ⧸ x.1)
    rcases exists_eq_ciSup_of_finite (f := f) with ⟨p, hp⟩
    let _ := p.2.1.1
    rw [← hp, ← Ideal.primeHeight_add_ringKrullDim_quotient_eq_ringKrullDim p.1]
    apply add_le_add_right (WithBot.coe_le_coe.mpr (iInf_le_iff.mpr fun b a ↦ a p))
  · let g : min → ℕ∞ := fun x ↦ @Ideal.primeHeight _ _ x.1 (minimalPrimes_isPrime x.2)
    rcases exists_eq_ciInf_of_finite (f := g) with ⟨p, hp⟩
    let _ := p.2.1.1
    rw [← hp, ← Ideal.primeHeight_add_ringKrullDim_quotient_eq_ringKrullDim p.1]
    apply add_le_add_left (le_iSup_iff.mpr fun b a ↦ a p)
