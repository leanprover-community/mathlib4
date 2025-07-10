/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import Mathlib.RingTheory.CohenMacaulay.Catenary

/-!

# A Noetherian Ring is CM iff the Unmixed Theorem holds

-/

universe u

variable {R : Type u} [CommRing R]

open RingTheory.Sequence IsLocalRing

class Ideal.IsUnmixed (I : Ideal R) : Prop where
  height_eq : ∀ {p : Ideal R}, p ∈ associatedPrimes R (R ⧸ I) → p.height = I.height

lemma associatedPrimes_eq_minimalPrimes_of_isUnmixed [IsNoetherianRing R] {I : Ideal R}
    (unmix : I.IsUnmixed) : associatedPrimes R (R ⧸ I) = I.minimalPrimes := by
  apply le_antisymm
  · intro p hp
    have := IsAssociatedPrime.isPrime hp
    apply Ideal.mem_minimalPrimes_of_height_eq _ (le_of_eq (unmix.1 hp))
    rw [← Ideal.annihilator_quotient (I := I), ← Submodule.annihilator_top]
    exact IsAssociatedPrime.annihilator_le hp
  · convert (Module.associatedPrimes.minimalPrimes_annihilator_mem_associatedPrimes R (R ⧸ I))
    exact Ideal.annihilator_quotient.symm

lemma Ideal.ofList_isUnmixed_of_associatedPrimes_eq_minimalPrimes [IsNoetherianRing R] (l : List R)
    (h : (Ideal.ofList l).height = l.length)
    (ass : associatedPrimes R (R ⧸ Ideal.ofList l) ⊆ (Ideal.ofList l).minimalPrimes) :
    (Ideal.ofList l).IsUnmixed := by
  refine ⟨fun {p} hp ↦ le_antisymm ?_ (Ideal.height_mono (ass hp).1.2)⟩

  sorry

variable [IsNoetherianRing R]

lemma isCohenMacaulayRing_of_unmixed
    (unmix : ∀ (l : List R), (Ideal.ofList l).height = l.length → (Ideal.ofList l).IsUnmixed) :
    IsCohenMacaulayRing R := by
  apply (isCohenMacaulayRing_def R).mpr (fun p hp ↦ (isCohenMacaulayLocalRing_def _).mpr ?_)
  have netop : p.height ≠ ⊤ := by
    have := p.finiteHeight_of_isNoetherianRing.1
    have := Ideal.IsPrime.ne_top hp
    tauto
  have {i : ℕ} : i ≤ p.height → ∃ rs : List R, (∀ r ∈ rs, r ∈ p) ∧ IsWeaklyRegular R rs ∧
    rs.length = i := by
    induction' i with i hi
    · intro _
      use []
      simp
    · intro le
      have lt : i < p.height := lt_of_lt_of_le (ENat.coe_lt_coe.mpr (lt_add_one i)) le
      rcases hi (le_of_lt lt) with ⟨rs, mem, reg, len⟩
      have netop : Ideal.ofList rs ≠ ⊤ := ne_top_of_le_ne_top (Ideal.IsPrime.ne_top hp)
        (Ideal.span_le.mpr mem)
      have ht := (Ideal.ofList_height_eq_length_of_isWeaklyRegular rs reg netop)
      let _ := Ideal.Quotient.nontrivial netop
      obtain ⟨r, rmem, hr⟩ : ∃ r ∈ p, IsSMulRegular (R ⧸ Ideal.ofList rs) r := by
        by_contra! h
        obtain ⟨q, qass, le⟩ : ∃ q ∈ associatedPrimes R (R ⧸ Ideal.ofList rs), p ≤ q := by
          rcases associatedPrimes.nonempty R (R ⧸ Ideal.ofList rs) with ⟨Ia, hIa⟩
          apply (Ideal.subset_union_prime_finite (associatedPrimes.finite R _) Ia Ia _).mp
          · rw [biUnion_associatedPrimes_eq_compl_regular R (R ⧸ Ideal.ofList rs)]
            exact fun r hr ↦ h r hr
          · exact fun I hin _ _ ↦ IsAssociatedPrime.isPrime hin
        have := Ideal.height_mono le
        rw [(unmix rs ht).1 qass, ht, len] at this
        exact this.not_gt lt
      use rs.concat r
      simp only [List.concat_eq_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.length_append, len, List.length_cons, List.length_nil, zero_add, and_true]
      refine ⟨fun s ↦ or_imp.mpr ⟨fun h ↦ mem s h, fun eq ↦ by simpa [eq]⟩, ⟨fun i hi ↦ ?_⟩⟩
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add, Nat.lt_succ] at hi
      rw [List.take_append_of_le_length hi]
      rcases lt_or_eq_of_le hi with lt|eq
      · simpa [← List.getElem_append_left' lt [r]] using reg.1 i lt
      · rw [List.getElem_concat_length eq, Ideal.smul_eq_mul, Ideal.mul_top,
          List.take_of_length_le (ge_of_eq eq)]
        exact hr
  apply le_antisymm _ (depth_le_ringKrullDim _)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, IsLocalRing.depth_eq_sSup_length_regular,
    WithBot.coe_le_coe]
  apply le_sSup
  rcases this p.height.coe_toNat_le_self with ⟨rs, mem, reg, len⟩
  use List.map (algebraMap R (Localization.AtPrime p)) rs
  simp only [List.length_map, len, ENat.coe_toNat_eq_self, ne_eq, netop, not_false_eq_true,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, exists_prop, and_true]
  have : ∀ a ∈ rs, (algebraMap R (Localization.AtPrime p)) a ∈
    IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    intro a ha
    simpa [← Ideal.mem_comap, Localization.AtPrime.comap_maximalIdeal] using mem a ha
  refine ⟨⟨isLocaliation_map_is_weakly_regular_of_is_weakly_regular p (Localization.AtPrime p)
    rs R (Localization.AtPrime p) (Algebra.linearMap R (Localization.AtPrime p)) reg, ?_⟩, this⟩
  rw [Ideal.smul_eq_mul, Ideal.mul_top, ne_comm]
  apply ne_top_of_le_ne_top (b := maximalIdeal (Localization.AtPrime p)) Ideal.IsPrime.ne_top'
  simpa only [Ideal.ofList, List.mem_map, Ideal.span_le] using fun b ⟨a, mem, eq⟩ ↦
   (by simpa [← eq] using this a mem)

theorem isCohenMacaulayRing_iff_unmixed : IsCohenMacaulayRing R ↔
    ∀ (l : List R), (Ideal.ofList l).height = l.length → (Ideal.ofList l).IsUnmixed := by
  refine ⟨fun cm l ht ↦ ⟨fun {p} hp ↦ ?_⟩, fun h ↦ isCohenMacaulayRing_of_unmixed h⟩
  have netop : Ideal.ofList l ≠ ⊤ := by
    by_contra eq
    simp [eq] at ht

  sorry
