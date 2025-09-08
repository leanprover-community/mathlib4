/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
-/
import Mathlib.RingTheory.CohenMacaulay.Basic
import Mathlib.RingTheory.RegularLocalRing.Basic

/-!

# Maximal Cohen Macaulay Module

The definition of maximal Cohen Macaulay module.

# Main definition and results

* `free_of_isMaximalCohenMacaulay_of_isRegularLocalRing` : maximal Cohen Macaulay module over
  regular local ring is free.

-/

universe v' v u' u

variable {R : Type u} [CommRing R]

open IsLocalRing

class ModuleCat.IsMaximalCohenMacaulay [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) : Prop where
  depth_eq_dim : IsLocalRing.depth M = ringKrullDim R

lemma isMaximalCohenMacaulay_def [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) : M.IsMaximalCohenMacaulay ↔ IsLocalRing.depth M = ringKrullDim R :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

/-
--need subsingleton imply depth eq top
instance [IsNoetherianRing R] [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [M.IsMaximalCohenMacaulay] : Nontrivial M := sorry
-/

lemma isCohenMacaulay_of_isMaximalCohenMacaulay [IsNoetherianRing R] [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [M.IsMaximalCohenMacaulay] : M.IsCohenMacaulay := by
  rw [M.isCohenMacaulay_iff]
  by_cases h : Subsingleton M
  · exact Or.inl h
  · have : Nontrivial M := not_subsingleton_iff_nontrivial.mp h
    right
    apply le_antisymm _ (depth_le_supportDim M)
    simpa [(isMaximalCohenMacaulay_def M).mp ‹_›] using Module.supportDim_le_ringKrullDim R M

lemma isCohenMacaulayLocalRing_of_isRegularLocalRing [IsRegularLocalRing R] :
    IsCohenMacaulayLocalRing R := by
  apply isCohenMacaulayLocalRing_of_ringKrullDim_le_depth
  rw [depth_eq_sSup_length_regular]
  let fg' : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
  let _ : Fintype (maximalIdeal R).generators := (Submodule.FG.finite_generators fg').fintype
  have : ringKrullDim R = ((maximalIdeal R).generators.toFinset.card : ℕ∞) := by
    rw [← (isRegularLocalRing_def R).mp ‹_›, ← Set.ncard_eq_toFinset_card',
      Submodule.FG.generators_ncard fg']
    rfl
  simp only [this, WithBot.coe_le_coe]
  apply le_sSup
  use (maximalIdeal R).generators.toFinset.toList
  simp only [Finset.length_toList, Set.toFinset_card, Set.coe_fintypeCard, Finset.mem_toList,
    Set.mem_toFinset, exists_prop, and_true]
  refine ⟨?_, fun r hr ↦ Submodule.FG.generators_mem (maximalIdeal R) hr⟩
  apply isRegular_of_span_eq_maximalIdeal
  · simpa [Ideal.ofList] using (maximalIdeal R).span_generators
  · rw [Finset.length_toList, this]
    rfl

lemma isField_of_isRegularLocalRing_of_dimension_zero [IsRegularLocalRing R]
    (h : ringKrullDim R = 0) : IsField R := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Submodule.spanRank_eq_zero_iff_eq_bot]
  have := (isRegularLocalRing_def R).mp ‹_›
  simp only [h, Nat.cast_eq_zero] at this
  have fg : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
  simpa [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg] using this

theorem free_of_isMaximalCohenMacaulay_of_isRegularLocalRing [IsRegularLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [M.IsMaximalCohenMacaulay] : Module.Free R M := by
  rcases exist_nat_eq R with ⟨n, hn⟩
  induction' n with n ih generalizing R M
  · have : IsField R := isField_of_isRegularLocalRing_of_dimension_zero hn
    sorry
  · obtain ⟨x, xmem, xnmem⟩ : ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R) ^ 2 := by
      by_contra! ge
      have : IsField R := by
        simpa only [← subsingleton_cotangentSpace_iff, Ideal.cotangent_subsingleton_iff,
          IsIdempotentElem] using le_antisymm Ideal.mul_le_right (le_of_le_of_eq ge (pow_two _))
      rw [ringKrullDim_eq_zero_of_isField this, ← Nat.cast_zero, Nat.cast_inj] at hn
      exact Nat.zero_ne_add_one n hn
    let _ := (quotient_span_singleton R xmem xnmem).1
    have dim : ringKrullDim (R ⧸ Ideal.span {x}) = n := by
      have := (quotient_span_singleton R xmem xnmem).2
      simp only [hn, Nat.cast_add, Nat.cast_one] at this
      exact (withBotENat_add_coe_cancel _ _ 1).mp this
    have reg : IsSMulRegular M x := by
      by_contra h
      have := (Set.ext_iff.mp (biUnion_associatedPrimes_eq_compl_regular R M) x).mpr h
      simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at this
      rcases this with ⟨p, pass, mem⟩
      --use `depth R ≤ dim(R ⧸ p)`
      sorry
    have : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) := by
      --Module.Finite.of_surjective
      sorry
    have max : (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x ↑M)).IsMaximalCohenMacaulay := by
      rw [isMaximalCohenMacaulay_def]
      --need to switch ring
      --RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff
      sorry
    have free := ih (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) dim
    --https://stacks.math.columbia.edu/tag/00NS
    sorry
