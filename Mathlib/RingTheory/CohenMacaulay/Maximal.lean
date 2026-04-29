/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
-/
module

public import Mathlib.RingTheory.CohenMacaulay.Basic
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.RegularLocalRing.Basic

/-!

# Maximal Cohen Macaulay Module

The definition of maximal Cohen Macaulay module.

# Main definition and results

* `isCohenMacaulayLocalRing_of_isRegularLocalRing` : regular local ring is Cohen Macaulay

* `free_of_isMaximalCohenMacaulay_of_isRegularLocalRing` : maximal Cohen Macaulay module over
  regular local ring is free.

-/

@[expose] public section

universe v' v u' u

variable {R : Type u} [CommRing R]

open IsLocalRing

/-- A `R`-module is maximal Cohen Macaulay if `IsLocalRing.depth M = ringKrullDim R`. -/
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
  let fg' : (maximalIdeal R).FG := (maximalIdeal R).fg_of_isNoetherianRing
  let _ : Fintype (maximalIdeal R).generators := (Submodule.FG.finite_generators fg').fintype
  have : ringKrullDim R = ((maximalIdeal R).generators.toFinset.card : ℕ∞) := by
    rw [← (isRegularLocalRing_iff R).mp ‹_›, ← Set.ncard_eq_toFinset_card',
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
  simpa [IsLocalRing.isField_iff_maximalIdeal_eq, ← Submodule.spanRank_eq_zero_iff_eq_bot,
    Submodule.FG.spanRank_eq_spanFinrank (maximalIdeal R).fg_of_isNoetherianRing, h] using
    (isRegularLocalRing_iff R).mp ‹_›

private instance (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] (x : R) :
    Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
  Module.Finite.of_restrictScalars_finite R _ _

theorem free_of_isMaximalCohenMacaulay_of_isRegularLocalRing [IsRegularLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [M.IsMaximalCohenMacaulay] : Module.Free R M := by
  rcases FiniteRingKrullDim.ringKrullDim_eq_nat R with ⟨n, hn⟩
  induction n generalizing R M with
  | zero =>
    let _ : Field R := (isField_of_isRegularLocalRing_of_dimension_zero hn).toField
    exact Module.Free.of_divisionRing R M
  | succ n ih =>
    rcases subsingleton_or_nontrivial M with sub|ntr
    · exact Module.Free.of_subsingleton R M
    · obtain ⟨x, xmem, xnmem⟩ : ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R) ^ 2 := by
        by_contra! ge
        have : IsField R := by
          simpa only [← subsingleton_cotangentSpace_iff, Ideal.cotangent_subsingleton_iff,
            IsIdempotentElem] using le_antisymm Ideal.mul_le_right (le_of_le_of_eq ge (pow_two _))
        rw [ringKrullDim_eq_zero_of_isField this, ← Nat.cast_zero, Nat.cast_inj] at hn
        exact Nat.zero_ne_add_one n hn
      let _ := (quotient_span_singleton R xmem xnmem).1
      have dim : ringKrullDim (R ⧸ Ideal.span {x}) = n := by
        simpa [hn, ENat.WithBot.add_one_cancel] using (quotient_span_singleton R xmem xnmem).2
      have reg : IsSMulRegular M x := by
        by_contra h
        have := (Set.ext_iff.mp (biUnion_associatedPrimes_eq_compl_regular R M) x).mpr h
        simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at this
        rcases this with ⟨p, pass, mem⟩
        have le := depth_le_ringKrullDim_associatedPrime M p pass
        rw [← WithBot.coe_le_coe, WithBot.coe_unbot, (isMaximalCohenMacaulay_def M).mp ‹_›] at le
        have : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) :=
          le.trans (ringKrullDim_le_of_surjective (Ideal.Quotient.factor
            ((Ideal.span_singleton_le_iff_mem p).mpr mem)) (Ideal.Quotient.factor_surjective _))
        rw [hn, dim, Nat.cast_le] at this
        exact (Nat.not_succ_le_self n) this
      have max : (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x ↑M)).IsMaximalCohenMacaulay := by
        rw [isMaximalCohenMacaulay_def, ← ENat.WithBot.add_natCast_cancel, Nat.cast_one,
          (quotient_span_singleton R xmem xnmem).2, ← WithBot.coe_one, ← WithBot.coe_add,
          ← (isMaximalCohenMacaulay_def M).mp ‹_›, WithBot.coe_inj,
          ← depth_quotSMulTop_succ_eq_moduleDepth M x reg xmem]
        congr 1
        have := nontrivial_quotSMulTop_of_mem_maximalIdeal M xmem
        apply (depth_eq_of_algebraMap_surjective _ _).symm
        simpa only [Ideal.Quotient.algebraMap_eq] using Ideal.Quotient.mk_surjective
      have free := ih (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) dim
      exact (free_iff_quotSMulTop_free R M xmem reg).mp free
