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

local instance (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] (x : R) :
    Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) := by
  let f : M →ₛₗ[Ideal.Quotient.mk (Ideal.span {x})] (QuotSMulTop x M) := {
    __ := Submodule.mkQ _
    map_smul' r m := rfl }
  exact Module.Finite.of_surjective f (Submodule.mkQ_surjective _)

open Pointwise in
lemma free_of_quotSMulTop_free [IsLocalRing R] [IsNoetherianRing R] (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Finite R M] {x : R} (mem : x ∈ maximalIdeal R) (reg : IsSMulRegular M x)
    (free : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) : Module.Free R M := by
  let I := Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  let fin : Fintype I := Module.Free.ChooseBasisIndex.fintype _ _
  have : Module.Finite R (I →₀ R) := by simp [Fintype.finite fin]
  let b := Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  let b' : QuotSMulTop x M ≃ₗ[R] I →₀ R ⧸ Ideal.span {x} := {
    __ := b.1
    map_smul' r m := by simp}
  let f := b'.symm.toLinearMap.comp (Finsupp.mapRange.linearMap (Submodule.mkQ (Ideal.span {x})))
  rcases Module.projective_lifting_property (Submodule.mkQ (x • (⊤ : Submodule R M))) f
    (Submodule.mkQ_surjective _) with ⟨g, hg⟩
  have surjf : Function.Surjective f := by
    simpa [f] using Finsupp.mapRange_surjective _ rfl (Submodule.mkQ_surjective (Ideal.span {x}))
  have lejac : Ideal.span {x} ≤ (⊥ :Ideal R).jacobson :=
    le_trans ((Ideal.span_singleton_le_iff_mem (maximalIdeal R)).mpr mem)
    (IsLocalRing.maximalIdeal_le_jacobson _)
  have surjg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, ← top_le_iff]
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp ‹_›) lejac
    rw [top_le_iff, sup_comm, ← Submodule.map_mkQ_eq_top, ← LinearMap.range_comp,
      Submodule.ideal_span_singleton_smul x ⊤, hg]
    exact LinearMap.range_eq_top_of_surjective f surjf
  have kerf : LinearMap.ker f = x • (⊤ : Submodule R (I →₀ R)) := by
    simp only [LinearEquiv.ker_comp, f]
    ext y
    simp only [Finsupp.ker_mapRange, Submodule.ker_mkQ, Finsupp.mem_submodule_iff]
    refine ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
    · simp only [Ideal.mem_span_singleton', mul_comm] at h
      rw [← Finsupp.univ_sum_single y]
      refine Submodule.sum_mem _ (fun i _ ↦ ?_)
      rcases h i with ⟨z, hz⟩
      simpa only [← hz, ← Finsupp.smul_single'] using
        Submodule.smul_mem_pointwise_smul (Finsupp.single i z) x ⊤ trivial
    · rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h with ⟨z, _, eq⟩
      simpa [← eq] using Ideal.IsTwoSided.mul_mem_of_left (z i) (Ideal.mem_span_singleton_self x)
  have injg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    have fg : (LinearMap.ker g).FG := IsNoetherian.noetherian (LinearMap.ker g)
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) _ fg _ lejac
    rw [Submodule.ideal_span_singleton_smul]
    intro y hy
    have : y ∈ x • (⊤ : Submodule R (I →₀ R)) := by simp [← kerf, ← hg, LinearMap.mem_ker.mp hy]
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp this with ⟨z, _, hz⟩
    simp only [← hz, LinearMap.mem_ker, map_smul] at hy
    have := LinearMap.mem_ker.mpr (IsSMulRegular.right_eq_zero_of_smul reg hy)
    simpa [hz] using Submodule.smul_mem_pointwise_smul z x _ this
  exact Module.Free.of_equiv (LinearEquiv.ofBijective g ⟨injg, surjg⟩)

theorem free_of_isMaximalCohenMacaulay_of_isRegularLocalRing [IsRegularLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [M.IsMaximalCohenMacaulay] : Module.Free R M := by
  rcases exist_nat_eq R with ⟨n, hn⟩
  induction n generalizing R M
  · have : IsField R := isField_of_isRegularLocalRing_of_dimension_zero hn
    let _ : Field R := this.toField
    exact Module.Free.of_divisionRing R M
  · rename_i n ih _ _ _ _ _
    by_cases ntr : Nontrivial M
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
        exact (WithBot.add_natCast_cancel _ _ 1).mp this
      have reg : IsSMulRegular M x := by
        by_contra h
        have := (Set.ext_iff.mp (biUnion_associatedPrimes_eq_compl_regular R M) x).mpr h
        simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at this
        rcases this with ⟨p, pass, mem⟩
        have le1 := depth_le_ringKrullDim_associatedPrime M p pass
        rw [← WithBot.coe_le_coe, WithBot.coe_unbot, (isMaximalCohenMacaulay_def M).mp ‹_›] at le1
        have le2 : ringKrullDim (R ⧸ p) ≤ ringKrullDim (R ⧸ Ideal.span {x}) :=
          ringKrullDim_le_of_surjective (Ideal.Quotient.factor
            ((Ideal.span_singleton_le_iff_mem p).mpr mem)) (Ideal.Quotient.factor_surjective _)
        have := le1.trans le2
        rw [hn, dim, Nat.cast_le] at this
        exact (Nat.not_succ_le_self n) this
      have max : (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x ↑M)).IsMaximalCohenMacaulay := by
        rw [isMaximalCohenMacaulay_def, ← WithBot.add_natCast_cancel _ _ 1, Nat.cast_one,
          (quotient_span_singleton R xmem xnmem).2, ← WithBot.coe_one, ← WithBot.coe_add,
          ← (isMaximalCohenMacaulay_def M).mp ‹_›, WithBot.coe_inj,
          ← depth_quotSMulTop_succ_eq_moduleDepth M x reg xmem]
        congr 1
        have : Nontrivial (QuotSMulTop x M) := quotSMulTop_nontrivial xmem M
        apply (depth_eq_of_algebraMap_surjective _ _).symm
        simpa only [Ideal.Quotient.algebraMap_eq] using Ideal.Quotient.mk_surjective
      have free := ih (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) dim
      exact free_of_quotSMulTop_free M xmem reg free
    · have : Subsingleton M := not_nontrivial_iff_subsingleton.mp ntr
      exact Module.Free.of_subsingleton R M
