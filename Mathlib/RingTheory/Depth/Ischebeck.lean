/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Module

/-!

# The Ischebeck theorem and its corollary

-/

@[expose] public section

open IsLocalRing LinearMap ModuleCat Pointwise
open RingTheory.Sequence Ideal CategoryTheory Abelian Limits

universe u v

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
theorem moduleDepth_ge_depth_sub_dim [IsNoetherianRing R] [IsLocalRing R] (M N : ModuleCat.{v} R)
    [Module.Finite R M] [Nfin : Module.Finite R N] [Nontrivial M] [Nntr : Nontrivial N]
    [Small.{v} R] : moduleDepth N M ≥ IsLocalRing.depth M -
    (Module.supportDim R N).unbot (Module.supportDim_ne_bot_of_nontrivial R N) := by
  generalize dim : ((Module.supportDim R N).unbot (Module.supportDim_ne_bot_of_nontrivial R N)) = r
  induction r with
  | top => simp
  | coe r =>
    induction r using Nat.strong_induction_on generalizing N
    rename_i r ihr
    by_cases eq0 : r = 0
    · simp only [eq0, CharP.cast_eq_zero, WithBot.unbot_eq_iff, WithBot.coe_zero] at dim
      have smul_lt := (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (maximalIdeal_le_jacobson (Module.annihilator R M))).lt_top'
      simp [eq0, IsLocalRing.depth, moduleDepth_eq_depth_of_supp_eq (maximalIdeal R) N M smul_lt
        (support_of_supportDim_eq_zero R N dim)]
    · refine (IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
        (motive := fun L ↦ (∀ (Lntr : Nontrivial L),
          ((Module.supportDim R L).unbot (Module.supportDim_ne_bot_of_nontrivial R L)) = r →
          (moduleDepth (ModuleCat.of R L) M ≥ IsLocalRing.depth M - r))) R Nfin)
          (fun L _ _ _ Ltr Lntr ↦ ?_) (fun L _ _ _ p e Lntr dim_eq ↦ ?_) ?_ Nntr dim
      · absurd Ltr
        exact (not_subsingleton_iff_nontrivial.mpr Lntr)
      · obtain ⟨x, hx1, hx2⟩ : ((maximalIdeal R : Set R) \ (p.asIdeal: Set R)).Nonempty  := by
          rw [Set.diff_nonempty]
          by_contra sub
          have peq := (maximalIdeal.isMaximal R).eq_of_le IsPrime.ne_top' sub
          have : Module.supportDim R (R ⧸ p.asIdeal) = 0 := by
            let : Field (R ⧸ maximalIdeal R) := Quotient.field (maximalIdeal R)
            rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, ← peq,
              Ideal.annihilator_quotient, ringKrullDim_eq_zero_of_field]
          absurd dim_eq
          simpa only [Module.supportDim_eq_of_equiv e, this, WithBot.unbot_zero,
            ← ENat.coe_zero, ENat.coe_inj, eq_comm] using eq0
        let S := (ModuleCat.of R L).smulShortComplex x
        have reg' : IsSMulRegular (R ⧸ p.asIdeal) (Ideal.Quotient.mk p.1 x) :=
          (IsRegular.of_ne_zero (Ideal.Quotient.eq_zero_iff_mem.not.mpr hx2)).isSMulRegular
        have reg : IsSMulRegular (ModuleCat.of R L) x := (e.isSMulRegular_congr _).mpr reg'
        have hS := reg.smulShortComplex_shortExact
        apply le_sSup
        intro i hi
        have : Subsingleton (Ext (ModuleCat.of R (QuotSMulTop x L)) M (i + 1)) := by
          have ntr := nontrivial_quotSMulTop_of_mem_maximalIdeal L hx1
          have dimlt : (Module.supportDim R (QuotSMulTop x L)).unbot
            (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L)) < r := by
            have : (Module.supportDim R (QuotSMulTop x L)) + 1 ≤ Module.supportDim R L := by
              simp only [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
              rw [e.annihilator_eq, Ideal.annihilator_quotient]
              have ple : p.1 ≤ Module.annihilator R (QuotSMulTop x L) := by
                rw [← p.1.annihilator_quotient, ← LinearEquiv.annihilator_eq e]
                exact (Submodule.mkQ _).annihilator_le_of_surjective (Submodule.mkQ_surjective _)
              have : Ideal.Quotient.mk p.asIdeal x ∈ nonZeroDivisors (R ⧸ p.1) := by
                simpa [Ideal.Quotient.eq_zero_iff_mem] using hx2
              exact ringKrullDim_succ_le_of_surjective _ (Quotient.factor_surjective ple) this
                (by simpa [Ideal.Quotient.eq_zero_iff_mem] using QuotSMulTop.mem_annihilator L x)
            have succle : (Module.supportDim R (QuotSMulTop x L)).unbot
              (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L)) + 1 ≤ r := by
              simpa [← dim_eq, WithBot.le_unbot_iff] using this
            have : (Module.supportDim R (QuotSMulTop x L)).unbot
              (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L)) ≠ ⊤ := by
              by_contra h
              simp [h] at succle
            exact (ENat.add_one_le_iff this).mp succle
          rcases ENat.ne_top_iff_exists.mp (ne_top_of_lt dimlt) with ⟨m, hm⟩
          simp only [← hm, Nat.cast_lt] at dimlt
          apply ext_subsingleton_of_lt_moduleDepth
          refine lt_of_lt_of_le ?_ (ihr m dimlt (ModuleCat.of R (QuotSMulTop x L)) hm.symm)
          by_cases eqtop : IsLocalRing.depth M = ⊤
          · simp only [Nat.cast_add, eqtop, ENat.top_sub_coe, ENat.add_lt_top,
              ENat.coe_lt_top, true_and]
          · rcases ENat.ne_top_iff_exists.mp eqtop with ⟨k, hk⟩
            have : (i + 1 : ℕ) ≤ IsLocalRing.depth M - r := by
              simpa [ENat.add_one_le_iff (ENat.coe_ne_top i)] using hi
            apply lt_of_le_of_lt this
            simp only [← hk, ← ENat.coe_sub, Nat.cast_lt] at hi ⊢
            omega
        have epi' : Function.Surjective (x • LinearMap.id (R := R) (M := (Ext (of R L) M i))) := by
          convert (AddCommGrpCat.epi_iff_surjective _).mp <| ShortComplex.Exact.epi_f
            (Ext.contravariant_sequence_exact₁' hS M i (i + 1) (Nat.add_comm 1 i))
            ((@AddCommGrpCat.isZero_of_subsingleton _ this).eq_zero_of_tgt _)
          ext a
          simp only [smul_apply, id_coe, id_eq, smulShortComplex, AddCommGrpCat.hom_ofHom,
            Ext.bilinearComp_apply_apply]
          nth_rw 1 [← Ext.mk₀_id_comp a, ← Ext.smul_comp, ← Ext.mk₀_smul]
          congr
        by_contra! ntr
        have mem : x ∈ (Module.annihilator R (Ext (of R L) M i)).jacobson :=
          maximalIdeal_le_jacobson _ hx1
        absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator mem
        nth_rw 1 [← LinearMap.range_eq_top_of_surjective _ epi']
        ext y
        simp only [mem_range, smul_apply, id_coe, id_eq, Submodule.mem_smul_pointwise_iff_exists,
          Submodule.mem_top, true_and]
      · intro L1 _ _ _ L2 _ _ _ L3 _ _ _ f g inj surj exac ih1' ih3' L2ntr dim_eq
        rcases subsingleton_or_nontrivial L1 with sub1|ntr1
        · have : Function.Injective g := by
            simp [← ker_eq_bot, exact_iff.mp exac, Subsingleton.eq_zero f]
          let eg : L2 ≃ₗ[R] L3 := LinearEquiv.ofBijective g ⟨this, surj⟩
          rw [moduleDepth_eq_of_iso_fst M eg.toModuleIso]
          apply ih3' this.nontrivial
          rw [← dim_eq, WithBot.unbot_inj, Module.supportDim_eq_of_equiv eg]
        · rcases subsingleton_or_nontrivial L3 with sub3|ntr3
          · have : Function.Surjective f := by
              simp [← range_eq_top, ← exact_iff.mp exac, Subsingleton.eq_zero g]
            let ef : L1 ≃ₗ[R] L2 := LinearEquiv.ofBijective f ⟨inj, this⟩
            rw [← moduleDepth_eq_of_iso_fst M ef.toModuleIso]
            apply ih1' this.nontrivial
            rw [← dim_eq, WithBot.unbot_inj, Module.supportDim_eq_of_equiv ef]
          · have dimle1 : ((Module.supportDim R L1).unbot
              (Module.supportDim_ne_bot_of_nontrivial R L1)) ≤ r := by
              rw [← dim_eq, ← WithBot.coe_le_coe, WithBot.coe_unbot, WithBot.coe_unbot]
              exact Module.supportDim_le_of_injective f inj
            have dimle3 : ((Module.supportDim R L3).unbot
              (Module.supportDim_ne_bot_of_nontrivial R L3)) ≤ r := by
              rw [← dim_eq, ← WithBot.coe_le_coe, WithBot.coe_unbot, WithBot.coe_unbot]
              exact Module.supportDim_le_of_surjective g surj
            have ge1 : moduleDepth (of R L1) M ≥ IsLocalRing.depth M -
              ((Module.supportDim R L1).unbot (Module.supportDim_ne_bot_of_nontrivial R L1)) := by
              rcases lt_or_eq_of_le dimle1 with lt|eq
              · rcases ENat.ne_top_iff_exists.mp (ne_top_of_lt lt) with ⟨m, hm⟩
                simp only [← hm, Nat.cast_lt] at lt
                simpa [← hm] using ihr m lt (ModuleCat.of.{v} R L1) hm.symm
              · simpa [eq] using ih1' ntr1 eq
            have ge3 : moduleDepth (of R L3) M ≥ IsLocalRing.depth M -
              ((Module.supportDim R L3).unbot (Module.supportDim_ne_bot_of_nontrivial R L3)) := by
              rcases lt_or_eq_of_le dimle3 with lt|eq
              · rcases ENat.ne_top_iff_exists.mp (ne_top_of_lt lt) with ⟨m, hm⟩
                simp only [← hm, Nat.cast_lt] at lt
                simpa [← hm] using ihr m lt (ModuleCat.of.{v} R L3) hm.symm
              · simpa [eq] using ih3' ntr3 eq
            let S := ModuleCat.shortComplexOfCompEqZero f g exac.linearMap_comp_eq_zero
            have hS := ModuleCat.shortComplex_shortExact S exac inj surj
            exact ge_trans (moduleDepth_ge_min_of_shortExact_snd_fst S hS M) (le_inf_iff.mpr
              ⟨(tsub_le_tsub_left dimle1 _).trans ge1, (tsub_le_tsub_left dimle3 _).trans ge3⟩)

lemma quotient_prime_ringKrullDim_ne_bot {P : Ideal R} (prime : P.IsPrime) :
    ringKrullDim (R ⧸ P) ≠ ⊥ :=
  ne_bot_of_le_ne_bot WithBot.zero_ne_bot
    (@ringKrullDim_nonneg_of_nontrivial _ _ (Quotient.nontrivial_iff.mpr prime.ne_top'))

theorem depth_le_ringKrullDim_associatedPrime [IsNoetherianRing R] [IsLocalRing R]
    [Small.{v} R] (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] (P : Ideal R)
    (ass : P ∈ associatedPrimes R M) : IsLocalRing.depth M ≤ (ringKrullDim (R ⧸ P)).unbot
      (quotient_prime_ringKrullDim_ne_bot ass.1) := by
  have := Quotient.nontrivial_iff.mpr ass.1.ne_top'
  have dep0 : moduleDepth (of R (Shrink.{v} (R ⧸ P))) M = 0 := by
    rw [moduleDepth_eq_zero_of_hom_nontrivial,
      (LinearEquiv.congrLeft M R (Shrink.linearEquiv R (R ⧸ P))).nontrivial_congr]
    rcases ((isAssociatedPrime_iff_exists_injective_linearMap P M).mp
      (AssociatedPrimes.mem_iff.mp ass)).2 with ⟨f, hf⟩
    exact nontrivial_of_ne f 0 (ne_zero_of_injective hf)
  have := moduleDepth_ge_depth_sub_dim M (ModuleCat.of R (Shrink.{v} (R ⧸ P)))
  simp only [dep0, ge_iff_le, nonpos_iff_eq_zero, tsub_eq_zero_iff_le] at this
  convert this
  rw [← Module.supportDim_quotient_eq_ringKrullDim,
    Module.supportDim_eq_of_equiv (Shrink.linearEquiv R (R ⧸ P))]

theorem depth_le_supportDim [IsNoetherianRing R] [IsLocalRing R] [Small.{v, u} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.depth M ≤ Module.supportDim R M := by
  rcases associatedPrimes.nonempty R M with ⟨p, hp⟩
  have := depth_le_ringKrullDim_associatedPrime M p hp
  rw [← WithBot.coe_le_coe, WithBot.coe_unbot] at this
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  exact this.trans (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective
    (le_of_eq_of_le Submodule.annihilator_top.symm hp.annihilator_le)))

theorem depth_le_ringKrullDim [IsNoetherianRing R] [IsLocalRing R] [Small.{v, u} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.depth M ≤ ringKrullDim R :=
  (depth_le_supportDim M).trans (Module.supportDim_le_ringKrullDim R M)

theorem depth_ne_top [IsNoetherianRing R] [IsLocalRing R] [Small.{v, u} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.depth M ≠ ⊤ := by
  have := lt_of_le_of_lt (depth_le_ringKrullDim M) ringKrullDim_lt_top
  simp only [← WithBot.coe_top, WithBot.coe_lt_coe] at this
  exact this.ne_top
