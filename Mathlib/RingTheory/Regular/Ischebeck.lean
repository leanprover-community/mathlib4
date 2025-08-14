/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.RingTheory.Regular.Depth
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!

# The Ischebeck theorem and its corollary

-/

namespace CategoryTheory

universe w v u

open Abelian Limits ZeroObject Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable (X I P Y : C)

section Injective

instance Abelian.Ext.subsingleton_of_injective [Injective I] (n : ℕ) [hn : NeZero n] :
    Subsingleton (Ext X I n) := by
  rw [← Nat.succ_pred_eq_of_ne_zero hn.1]
  exact subsingleton_of_forall_eq 0 eq_zero_of_injective

variable {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
  (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) [NeZero n₀]

noncomputable def injective_dim_shifting : Ext X S.X₃ n₀ ≃+ Ext X S.X₁ n₁ :=
  have : NeZero n₁ := by
    rw [← h]
    infer_instance
  have : IsIso (AddCommGrp.ofHom (hS.extClass.postcomp X h)) :=
    ComposableArrows.Exact.isIso_map' (covariantSequence_exact X hS n₀ n₁ h) 1 (by decide)
      (IsZero.eq_zero_of_src (AddCommGrp.of (Ext X S.X₂ n₀)).isZero_of_subsingleton _)
      (IsZero.eq_zero_of_tgt (AddCommGrp.of (Ext X S.X₂ n₁)).isZero_of_subsingleton _)
  (CategoryTheory.asIso (AddCommGrp.ofHom (hS.extClass.postcomp X h))).addCommGroupIsoToAddEquiv

lemma injective_dim_shifting_apply (e : Ext X S.X₃ n₀) :
  injective_dim_shifting X hS n₀ n₁ h e = hS.extClass.postcomp X h e := rfl

end Injective

section Projective

omit [HasExt C] in
theorem shortExact_kernel_of_epi {X Y : C} (e : X ⟶ Y) [he : Epi e] :
    (ShortComplex.mk (kernel.ι e) e (kernel.condition e)).ShortExact where
  exact := ShortComplex.exact_kernel e
  mono_f := equalizer.ι_mono
  epi_g := he

instance Abelian.Ext.subsingleton_of_projective [Projective P] (n : ℕ) [hn : NeZero n] :
    Subsingleton (Ext P Y n) := by
  rw [← Nat.succ_pred_eq_of_ne_zero hn.1]
  exact subsingleton_of_forall_eq 0 eq_zero_of_projective

variable {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
  (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) [NeZero n₀]

noncomputable def projective_dim_shifting : Ext S.X₁ Y n₀ ≃+ Ext S.X₃ Y n₁ :=
  have : NeZero n₁ := by
    rw [← h]
    infer_instance
  have : IsIso (AddCommGrp.ofHom (hS.extClass.precomp Y h)) :=
    ComposableArrows.Exact.isIso_map' (contravariantSequence_exact hS Y n₀ n₁ h) 1 (by decide)
      (IsZero.eq_zero_of_src (AddCommGrp.of (Ext S.X₂ Y n₀)).isZero_of_subsingleton _)
      (IsZero.eq_zero_of_tgt (AddCommGrp.of (Ext S.X₂ Y n₁)).isZero_of_subsingleton _)
  (CategoryTheory.asIso (AddCommGrp.ofHom (hS.extClass.precomp Y h))).addCommGroupIsoToAddEquiv

lemma projective_dim_shifting_apply (e : Ext S.X₁ Y n₀) :
  projective_dim_shifting Y hS n₀ n₁ h e = hS.extClass.precomp Y h e := rfl

end Projective

end CategoryTheory

open IsLocalRing LinearMap ModuleCat Pointwise
open RingTheory.Sequence Ideal CategoryTheory Abelian Limits

universe u v

variable {R : Type u} [CommRing R]

local instance [Small.{v} R] : CategoryTheory.HasExt.{max u v} (ModuleCat.{v} R) :=
  --CategoryTheory.HasExt.standard (ModuleCat.{v} R)
  CategoryTheory.hasExt_of_enoughProjectives.{max u v} (ModuleCat.{v} R)

instance [Small.{v} R] [IsNoetherianRing R] (N M : ModuleCat.{v} R)
    [Module.Finite R N] [Module.Finite R M] (i : ℕ) : Module.Finite R (Ext.{max u v} N M i) := sorry

lemma quotSMulTop_nontrivial [IsLocalRing R] {x : R} (mem : x ∈ maximalIdeal R)
    (L : Type*) [AddCommGroup L] [Module R L] [Module.Finite R L] [Nontrivial L] :
    Nontrivial (QuotSMulTop x L) := by
  apply Submodule.Quotient.nontrivial_of_lt_top _ (Ne.lt_top' _)
  apply Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
  exact IsLocalRing.maximalIdeal_le_jacobson _ mem

theorem moduleDepth_ge_depth_sub_dim [IsNoetherianRing R] [IsLocalRing R] (M N : ModuleCat.{v} R)
    [Module.Finite R M] [Nfin : Module.Finite R N] [Nontrivial M] [Nntr : Nontrivial N]
    [Small.{v} R] : moduleDepth N M ≥ IsLocalRing.depth M -
    (Module.supportDim R N).unbot (Module.supportDim_ne_bot_of_nontrivial R N) := by
  generalize dim :
    ((Module.supportDim R N).unbot (Module.supportDim_ne_bot_of_nontrivial R N)).toNat = r
  induction' r using Nat.strong_induction_on with r ihr generalizing N
  by_cases eq0 : r = 0
  · by_cases eqtop : (Module.supportDim R N).unbot (Module.supportDim_ne_bot_of_nontrivial R N) = ⊤
    · simp [eqtop]
    · rw [← ENat.coe_toNat eqtop, dim]
      show moduleDepth N M ≥ IsLocalRing.depth M - r
      simp only [eq0, ENat.toNat_eq_zero, WithBot.unbot_eq_iff, WithBot.coe_zero, eqtop,
        or_false] at dim
      have smul_lt : (maximalIdeal R) • (⊤ : Submodule R M) < (⊤ : Submodule R M) :=
        Ne.lt_top' (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M)))
      simp [eq0, IsLocalRing.depth, moduleDepth_eq_depth_of_supp_eq (maximalIdeal R) N M smul_lt
        <| support_of_supportDim_eq_zero R N dim]
  · have eqr (n : ℕ∞) : n.toNat = r → n = r := by
      let _ : NeZero r := ⟨eq0⟩
      simp
    refine (IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
      (motive := fun L ↦ (∀ (Lntr : Nontrivial L),
        (((Module.supportDim R L).unbot (Module.supportDim_ne_bot_of_nontrivial R L))).toNat = r →
        (moduleDepth (ModuleCat.of R L) M ≥ IsLocalRing.depth M -
        (Module.supportDim R L).unbot (Module.supportDim_ne_bot_of_nontrivial R L)))) R Nfin)
        ?_ ?_ ?_ Nntr dim
    · intro L _ _ _ Ltr Lntr
      absurd Ltr
      exact (not_subsingleton_iff_nontrivial.mpr Lntr)
    · intro L _ _ _ p e Lntr dim_eq
      rw [eqr _ dim_eq]
      obtain ⟨x, hx⟩ : ((maximalIdeal R : Set R) \ (p.asIdeal: Set R)).Nonempty  := by
        rw [Set.diff_nonempty]
        by_contra sub
        have := Ideal.IsMaximal.eq_of_le (maximalIdeal.isMaximal R) IsPrime.ne_top' sub
        have : Module.supportDim R (R ⧸ p.asIdeal) = 0 := by
          let _ : Field (R ⧸ maximalIdeal R) := Quotient.field (maximalIdeal R)
          rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, ← this,
            Ideal.annihilator_quotient, ringKrullDim_eq_zero_of_field]
        absurd eqr _ dim_eq
        simpa only [Module.supportDim_eq_of_equiv e, this, WithBot.unbot_zero,
          ← ENat.coe_zero, ENat.coe_inj, eq_comm] using eq0
      let S := (ModuleCat.of R L).smulShortComplex x
      have reg' : Function.Injective (x • (LinearMap.id (R := R) (M := L))) := by
        rw [← LinearMap.ker_eq_bot]
        ext l
        simp only [mem_ker, smul_apply, id_coe, id_eq, Submodule.mem_bot]
        refine ⟨fun h ↦ ?_, fun h ↦ smul_eq_zero_of_right x h⟩
        apply e.injective
        have : (Ideal.Quotient.mk p.asIdeal x) * e l = 0 := by
          have : (Ideal.Quotient.mk p.asIdeal x) * e l = x • e l := rfl
          rw [this, ← map_smul, h, map_zero]
        rcases mul_eq_zero.mp this with xzero|zero
        · absurd xzero
          exact Ideal.Quotient.eq_zero_iff_mem.not.mpr (Set.notMem_of_mem_diff hx)
        · rw [zero, map_zero]
      have reg : IsSMulRegular (ModuleCat.of R L) x := reg'
      have hS := reg.smulShortComplex_shortExact
      apply le_sSup
      intro i hi
      have : Subsingleton (Ext.{max u v} (ModuleCat.of R (QuotSMulTop x L)) M (i + 1)) := by
        have ntr : Nontrivial (QuotSMulTop x L) := quotSMulTop_nontrivial (Set.mem_of_mem_diff hx) L
        have dimlt' : (Module.supportDim R (QuotSMulTop x L)).unbot
          (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L)) < r := by
          have : (Module.supportDim R (QuotSMulTop x L)) + 1 ≤ Module.supportDim R L := by
            simp only [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
            rw [LinearEquiv.annihilator_eq e, Ideal.annihilator_quotient]
            have ple : p.asIdeal ≤ Module.annihilator R (QuotSMulTop x L) := by
              rw [Submodule.annihilator_quotient, ← Ideal.annihilator_quotient (I := p.asIdeal),
                ← LinearEquiv.annihilator_eq e, ← Submodule.annihilator_top, ← Submodule.colon_bot]
              exact Submodule.colon_mono bot_le (le_refl ⊤)
            let f := Quotient.factor ple
            have mem_ann : x ∈ Module.annihilator R (QuotSMulTop x L) := by
              apply Module.mem_annihilator.mpr (fun l ↦ ?_)
              induction' l using Submodule.Quotient.induction_on with l
              simpa [← Submodule.Quotient.mk_smul] using
                Submodule.smul_mem_pointwise_smul l x ⊤ trivial
            have : Ideal.Quotient.mk p.asIdeal x ∈ nonZeroDivisors (R ⧸ p.asIdeal) := by
              simpa [Ideal.Quotient.eq_zero_iff_mem] using Set.notMem_of_mem_diff hx
            exact ringKrullDim_succ_le_of_surjective (Quotient.factor ple)
              (Quotient.factor_surjective ple) this
              (by simpa [Quotient.eq_zero_iff_mem] using mem_ann)
          have succle : (Module.supportDim R (QuotSMulTop x L)).unbot
            (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L)) + 1 ≤ r := by
            simpa [← eqr _ dim_eq, WithBot.le_unbot_iff] using this
          have : (Module.supportDim R (QuotSMulTop x L)).unbot
            (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L)) ≠ ⊤ := by
            by_contra h
            simp [h] at succle
          exact (ENat.add_one_le_iff this).mp succle
        have dimlt : ((Module.supportDim R (QuotSMulTop x L)).unbot
          (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L))).toNat < r := by
          rw [← ENat.coe_lt_coe, ENat.coe_toNat (ne_top_of_lt dimlt')]
          exact dimlt'
        apply ext_subsingleton_of_lt_moduleDepth
        refine lt_of_lt_of_le ?_ (ihr _ dimlt (ModuleCat.of R (QuotSMulTop x L)) rfl)
        rcases ENat.ne_top_iff_exists.mp (ne_top_of_lt dimlt') with ⟨m, hm⟩
        by_cases eqtop : IsLocalRing.depth M = ⊤
        · simp only [Nat.cast_add, eqtop, ← hm, ENat.top_sub_coe, ENat.add_lt_top,
            ENat.coe_lt_top, true_and]
        · rcases ENat.ne_top_iff_exists.mp eqtop with ⟨k, hk⟩
          have : (i + 1 : ℕ) ≤ IsLocalRing.depth M - r := by
            simpa [ENat.add_one_le_iff (ENat.coe_ne_top i)] using hi
          apply lt_of_le_of_lt this
          have le : r ≤ k := by
            simp only [← hk, ← ENat.coe_sub, Nat.cast_lt] at hi
            omega
          simp only [← hk, ← ENat.coe_sub, ← hm, Nat.cast_lt]
          simp only [← hm, Nat.cast_lt] at dimlt'
          omega
      have zero : IsZero
        (AddCommGrp.of (Ext.{max u v} (ModuleCat.of R (QuotSMulTop x L)) M (i + 1))) :=
        @AddCommGrp.isZero_of_subsingleton _ this
      have epi' : Function.Surjective
        ⇑(x • LinearMap.id (R := R) (M := (Ext.{max u v} (of R L) M i))) := by
        convert (AddCommGrp.epi_iff_surjective _).mp <| ShortComplex.Exact.epi_f
          (Ext.contravariant_sequence_exact₁' hS M i (i + 1) (Nat.add_comm 1 i))
          (zero.eq_zero_of_tgt _)
        ext a
        change x • a = Ext.bilinearCompOfLinear R _ _ _ _ _ _ (zero_add i)
          ((Ext.homEquiv₀_linearHom R).symm
          (ModuleCat.homLinearEquiv.symm (S := R) (x • LinearMap.id))) a
        simp only [map_smul, smul_apply]
        congr
        exact (Ext.mk₀_id_comp a).symm
      have range : LinearMap.range (x • LinearMap.id) =
        x • (⊤ : Submodule R (Ext.{max u v} (of R L) M i)) := by
        ext y
        simp only [mem_range, smul_apply, id_coe, id_eq, Submodule.mem_smul_pointwise_iff_exists,
          Submodule.mem_top, true_and]
      by_contra ntr
      rw [not_subsingleton_iff_nontrivial] at ntr
      have mem : x ∈ (Module.annihilator R (Ext.{max u v} (of R L) M i)).jacobson :=
        IsLocalRing.maximalIdeal_le_jacobson _ (Set.mem_of_mem_diff hx)
      absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator mem
      nth_rw 1 [← LinearMap.range_eq_top_of_surjective _ epi', ← range]
    · intro L1 _ _ _ L2 _ _ _ L3 _ _ _ f g inj surj exac ih1' ih3' L2ntr dim_eq
      rw [eqr _ dim_eq]
      by_cases ntr : Nontrivial L1 ∧ Nontrivial L3
      · let _ := ntr.1
        let _ := ntr.2
        have dimle1' : ((Module.supportDim R L1).unbot
          (Module.supportDim_ne_bot_of_nontrivial R L1)) ≤ r := by
          rw [← (eqr _ dim_eq), ← WithBot.coe_le_coe, WithBot.coe_unbot, WithBot.coe_unbot]
          exact Module.supportDim_le_of_injective f inj
        have dimle3' : ((Module.supportDim R L3).unbot
          (Module.supportDim_ne_bot_of_nontrivial R L3)) ≤ r := by
          rw [← (eqr _ dim_eq), ← WithBot.coe_le_coe, WithBot.coe_unbot, WithBot.coe_unbot]
          exact Module.supportDim_le_of_surjective g surj
        have ge1 : moduleDepth (of R L1) M ≥ IsLocalRing.depth M - ((Module.supportDim R L1).unbot
          (Module.supportDim_ne_bot_of_nontrivial R L1)) := by
          rcases lt_or_eq_of_le (ENat.toNat_le_of_le_coe dimle1') with lt|eq
          · exact ihr _ lt (ModuleCat.of.{v} R L1) rfl
          · exact ih1' ntr.1 eq
        have ge3 : moduleDepth (of R L3) M ≥ IsLocalRing.depth M - ((Module.supportDim R L3).unbot
          (Module.supportDim_ne_bot_of_nontrivial R L3)) := by
          rcases lt_or_eq_of_le (ENat.toNat_le_of_le_coe dimle3') with lt|eq
          · exact ihr _ lt (ModuleCat.of.{v} R L3) rfl
          · exact ih3' ntr.2 eq
        let S : ShortComplex (ModuleCat.{v} R) := {
          X₁ := ModuleCat.of R L1
          X₂ := ModuleCat.of R L2
          X₃ := ModuleCat.of R L3
          f := ModuleCat.ofHom f
          g := ModuleCat.ofHom g
          zero := by
            ext
            simp [Function.Exact.apply_apply_eq_zero exac] }
        have hS : S.ShortExact := {
          exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr exac
          mono_f := (ModuleCat.mono_iff_injective S.f).mpr inj
          epi_g := (ModuleCat.epi_iff_surjective S.g).mpr surj }
        exact ge_trans (moduleDepth_ge_min_of_shortExact_fst S hS M) (le_inf_iff.mpr
          ⟨le_trans (tsub_le_tsub_left dimle1' _) ge1, le_trans (tsub_le_tsub_left dimle3' _) ge3⟩)
      · have : Subsingleton L1 ∨ Subsingleton L3 := by
          simpa [← not_nontrivial_iff_subsingleton] using Classical.not_and_iff_not_or_not.mp ntr
        rcases this with sub1|sub3
        · have : Function.Injective g := by
            rw [← ker_eq_bot, exact_iff.mp exac, range_eq_bot, Subsingleton.eq_zero f]
          let eg : L2 ≃ₗ[R] L3 := LinearEquiv.ofBijective g ⟨this, surj⟩
          let L3ntr : Nontrivial L3 := Function.Injective.nontrivial this
          have dimeq3 : (((Module.supportDim R L3).unbot
            (Module.supportDim_ne_bot_of_nontrivial R L3))).toNat = r := by
            rw [← dim_eq]
            congr 2
            exact (Module.supportDim_eq_of_equiv eg).symm
          rw [moduleDepth_eq_of_iso_fst M eg.toModuleIso, ← eqr _ dimeq3]
          exact ih3' L3ntr dimeq3
        · have : Function.Surjective f := by
            rw [← range_eq_top, ← exact_iff.mp exac, ker_eq_top, Subsingleton.eq_zero g]
          let ef : L1 ≃ₗ[R] L2 := LinearEquiv.ofBijective f ⟨inj, this⟩
          let L1ntr : Nontrivial L1 := Function.Surjective.nontrivial this
          have dimeq1 : (((Module.supportDim R L1).unbot
            (Module.supportDim_ne_bot_of_nontrivial R L1))).toNat = r := by
            rw [← dim_eq]
            congr 2
            exact Module.supportDim_eq_of_equiv ef
          rw [← moduleDepth_eq_of_iso_fst M ef.toModuleIso, ← eqr _ dimeq1]
          exact ih1' L1ntr dimeq1

lemma quotient_prime_ringKrullDim_ne_bot {P : Ideal R} (prime : P.IsPrime) :
    ringKrullDim (R ⧸ P) ≠ ⊥ :=
  ne_bot_of_le_ne_bot WithBot.zero_ne_bot (@ringKrullDim_nonneg_of_nontrivial _ _ (
        Quotient.nontrivial prime.ne_top'))

theorem depth_le_ringKrullDim_associatedPrime [IsNoetherianRing R] [IsLocalRing R]
    [Small.{v} R] (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] (P : Ideal R)
    (ass : P ∈ associatedPrimes R M) : IsLocalRing.depth M ≤ (ringKrullDim (R ⧸ P)).unbot
      (quotient_prime_ringKrullDim_ne_bot ass.1) := by
  let _ := Quotient.nontrivial ass.1.ne_top'
  let _ : Module.Finite R (Shrink.{v} (R ⧸ P)) :=
    Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ P)).symm
  let _ : Nontrivial (Shrink.{v} (R ⧸ P)) :=
    (Shrink.linearEquiv R (R ⧸ P)).nontrivial
  have dep0 : moduleDepth (of R (Shrink.{v} (R ⧸ P))) M = 0 := by
    rw [moduleDepth_eq_zero_of_hom_nontrivial,
      (LinearEquiv.congrLeft M R (Shrink.linearEquiv R (R ⧸ P))).nontrivial_congr]
    rcases ((isAssociatedPrime_iff_exists_injective_linearMap P M).mp
      (AssociatePrimes.mem_iff.mp ass)).2 with ⟨f, hf⟩
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
