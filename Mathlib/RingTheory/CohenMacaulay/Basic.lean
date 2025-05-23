/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.Regular.Ischebeck
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Spectrum.Prime.Module

/-!
# Definition of Cohen-Macaulay Ring

-/

universe v' v u' u

variable {R : Type u} [CommRing R]

open RingTheory.Sequence IsLocalRing ModuleCat

class ModuleCat.IsCohenMacaulay [IsLocalRing R] [Small.{v} R] (M : ModuleCat.{v} R) : Prop where
  depth_eq_dim : Subsingleton M ∨ Module.supportDim R M = IsLocalRing.depth M

lemma ModuleCat.isCohenMacaulay_iff [IsLocalRing R] [Small.{v} R] (M : ModuleCat.{v} R) :
    M.IsCohenMacaulay ↔ Subsingleton M ∨ Module.supportDim R M = IsLocalRing.depth M :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma ModuleCat.depth_eq_supportDim_of_cohenMacaulay [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [cm : M.IsCohenMacaulay] [ntr : Nontrivial M] :
    Module.supportDim R M = IsLocalRing.depth M := by
  have : ¬ Subsingleton M := not_subsingleton_iff_nontrivial.mpr ntr
  have := M.isCohenMacaulay_iff.mp cm
  tauto

lemma ModuleCat.depth_eq_supportDim_unbot_of_cohenMacaulay [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [cm : M.IsCohenMacaulay] [ntr : Nontrivial M] :
    (Module.supportDim R M).unbot
    (Module.supportDim_ne_bot_of_nontrivial R M) = IsLocalRing.depth M := by
  simp [M.depth_eq_supportDim_of_cohenMacaulay]

lemma ModuleCat.IsCohenMacaulay_of_iso [IsLocalRing R] [Small.{v} R] {M M' : ModuleCat.{v} R}
    (e : M ≅ M') [M.IsCohenMacaulay] : M'.IsCohenMacaulay := by
  rw [M'.isCohenMacaulay_iff]
  by_cases ntr : Nontrivial M
  · right
    rw [← IsLocalRing.depth_eq_of_iso e,
      ← Module.supportDim_eq_of_equiv e.toLinearEquiv, M.depth_eq_supportDim_of_cohenMacaulay]
  · simp [← e.toLinearEquiv.subsingleton_congr, not_nontrivial_iff_subsingleton.mp ntr]

--isCohenMacaulay universe invariant

section IsLocalization

variable [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R) [Small.{v} R]

lemma depth_eq_dim_quotient_associated_prime_of_isCohenMacaulay (M : ModuleCat.{v} R)
    [M.IsCohenMacaulay] [Module.Finite R M] [Nontrivial M] [Small.{v} (R ⧸ p)]
    (mem : p ∈ associatedPrimes R M) :
    IsLocalRing.depth M = (ringKrullDim (R ⧸ p)).unbot
    (quotient_prime_ringKrullDim_ne_bot mem.1) := by
  apply le_antisymm (depth_le_ringKrullDim_associatedPrime M p mem)
  rw [← M.depth_eq_supportDim_unbot_of_cohenMacaulay]
  rw [← WithBot.coe_le_coe, WithBot.coe_unbot, WithBot.coe_unbot,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective
    (le_of_eq_of_le Submodule.annihilator_top.symm (AssociatePrimes.mem_iff.mp mem).annihilator_le))

--will update the two sets are equal when done with works about `Ass(M)`
lemma associated_prime_minimal_of_isCohenMacaulay (M : ModuleCat.{v} R)
    [M.IsCohenMacaulay] [Module.Finite R M] [Nontrivial M] [Small.{v} (R ⧸ p)]
    (mem : p ∈ associatedPrimes R M) : p ∈ (Module.annihilator R M).minimalPrimes := by
  have eq := Eq.trans M.depth_eq_supportDim_unbot_of_cohenMacaulay
    (depth_eq_dim_quotient_associated_prime_of_isCohenMacaulay p M mem)
  rw [← WithBot.coe_inj, WithBot.coe_unbot, WithBot.coe_unbot, ringKrullDim_quotient,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator, ringKrullDim_quotient] at eq
  let _ : p.IsPrime := mem.1
  have ann_le : Module.annihilator R M ≤ p := (le_of_eq_of_le Submodule.annihilator_top.symm
    (AssociatePrimes.mem_iff.mp mem).annihilator_le)
  rcases Ideal.exists_minimalPrimes_le ann_le with ⟨p', hp', le⟩
  rcases lt_or_eq_of_le le with lt|eq
  · classical
    let f : WithBot (PrimeSpectrum.zeroLocus (p : Set R)) →
        (PrimeSpectrum.zeroLocus ((Module.annihilator R M) : Set R)):= fun I ↦ by
        by_cases eqbot : I = ⊥
        · exact ⟨⟨p', Ideal.minimalPrimes_isPrime hp'⟩, hp'.1.2⟩
        · exact ⟨(I.unbot eqbot).1, PrimeSpectrum.zeroLocus_anti_mono ann_le (I.unbot eqbot).2⟩
    have f_mono : StrictMono f := by
      intro a b alt
      by_cases eqbot : a = ⊥
      · simp only [eqbot, ↓reduceDIte, alt.ne_bot, Subtype.mk_lt_mk, f]
        apply lt_of_lt_of_le lt (b.unbot alt.ne_bot).2
      · simp only [eqbot, ↓reduceDIte, alt.ne_bot, Subtype.mk_lt_mk, Subtype.coe_lt_coe, f]
        rw [← WithBot.coe_lt_coe, WithBot.coe_unbot, WithBot.coe_unbot]
        exact alt
    have dim_le := Order.krullDim_le_of_strictMono f f_mono
    let _ : Nonempty (PrimeSpectrum.zeroLocus (p : Set R)) := Nonempty.intro ⟨⟨p, mem.1⟩, le_refl p⟩
    rw [Order.krullDim_withBot, eq, ← ringKrullDim_quotient] at dim_le
    have nebot : ringKrullDim (R ⧸ p) ≠ ⊥ := quotient_prime_ringKrullDim_ne_bot mem.1
    have netop : (ringKrullDim (R ⧸ p)).unbot nebot ≠ ⊤ := by
      have : FiniteRingKrullDim R := instFiniteRingKrullDimOfIsNoetherianRingOfIsLocalRing
      have : ringKrullDim (R ⧸ p) ≠ ⊤ :=
        ne_top_of_le_ne_top ringKrullDim_ne_top
         (ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) (Ideal.Quotient.mk_surjective))
      simpa [← WithBot.coe_inj.not]
    rcases ENat.ne_top_iff_exists.mp netop with ⟨m, hm⟩
    have : (ringKrullDim (R ⧸ p)).unbot nebot + 1 ≤ (ringKrullDim (R ⧸ p)).unbot nebot := by
      rw [← WithBot.coe_le_coe]
      simpa using dim_le
    absurd this
    rw [← hm, not_le, ← ENat.coe_one, ← ENat.coe_add, ENat.coe_lt_coe]
    exact lt_add_one m
  · simpa [← eq] using hp'

lemma ENat.add_right_cancel_iff (a b c : ℕ∞) (netop : c ≠ ⊤) : a + c = b + c ↔ a = b :=
  ⟨fun h ↦ ENat.add_left_injective_of_ne_top netop h, fun h ↦ by rw [h]⟩

lemma withBotENat_add_coe_cancel (a b : WithBot ℕ∞) (c : ℕ) : a + c = b + c ↔ a = b := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  by_cases eqbot : a = ⊥
  · simp [eqbot, WithBot.bot_add] at h
    rw [WithBot.add_coe_eq_bot_iff.mp h.symm, eqbot]
  · by_cases eqbot' : b = ⊥
    · absurd eqbot
      simpa [eqbot'] using h
    · have : a.unbot eqbot + c = b.unbot eqbot' + c := by
        apply WithBot.coe_inj.mp
        convert h
        repeat simp;rfl
      rw [← WithBot.coe_unbot a eqbot, ← WithBot.coe_unbot b eqbot', WithBot.coe_inj]
      simpa [ENat.add_right_cancel_iff _ _ _ (ENat.coe_ne_top c)] using this

lemma quotSMulTop_isCohenMacaulay_iff_isCohenMacaulay (M : ModuleCat.{v} R) [Module.Finite R M]
    (r : R) (reg : IsSMulRegular M r) (mem : r ∈ maximalIdeal R) :
     M.IsCohenMacaulay ↔ (ModuleCat.of R (QuotSMulTop r M)).IsCohenMacaulay := by
  simp only [ModuleCat.isCohenMacaulay_iff]
  by_cases ntr : Subsingleton M
  · have : Subsingleton (QuotSMulTop r M) := Function.Surjective.subsingleton
      (Submodule.mkQ_surjective _)
    simp [ntr, this]
  · have ntr1 : Nontrivial M := not_subsingleton_iff_nontrivial.mp ntr
    have ntr2 : Nontrivial (QuotSMulTop r M) := quotSMulTop_nontrivial mem M
    simp only [not_subsingleton_iff_nontrivial.mpr ntr2, false_or, ntr]
    rw [← Module.supportDim_quotSMulTop_succ_eq_supportDim r reg mem,
      ← IsLocalRing.depth_quotSMulTop_succ_eq_moduleDepth M r reg mem, WithBot.coe_add]
    exact withBotENat_add_coe_cancel _ _ 1

lemma quotient_regular_isCohenMacaulay_iff_isCohenMacaulay
    (M : ModuleCat.{v} R) [Module.Finite R M] (rs : List R) (reg : IsRegular M rs) :
    M.IsCohenMacaulay ↔
    (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))).IsCohenMacaulay := by
  have ntr2 : Nontrivial (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) :=
    (IsRegular.quot_ofList_smul_nontrivial reg ⊤)
  have ntr1 : Nontrivial M := Function.Surjective.nontrivial (Submodule.mkQ_surjective
    (Ideal.ofList rs • (⊤ : Submodule R M)))
  simp only [isCohenMacaulay_iff, ← not_nontrivial_iff_subsingleton, ntr1, not_true_eq_false,
    false_or, ntr2]
  rw [← Module.supportDim_regular_sequence_add_length_eq_supportDim rs reg,
    ← depth_quotient_regular_sequence_add_length_eq_depth M rs reg, WithBot.coe_add]
  exact withBotENat_add_coe_cancel _ _ rs.length

variable [p.IsPrime] {Rₚ : Type u'} [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
  [IsLocalRing Rₚ]
  -- This can be deduced from `IsLocalization.AtPrime Rₚ p`, but cannot be an
  -- `instance`, so we need to manually add this condition.

abbrev SemiLinearMapAlgebraMapOfLinearMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₗ[R] N) : M →ₛₗ[algebraMap R A] N where
  __ := f
  map_smul' m r := by simp

abbrev LinearMapOfSemiLinearMapAlgebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₛₗ[algebraMap R A] N) : M →ₗ[R] N where
  __ := f
  map_smul' m r := by simp

variable (Rₚ) in
omit [IsLocalRing R] [IsNoetherianRing R] [Small.{v, u} R] [IsLocalRing Rₚ]
  [IsLocalization.AtPrime Rₚ p] in
open Pointwise in
lemma isLocaliation_map_isSMulRegular_of_isSMulRegular (r : R)
    (M : Type*) [AddCommGroup M] [Module R M] (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]
    (reg : IsSMulRegular M r) : IsSMulRegular Mₚ (algebraMap R Rₚ r) := by
  rw [isSMulRegular_algebraMap_iff r, isSMulRegular_iff_ker_lsmul_eq_bot Mₚ r,
    LinearMap.ker_eq_bot']
  intro m hm
  rcases IsLocalizedModule.mk'_surjective p.primeCompl f m with ⟨a, ha⟩
  simp only [← ha, LinearMap.lsmul_apply] at hm ⊢
  have : r • IsLocalizedModule.mk' f a.1 a.2 = 0 := hm
  rw [← IsLocalizedModule.mk'_smul, IsLocalizedModule.mk'_eq_zero'] at this
  simp only [Subtype.exists, Submonoid.mk_smul, exists_prop] at this
  rcases this with ⟨s, mem, hs⟩
  rw [smul_smul, mul_comm, ← smul_smul] at hs
  apply (IsLocalizedModule.mk'_eq_zero' f a.2).mpr ⟨⟨s, mem⟩, ?_⟩
  simp only [Submonoid.mk_smul, ← Submodule.mem_bot (R := R),
    ← (isSMulRegular_iff_ker_lsmul_eq_bot M r).mp reg]
  exact hs

variable (Rₚ) in
abbrev quotSMulTop_isLocalizedModule_map (x : R) (M : Type*) [AddCommGroup M] [Module R M]
    (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f] :
    QuotSMulTop x M →ₗ[R] QuotSMulTop ((algebraMap R Rₚ) x) Mₚ :=
  LinearMapOfSemiLinearMapAlgebraMap (Submodule.mapQ _ _
    (SemiLinearMapAlgebraMapOfLinearMap f)
    (fun m hm ↦ by
      rw [← Submodule.ideal_span_singleton_smul] at hm
      simp only [Submodule.mem_comap, LinearMap.coe_mk, LinearMap.coe_toAddHom]
      refine Submodule.smul_induction_on hm (fun r hr m hm ↦ ?_)
        (fun m1 m2 hm1 hm2 ↦ by simpa using Submodule.add_mem _ hm1 hm2)
      rcases Ideal.mem_span_singleton'.mp hr with ⟨r', hr'⟩
      simpa only [← hr', map_smul, mul_comm r' x, ← smul_smul,
        algebra_compatible_smul Rₚ x (r' • f m)]
        using Submodule.smul_mem_pointwise_smul (r' • f m) ((algebraMap R Rₚ) x) ⊤ hm))

variable (Rₚ) in
omit [IsLocalRing R] [IsNoetherianRing R] [Small.{v, u} R] [IsLocalRing Rₚ] in
lemma isLocalizedModule_quotSMulTop_isLocalizedModule_map (x : R)
    (M : Type*) [AddCommGroup M] [Module R M] (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f] :
    IsLocalizedModule.AtPrime p (quotSMulTop_isLocalizedModule_map p Rₚ x M Mₚ f) where
  map_units r := by
    let alg := (Algebra.algHom R Rₚ (Module.End Rₚ (QuotSMulTop ((algebraMap R Rₚ) x) Mₚ)))
    rcases isUnit_iff_exists.mp (IsUnit.algebraMap_of_algebraMap (r := r.1) alg.toLinearMap
      (map_one alg) (IsLocalization.map_units Rₚ r)) with ⟨s, hs1, hs2⟩
    exact isUnit_iff_exists.mpr ⟨LinearMap.restrictScalars R s,
      ⟨LinearMap.ext (fun x ↦ by simpa using DFunLike.congr hs1 (Eq.refl x)),
        LinearMap.ext (fun x ↦ by simpa using DFunLike.congr hs2 (Eq.refl x))⟩⟩
  surj' y := by
    induction' y using Submodule.Quotient.induction_on with y
    rcases IsLocalizedModule.surj' (S := p.primeCompl) (f := f) y with ⟨z, hz⟩
    use (Submodule.Quotient.mk z.1, z.2)
    simp [← hz]
  exists_of_eq {y1 y2} h := by
    induction' y1 using Submodule.Quotient.induction_on with y1
    induction' y2 using Submodule.Quotient.induction_on with y2
    simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, Submodule.mapQ_apply] at h
    have h := (Submodule.Quotient.mk_eq_zero _).mp (sub_eq_zero_of_eq h)
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h with ⟨m, _, hm⟩
    rcases IsLocalizedModule.surj p.primeCompl f m with ⟨⟨z, s⟩, hz⟩
    have eq : f (s • (y1 - y2)) = f (x • z) := by simp [← hm, ← hz, smul_comm s x m]
    rcases IsLocalizedModule.exists_of_eq (S := p.primeCompl) eq with ⟨c, hc⟩
    use c * s
    apply sub_eq_zero.mp
    have h : (0 : QuotSMulTop x M) = Submodule.Quotient.mk (c • s • (y1 - y2)) := by
      simpa [hc] using (smul_eq_zero_of_right c <| (Submodule.Quotient.mk_eq_zero _).mpr <|
        Submodule.smul_mem_pointwise_smul z x ⊤ Submodule.mem_top).symm
    simp [h, smul_sub, mul_smul]

variable (Rₚ) in
omit [IsLocalRing R] [IsNoetherianRing R] [Small.{v, u} R] [IsLocalRing Rₚ] in
open Pointwise in
lemma isLocaliation_map_is_weakly_regular_of_is_weakly_regular (rs : List R)
    (M : Type*) [AddCommGroup M] [Module R M] (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]
    (reg : IsWeaklyRegular M rs) : IsWeaklyRegular Mₚ (rs.map (algebraMap R Rₚ)) := by
  generalize len : rs.length = n
  induction' n with n ih generalizing M Mₚ rs
  · simp [List.length_eq_zero_iff.mp len]
  · match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [isWeaklyRegular_cons_iff, List.map_cons] at reg ⊢
      refine ⟨isLocaliation_map_isSMulRegular_of_isSMulRegular p Rₚ x M Mₚ f reg.1, ?_⟩
      let g := quotSMulTop_isLocalizedModule_map p Rₚ x M Mₚ f
      have := isLocalizedModule_quotSMulTop_isLocalizedModule_map p Rₚ x M Mₚ f
      exact ih rs' (QuotSMulTop x M) (QuotSMulTop ((algebraMap R Rₚ) x) Mₚ) g reg.2 len

variable [Small.{v'} Rₚ] [IsNoetherianRing Rₚ]

variable (M : ModuleCat.{v} R) (Mₚ : ModuleCat.{v'} Rₚ)
  [Module R Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f] [IsScalarTower R Rₚ Mₚ]

include p f

lemma isLocalization_at_prime_prime_depth_le_depth [Small.{v} (R ⧸ p)] [Module.Finite R M]
    [Nontrivial M] [Nontrivial Mₚ] : p.depth M ≤ IsLocalRing.depth Mₚ := by
  let _ : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule p.primeCompl f
  simp only [IsLocalRing.depth_eq_sSup_length_regular, Ideal.depth]
  let _ : Module.Finite R (Shrink.{v, u} (R ⧸ p)) :=
    Module.Finite.equiv (Shrink.linearEquiv (R ⧸ p) R).symm
  have smul_lt : p • (⊤ : Submodule R M) < ⊤ :=
    Ne.lt_top' (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      ((IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top')).trans
      (IsLocalRing.maximalIdeal_le_jacobson _)))
  have h_supp : Module.support R (of R (Shrink.{v, u} (R ⧸ p))) = PrimeSpectrum.zeroLocus p := by
    rw [(Shrink.linearEquiv (R ⧸ p) R).support_eq, Module.support_eq_zeroLocus,
      Ideal.annihilator_quotient]
  rw [moduleDepth_eq_sSup_length_regular p _ _ smul_lt h_supp]
  apply sSup_le (fun n hn ↦ le_sSup ?_)
  rcases hn with ⟨rs, reg, mem, len⟩
  have mem' : ∀ r ∈ List.map (⇑(algebraMap R Rₚ)) rs, r ∈ maximalIdeal Rₚ := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨r', hr', eq⟩
    rw [← eq, IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p]
    exact mem r' hr'
  have reg' : RingTheory.Sequence.IsRegular (↑Mₚ) (List.map (⇑(algebraMap R Rₚ)) rs) := by
    refine ⟨isLocaliation_map_is_weakly_regular_of_is_weakly_regular
      p Rₚ rs M Mₚ f reg.toIsWeaklyRegular, ?_⟩
    have : Ideal.ofList (List.map (⇑(algebraMap R Rₚ)) rs) • (⊤ : Submodule Rₚ Mₚ) ≤
      maximalIdeal Rₚ • (⊤ : Submodule Rₚ Mₚ) := by
      apply Submodule.smul_mono _ fun _ a ↦ a
      simpa only [Ideal.ofList, Ideal.span_le] using mem'
    apply (ne_top_of_lt (b := ⊤) (lt_of_le_of_lt this (Ne.lt_top (Ne.symm _)))).symm
    exact Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)
  use (rs.map (algebraMap R Rₚ)), reg', mem'
  rw [List.length_map, len]

omit [Small.{v', u'} Rₚ] in
lemma isLocalize_at_prime_dim_eq_prime_depth_of_isCohenMacaulay [Small.{v} (R ⧸ p)]
    [Module.Finite R M] [M.IsCohenMacaulay] [ntr : Nontrivial Mₚ] :
    Module.supportDim Rₚ Mₚ = p.depth M := by
  let _ : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule p.primeCompl f
  let _ : Nontrivial M := by
    by_contra h
    absurd not_subsingleton_iff_nontrivial.mpr ntr
    rw [IsLocalizedModule.subsingleton_iff_ker_eq_top p.primeCompl f]
    have := (Submodule.subsingleton_iff R).mpr (not_nontrivial_iff_subsingleton.mp h)
    apply Subsingleton.elim
  have : p.depth M ≠ ⊤ :=
    ne_top_of_le_ne_top (depth_ne_top M) (ideal_depth_le_depth p Ideal.IsPrime.ne_top' M)
  rcases ENat.ne_top_iff_exists.mp this with ⟨n, hn⟩
  induction' n with n ih generalizing M Mₚ
  · simp only [← hn, CharP.cast_eq_zero, WithBot.coe_zero]
    have min : p ∈ (Module.annihilator R M).minimalPrimes := by
      simp only [CharP.cast_eq_zero, Ideal.depth] at hn
      rw [Eq.comm, moduleDepth_eq_zero_of_hom_nontrivial,
        ((Shrink.linearEquiv (R ⧸ p) R).congrLeft M R).nontrivial_congr] at hn
      obtain ⟨g, hg⟩ : ∃ g : R ⧸ p →ₗ[R] M, g ≠ 0 := exists_ne 0
      have : g 1 ≠ 0 := by
        by_contra eq0
        absurd hg
        apply LinearMap.ext (fun r ↦ ?_)
        induction' r using Submodule.Quotient.induction_on with r
        nth_rw 1 [← mul_one r, ← smul_eq_mul, Submodule.Quotient.mk_smul, map_smul]
        simp [eq0]
      have le : p ≤ LinearMap.ker (LinearMap.toSpanSingleton R M (g 1)) := by
        intro r hr
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul,
          ← map_one (Ideal.Quotient.mk p), ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul]
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
      rcases exists_le_isAssociatedPrime_of_isNoetherianRing R (g 1) this with ⟨p', ass, hp'⟩
      let P : PrimeSpectrum R := ⟨p, by assumption⟩
      have ntr : Nontrivial (LocalizedModule P.asIdeal.primeCompl M) :=
        (IsLocalizedModule.linearEquiv p.primeCompl
          (LocalizedModule.mkLinearMap p.primeCompl M) f).nontrivial
      have mem_supp := Module.mem_support_iff.mpr ntr
      simp only [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus,
        SetLike.coe_subset_coe, P] at mem_supp
      have min := associated_prime_minimal_of_isCohenMacaulay p' M ass
      convert min
      simp only [Ideal.minimalPrimes, Set.mem_setOf_eq] at min
      exact min.eq_of_le ⟨by assumption, mem_supp⟩ (le.trans hp')
    have : Module.support Rₚ Mₚ = {⟨maximalIdeal Rₚ, Ideal.IsMaximal.isPrime' _⟩} := by
      apply le_antisymm
      · intro I hI
        simp only [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus,
          SetLike.coe_subset_coe] at hI
        have le : (Module.annihilator R M).map (algebraMap R Rₚ) ≤ Module.annihilator Rₚ Mₚ := by
          apply Ideal.map_le_iff_le_comap.mpr (fun r hr ↦ ?_)
          simp only [Ideal.mem_comap, Module.mem_annihilator, algebraMap_smul]
          intro m
          rcases (IsLocalizedModule.mk'_surjective p.primeCompl f) m with ⟨⟨l, s⟩, h⟩
          simp [← h, Function.uncurry_apply_pair, ← IsLocalizedModule.mk'_smul,
            Module.mem_annihilator.mp hr l]
        have : maximalIdeal Rₚ ∈
          ((Module.annihilator R M).map (algebraMap R Rₚ)).minimalPrimes := by
          simpa [IsLocalization.minimalPrimes_map p.primeCompl,
            IsLocalization.AtPrime.comap_maximalIdeal Rₚ p] using min
        simp only [Ideal.minimalPrimes, Set.mem_setOf_eq] at this
        exact PrimeSpectrum.ext (this.eq_of_le ⟨I.2, le.trans hI⟩ (le_maximalIdeal_of_isPrime I.1))
      · simpa using IsLocalRing.maximalIdeal_mem_support Rₚ Mₚ
    have : Unique (Module.support Rₚ Mₚ) := by
      simpa [this] using Set.uniqueSingleton _
    exact Order.krullDim_eq_zero_of_unique
  · have : Subsingleton ((ModuleCat.of R (Shrink.{v} (R ⧸ p))) →ₗ[R] M) := by
      by_contra ntr
      rw [not_subsingleton_iff_nontrivial, ← moduleDepth_eq_zero_of_hom_nontrivial] at ntr
      simp [Ideal.depth, ntr] at hn
    rcases IsSMulRegular.subsingleton_linearMap_iff.mp
      (((Shrink.linearEquiv (R ⧸ p) R).congrLeft M R).symm.subsingleton) with ⟨a, mem, reg⟩
    rw [Ideal.annihilator_quotient] at mem
    let M' := ModuleCat.of R (QuotSMulTop a M)
    let _ : Nontrivial M' := quotSMulTop_nontrivial (le_maximalIdeal_of_isPrime p mem) M
    let _ : M'.IsCohenMacaulay := (quotSMulTop_isCohenMacaulay_iff_isCohenMacaulay M a reg
      (le_maximalIdeal_of_isPrime p mem)).mp (by assumption)
    have netop' : p.depth M' ≠ ⊤ :=
      ne_top_of_le_ne_top (depth_ne_top M') (ideal_depth_le_depth p Ideal.IsPrime.ne_top' M')
    have depth_eq : p.depth M'= n := by
      simp only [Nat.cast_add, ← p.depth_quotSMulTop_succ_eq_moduleDepth M a reg mem] at hn
      exact (ENat.add_right_cancel_iff _ _ 1 (ENat.coe_ne_top 1)).mp hn.symm
    let M'ₚ := ModuleCat.of Rₚ (QuotSMulTop ((algebraMap R Rₚ) a) Mₚ)
    have map_mem : (algebraMap R Rₚ) a ∈ maximalIdeal Rₚ :=
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p a _).mpr mem)
    let _ : Nontrivial M'ₚ := quotSMulTop_nontrivial map_mem Mₚ
    have eq_succ : Module.supportDim Rₚ M'ₚ + 1 = Module.supportDim Rₚ Mₚ :=
      Module.supportDim_quotSMulTop_succ_eq_supportDim ((algebraMap R Rₚ) a)
        (isLocaliation_map_isSMulRegular_of_isSMulRegular p Rₚ a M Mₚ f reg) map_mem
    let _ := isLocalizedModule_quotSMulTop_isLocalizedModule_map p Rₚ a M Mₚ f
    have := ih M' M'ₚ (quotSMulTop_isLocalizedModule_map p Rₚ a M Mₚ f) netop' depth_eq.symm
    simp [← eq_succ, ← hn, this, depth_eq]

lemma isLocalize_at_prime_isCohenMacaulay_of_isCohenMacaulay [Module.Finite R M]
    [M.IsCohenMacaulay] : Mₚ.IsCohenMacaulay := by
  let _ : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule p.primeCompl f
  simp only [ModuleCat.isCohenMacaulay_iff]
  by_cases ntr : Subsingleton Mₚ
  · simp [ntr]
  · simp only [ntr, false_or]
    have ntr2 : Nontrivial Mₚ := not_subsingleton_iff_nontrivial.mp ntr
    have ntr1 : Nontrivial M := by
      by_contra h
      absurd ntr
      rw [IsLocalizedModule.subsingleton_iff_ker_eq_top p.primeCompl f]
      have := (Submodule.subsingleton_iff R).mpr (not_nontrivial_iff_subsingleton.mp h)
      apply Subsingleton.elim
    apply le_antisymm _ (depth_le_supportDim Mₚ)
    rw [isLocalize_at_prime_dim_eq_prime_depth_of_isCohenMacaulay p M Mₚ f]
    exact WithBot.coe_le_coe.mpr (isLocalization_at_prime_prime_depth_le_depth p M Mₚ f)

lemma isLocalize_at_prime_depth_eq_of_isCohenMacaulay [Small.{v} (R ⧸ p)] [M.IsCohenMacaulay] :
    p.depth M = IsLocalRing.depth Mₚ := sorry

end IsLocalization

--have some universe problem may have better statement using `IsLocalizedModule`
lemma localize_at_prime_isCohenMacaulay_of_isCohenMacaulay [IsLocalRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [Small.{v} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [M.IsCohenMacaulay] :
    (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).IsCohenMacaulay :=
  isLocalize_at_prime_isCohenMacaulay_of_isCohenMacaulay p M _
    (LocalizedModule.mkLinearMap p.primeCompl M)

--have some universe problem may have better statement using `IsLocalizedModule`
lemma localize_at_prime_depth_eq_of_isCohenMacaulay [IsLocalRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [Small.{v} R] [Small.{v} (R ⧸ (maximalIdeal R))] [Small.{v} (R ⧸ p)]
    (M : ModuleCat.{v} R) [M.IsCohenMacaulay] : p.depth M =
    IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)) :=
  isLocalize_at_prime_depth_eq_of_isCohenMacaulay p M _
    (LocalizedModule.mkLinearMap p.primeCompl M)

variable (R)

class IsCohenMacaulayLocalRing : Prop extends IsLocalRing R where
  depth_eq_dim : ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R)

class IsCohenMacaulayRing : Prop where
  CM_localize : ∀ p : Ideal R, ∀ (_ : p.IsPrime), IsCohenMacaulayLocalRing (Localization.AtPrime p)

lemma isCohenMacaulayRing_iff : IsCohenMacaulayRing R ↔
    ∀ m : Ideal R, ∀ (_ : m.IsMaximal), IsCohenMacaulayLocalRing (Localization.AtPrime m) := by
  sorry

--unmixedness theorem

--polynomial ring over CM ring is CM
