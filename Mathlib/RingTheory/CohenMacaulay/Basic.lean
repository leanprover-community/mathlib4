/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
-/
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Regular.Ischebeck

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
    [M.IsCohenMacaulay] [Module.Finite R M] [Nontrivial M]
    (mem : p ∈ associatedPrimes R M) :
    IsLocalRing.depth M = (ringKrullDim (R ⧸ p)).unbot
    (quotient_prime_ringKrullDim_ne_bot mem.1) := by
  apply le_antisymm (depth_le_ringKrullDim_associatedPrime M p mem)
  rw [← M.depth_eq_supportDim_unbot_of_cohenMacaulay]
  rw [← WithBot.coe_le_coe, WithBot.coe_unbot, WithBot.coe_unbot,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective
    (le_of_eq_of_le Submodule.annihilator_top.symm (AssociatePrimes.mem_iff.mp mem).annihilator_le))

lemma associated_prime_minimal_of_isCohenMacaulay (M : ModuleCat.{v} R)
    [M.IsCohenMacaulay] [Module.Finite R M] [Nontrivial M]
    (mem : p ∈ associatedPrimes R M) : p ∈ (Module.annihilator R M).minimalPrimes := by
  have eq := Eq.trans M.depth_eq_supportDim_unbot_of_cohenMacaulay
    (depth_eq_dim_quotient_associated_prime_of_isCohenMacaulay p M mem)
  rw [← WithBot.coe_inj, WithBot.coe_unbot, WithBot.coe_unbot, ringKrullDim_quotient,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator, ringKrullDim_quotient] at eq
  have : p.IsPrime := mem.1
  have ann_le : Module.annihilator R M ≤ p := (le_of_eq_of_le Submodule.annihilator_top.symm
    (AssociatePrimes.mem_iff.mp mem).annihilator_le)
  rcases Ideal.exists_minimalPrimes_le ann_le with ⟨p', hp', le⟩
  rcases lt_or_eq_of_le le with lt|eq
  · classical
    let f : WithBot (PrimeSpectrum.zeroLocus (p : Set R)) →
        (PrimeSpectrum.zeroLocus ((Module.annihilator R M) : Set R)) := fun I ↦ by
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
    have : Nonempty (PrimeSpectrum.zeroLocus (p : Set R)) := Nonempty.intro ⟨⟨p, mem.1⟩, le_refl p⟩
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

lemma associated_prime_eq_minimalPrimes_isCohenMacaulay (M : ModuleCat.{v} R)
    [M.IsCohenMacaulay] [Module.Finite R M] [Nontrivial M] :
    associatedPrimes R M = (Module.annihilator R M).minimalPrimes :=
  le_antisymm (fun p hp ↦ associated_prime_minimal_of_isCohenMacaulay p M hp)
    (Module.associatedPrimes.minimalPrimes_annihilator_mem_associatedPrimes R M)

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
        repeat simpa using by rfl
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
    rw [← Module.supportDim_quotSMulTop_succ_eq_supportDim reg mem,
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
abbrev quotSMulTop_isLocalizedModule_map (x : R) (M : Type*) [AddCommGroup M] [Module R M]
    (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) :
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
omit [IsLocalRing R] [IsNoetherianRing R] [Small.{v, u} R] in
lemma isLocalizedModule_quotSMulTop_isLocalizedModule_map (x : R)
    (M : Type*) [AddCommGroup M] [Module R M] (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f] :
    IsLocalizedModule.AtPrime p (quotSMulTop_isLocalizedModule_map Rₚ x M Mₚ f) where
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

variable [Small.{v'} Rₚ] [IsNoetherianRing Rₚ]
  (M : ModuleCat.{v} R) (Mₚ : ModuleCat.{v'} Rₚ) [Module R Mₚ] [IsScalarTower R Rₚ Mₚ]
  (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]

include p f

lemma isLocalization_at_prime_prime_depth_le_depth [IsLocalRing Rₚ] [Module.Finite R M]
    [ntr : Nontrivial Mₚ] : p.depth M ≤ IsLocalRing.depth Mₚ := by
  have : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule p.primeCompl f
  have : Nontrivial M := by
    by_contra h
    absurd not_subsingleton_iff_nontrivial.mpr ntr
    rw [IsLocalizedModule.subsingleton_iff_ker_eq_top p.primeCompl f]
    have := (Submodule.subsingleton_iff R).mpr (not_nontrivial_iff_subsingleton.mp h)
    apply Subsingleton.elim
  simp only [IsLocalRing.depth_eq_sSup_length_regular, Ideal.depth]
  have : Module.Finite R (Shrink.{v, u} (R ⧸ p)) :=
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
  refine ⟨rs.map (algebraMap R Rₚ), reg.isRegular_of_isLocalizedModule_of_mem_prime p Rₚ f mem,
    fun _ hr ↦ ?_, by simpa using len⟩
  rcases List.mem_map.mp hr with ⟨r, hr, eq⟩
  simpa only [← eq, IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p] using mem r hr

omit [Small.{v', u'} Rₚ] in
lemma isLocalize_at_prime_dim_eq_prime_depth_of_isCohenMacaulay
    [Module.Finite R M] [M.IsCohenMacaulay] [ntr : Nontrivial Mₚ] :
    Module.supportDim Rₚ Mₚ = p.depth M := by
  have : IsLocalRing Rₚ := IsLocalization.AtPrime.isLocalRing Rₚ p
  have : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule p.primeCompl f
  have : Nontrivial M := by
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
      let P : PrimeSpectrum R := ⟨p, ‹_›⟩
      have ntr : Nontrivial (LocalizedModule P.asIdeal.primeCompl M) :=
        (IsLocalizedModule.linearEquiv p.primeCompl
          (LocalizedModule.mkLinearMap p.primeCompl M) f).nontrivial
      have mem_supp := Module.mem_support_iff.mpr ntr
      simp only [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus,
        SetLike.coe_subset_coe, P] at mem_supp
      have min := associated_prime_minimal_of_isCohenMacaulay p' M ass
      convert min
      simp only [Ideal.minimalPrimes, Set.mem_setOf_eq] at min
      exact min.eq_of_le ⟨‹_›, mem_supp⟩ (le.trans hp')
    have : Module.support Rₚ Mₚ = {closedPoint Rₚ} := by
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
      · simpa using IsLocalRing.closedPoint_mem_support Rₚ Mₚ
    have : Unique (Module.support Rₚ Mₚ) := by simpa [this] using Set.uniqueSingleton _
    exact Order.krullDim_eq_zero_of_unique
  · have : Subsingleton ((ModuleCat.of R (Shrink.{v} (R ⧸ p))) →ₗ[R] M) := by
      by_contra ntr
      rw [not_subsingleton_iff_nontrivial, ← moduleDepth_eq_zero_of_hom_nontrivial] at ntr
      simp [Ideal.depth, ntr] at hn
    rcases IsSMulRegular.subsingleton_linearMap_iff.mp
      (((Shrink.linearEquiv (R ⧸ p) R).congrLeft M R).symm.subsingleton) with ⟨a, mem, reg⟩
    rw [Ideal.annihilator_quotient] at mem
    let M' := ModuleCat.of R (QuotSMulTop a M)
    have : Nontrivial M' := quotSMulTop_nontrivial (le_maximalIdeal_of_isPrime p mem) M
    have : M'.IsCohenMacaulay := (quotSMulTop_isCohenMacaulay_iff_isCohenMacaulay M a reg
      (le_maximalIdeal_of_isPrime p mem)).mp ‹_›
    have netop' : p.depth M' ≠ ⊤ :=
      ne_top_of_le_ne_top (depth_ne_top M') (ideal_depth_le_depth p Ideal.IsPrime.ne_top' M')
    have depth_eq : p.depth M'= n := by
      simp only [Nat.cast_add, ← p.depth_quotSMulTop_succ_eq_moduleDepth M a reg mem] at hn
      exact (ENat.add_right_cancel_iff _ _ 1 (ENat.coe_ne_top 1)).mp hn.symm
    let M'ₚ := ModuleCat.of Rₚ (QuotSMulTop ((algebraMap R Rₚ) a) Mₚ)
    have map_mem : (algebraMap R Rₚ) a ∈ maximalIdeal Rₚ :=
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p a _).mpr mem)
    have : Nontrivial M'ₚ := quotSMulTop_nontrivial map_mem Mₚ
    have eq_succ : Module.supportDim Rₚ M'ₚ + 1 = Module.supportDim Rₚ Mₚ :=
      Module.supportDim_quotSMulTop_succ_eq_supportDim
        (reg.of_isLocalizedModule p.primeCompl Rₚ f) map_mem
    have := isLocalizedModule_quotSMulTop_isLocalizedModule_map p Rₚ a M Mₚ f
    simp [← eq_succ, ← hn, depth_eq, ih M' M'ₚ (quotSMulTop_isLocalizedModule_map Rₚ a M Mₚ f)
      inferInstance ‹_› netop' depth_eq.symm]

lemma isLocalize_at_prime_isCohenMacaulay_of_isCohenMacaulay [IsLocalRing Rₚ] [Module.Finite R M]
    [M.IsCohenMacaulay] : Mₚ.IsCohenMacaulay := by
  have : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule p.primeCompl f
  simp only [ModuleCat.isCohenMacaulay_iff]
  by_cases ntr : Subsingleton Mₚ
  · simp [ntr]
  · simp only [ntr, false_or]
    have ntr2 : Nontrivial Mₚ := not_subsingleton_iff_nontrivial.mp ntr
    apply le_antisymm _ (depth_le_supportDim Mₚ)
    rw [isLocalize_at_prime_dim_eq_prime_depth_of_isCohenMacaulay p M Mₚ f]
    exact WithBot.coe_le_coe.mpr (isLocalization_at_prime_prime_depth_le_depth p M Mₚ f)

lemma isLocalize_at_prime_depth_eq_of_isCohenMacaulay [IsLocalRing Rₚ] [Module.Finite R M]
    [Nontrivial Mₚ] [M.IsCohenMacaulay] :
    p.depth M = IsLocalRing.depth Mₚ := by
  have : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule p.primeCompl f
  apply le_antisymm (isLocalization_at_prime_prime_depth_le_depth p M Mₚ f)
  rw [← WithBot.coe_le_coe, ← isLocalize_at_prime_dim_eq_prime_depth_of_isCohenMacaulay p M Mₚ f]
  exact (depth_le_supportDim Mₚ)

end IsLocalization

-- have some universe problem may have better statement using `IsLocalizedModule`
lemma localize_at_prime_isCohenMacaulay_of_isCohenMacaulay [IsLocalRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [Small.{v} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [M.IsCohenMacaulay] :
    (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).IsCohenMacaulay :=
  isLocalize_at_prime_isCohenMacaulay_of_isCohenMacaulay p M _
    (LocalizedModule.mkLinearMap p.primeCompl M)

-- have some universe problem may have better statement using `IsLocalizedModule`
lemma localize_at_prime_depth_eq_of_isCohenMacaulay [IsLocalRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [Small.{v} R] (M : ModuleCat.{v} R) [Module.Finite R M]
    [M.IsCohenMacaulay] [Nontrivial (LocalizedModule.AtPrime p M)] : p.depth M =
    IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule.AtPrime p M)) :=
  isLocalize_at_prime_depth_eq_of_isCohenMacaulay p M _
    (LocalizedModule.mkLinearMap p.primeCompl M)

variable (R)

class IsCohenMacaulayLocalRing : Prop extends IsLocalRing R where
  depth_eq_dim : ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R)

lemma isCohenMacaulayLocalRing_def [IsLocalRing R] : IsCohenMacaulayLocalRing R ↔
    ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R) :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma isCohenMacaulayLocalRing_of_ringKrullDim_le_depth [IsLocalRing R] [IsNoetherianRing R]
    (le : ringKrullDim R ≤ IsLocalRing.depth (ModuleCat.of R R)) : IsCohenMacaulayLocalRing R :=
  (isCohenMacaulayLocalRing_def _).mpr (le_antisymm le (depth_le_ringKrullDim _))

--may be able to remove noetherian condition here by modify `IsLocalRing.depth_eq_of_ringEquiv`
lemma isCohenMacaulayLocalRing_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R']
    [IsNoetherianRing R] (e : R ≃+* R') [CM : IsCohenMacaulayLocalRing R] :
    IsCohenMacaulayLocalRing R' := by
  have := e.isLocalRing
  have : IsNoetherianRing R' := isNoetherianRing_of_ringEquiv R e
  simp only [isCohenMacaulayLocalRing_def] at CM ⊢
  rw [← ringKrullDim_eq_of_ringEquiv e, ← IsLocalRing.depth_eq_of_ringEquiv e, CM]

lemma isCohenMacaulayLocalRing_iff [IsLocalRing R] :
    IsCohenMacaulayLocalRing R ↔ (ModuleCat.of R R).IsCohenMacaulay := by
  simp [isCohenMacaulayLocalRing_def, isCohenMacaulay_iff,
    not_subsingleton_iff_nontrivial.mpr inferInstance, Module.supportDim_self_eq_ringKrullDim]

instance [IsCohenMacaulayLocalRing R] : (ModuleCat.of R R).IsCohenMacaulay :=
  (isCohenMacaulayLocalRing_iff R).mp ‹_›

lemma isCohenMacaulayLocalRing_localization_atPrime [IsCohenMacaulayLocalRing R]
    [IsNoetherianRing R](p : Ideal R) [p.IsPrime]
    (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] :
    IsCohenMacaulayLocalRing Rₚ := by
  have := IsLocalization.AtPrime.isLocalRing Rₚ p
  have := IsLocalization.isNoetherianRing p.primeCompl Rₚ ‹_›
  rw [isCohenMacaulayLocalRing_iff]
  exact isLocalize_at_prime_isCohenMacaulay_of_isCohenMacaulay p (ModuleCat.of R R)
    (ModuleCat.of Rₚ Rₚ) (Algebra.linearMap R Rₚ)

lemma associatedPrimes_self_eq_minimalPrimes [IsCohenMacaulayLocalRing R] [IsNoetherianRing R] :
    associatedPrimes R R = minimalPrimes R := by
  have : Module.annihilator R R = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  simp [associated_prime_eq_minimalPrimes_isCohenMacaulay (ModuleCat.of R R), this, minimalPrimes]

class IsCohenMacaulayRing : Prop where
  CM_localize : ∀ p : Ideal R, ∀ (_ : p.IsPrime), IsCohenMacaulayLocalRing (Localization.AtPrime p)

lemma isCohenMacaulayRing_def : IsCohenMacaulayRing R ↔
    ∀ p : Ideal R, ∀ (_ : p.IsPrime), IsCohenMacaulayLocalRing (Localization.AtPrime p) :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma isCohenMacaulayRing_def' : IsCohenMacaulayRing R ↔
  ∀ p : PrimeSpectrum R, IsCohenMacaulayLocalRing (Localization.AtPrime p.1) :=
  ⟨fun ⟨h⟩ ↦ fun p ↦ h p.1 p.2, fun h ↦ ⟨fun p hp ↦ h ⟨p, hp⟩⟩⟩

lemma isCohenMacaulayRing_iff [IsNoetherianRing R] : IsCohenMacaulayRing R ↔
    ∀ m : Ideal R, ∀ (_ : m.IsMaximal), IsCohenMacaulayLocalRing (Localization.AtPrime m) := by
  refine ⟨fun ⟨h⟩ ↦ fun m hm ↦ h m (Ideal.IsMaximal.isPrime hm), fun h ↦ ⟨fun p hp ↦  ?_⟩⟩
  rcases Ideal.exists_le_maximal p (Ideal.IsPrime.ne_top hp) with ⟨m, hm, le⟩
  have := (isCohenMacaulayLocalRing_iff _).mp (h m hm)
  let Rₘ := Localization.AtPrime m
  let Rₚ := Localization.AtPrime p
  have disj := (Set.disjoint_compl_left_iff_subset.mpr le)
  have : (p.map (algebraMap R Rₘ)).IsPrime := by
    simpa [IsLocalization.isPrime_iff_isPrime_disjoint m.primeCompl Rₘ, hp,
      IsLocalization.comap_map_of_isPrime_disjoint m.primeCompl Rₘ p hp disj] using disj
  have le' : m.primeCompl ≤ p.primeCompl := by simpa [Ideal.primeCompl] using le
  let : Algebra Rₘ Rₚ := IsLocalization.localizationAlgebraOfSubmonoidLe Rₘ Rₚ _ _ le'
  have := IsLocalization.localization_isScalarTower_of_submonoid_le Rₘ Rₚ _ _ le'
  have : IsLocalization.AtPrime (Localization.AtPrime (Ideal.map (algebraMap R Rₘ) p)) p := by
    convert IsLocalization.isLocalization_atPrime_localization_atPrime m.primeCompl
      (p.map (algebraMap R Rₘ))
    rw [IsLocalization.comap_map_of_isPrime_disjoint m.primeCompl Rₘ p hp disj]
  let e' := (IsLocalization.algEquiv p.primeCompl Rₚ
      (Localization.AtPrime (Ideal.map (algebraMap R Rₘ) p)))
  let e : Rₚ ≃ₐ[Rₘ] Localization.AtPrime (Ideal.map (algebraMap R Rₘ) p) :=
    AlgEquiv.ofLinearEquiv (LinearEquiv.extendScalarsOfIsLocalization m.primeCompl Rₘ e')
      (map_one e') (map_mul e')
  have : IsLocalization.AtPrime Rₚ (Ideal.map (algebraMap R Rₘ) p) :=
    IsLocalization.isLocalization_of_algEquiv (Ideal.map (algebraMap R Rₘ) p).primeCompl e.symm
  exact (isCohenMacaulayLocalRing_iff _).mpr
    (isLocalize_at_prime_isCohenMacaulay_of_isCohenMacaulay (p.map (algebraMap R Rₘ))
    (ModuleCat.of Rₘ Rₘ) (ModuleCat.of Rₚ Rₚ) (Algebra.linearMap Rₘ Rₚ))

lemma isCohenMacaulayRing_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R']
    [IsNoetherianRing R] (e : R ≃+* R') [CM : IsCohenMacaulayRing R] :
    IsCohenMacaulayRing R' := by
  apply (isCohenMacaulayRing_def R').mpr (fun p' hp' ↦ ?_)
  let p := p'.comap e
  have : Submonoid.map e.toMonoidHom p.primeCompl = p'.primeCompl := by
    ext x
    have : (∃ y, e y ∉ p' ∧ e y = x) ↔ x ∉ p' := ⟨fun ⟨y, hy, eq⟩ ↦ by simpa [← eq],
      fun h ↦ ⟨e.symm x, by simpa, RingEquiv.apply_symm_apply e x⟩⟩
    simpa only [Ideal.primeCompl, p]
  let _ := (isCohenMacaulayRing_def R).mp ‹_› p (Ideal.comap_isPrime e p')
  exact isCohenMacaulayLocalRing_of_ringEquiv
    (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p) (Localization.AtPrime p') e this)

open Ideal

open Pointwise in
lemma quotient_regular_smul_top_isCohenMacaulay_iff_isCohenMacaulay [IsLocalRing R]
    [IsNoetherianRing R] (x : R) (reg : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) :
    IsCohenMacaulayLocalRing R ↔ IsCohenMacaulayLocalRing (R ⧸ x • (⊤ : Ideal R)) := by
  have : IsLocalRing (R ⧸ x • (⊤ : Ideal R)) :=
    have : Nontrivial (R ⧸ x • (⊤ : Ideal R)) :=
      Quotient.nontrivial (by simpa [← Submodule.ideal_span_singleton_smul])
    have : IsLocalHom (Ideal.Quotient.mk (x • (⊤ : Ideal R))) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk (x • (⊤ : Ideal R))) Ideal.Quotient.mk_surjective
  simp only [isCohenMacaulayLocalRing_def,
    ← ringKrullDim_quotSMulTop_succ_eq_ringKrullDim reg mem,
    ← depth_quotient_regular_succ_eq_depth x reg mem, WithBot.coe_add, WithBot.coe_one]
  exact withBotENat_add_coe_cancel _ _ 1

lemma quotient_span_regular_isCohenMacaulay_iff_isCohenMacaulay [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (reg : IsSMulRegular R x) (mem : x ∈ maximalIdeal R) :
    IsCohenMacaulayLocalRing R ↔ IsCohenMacaulayLocalRing (R ⧸ Ideal.span {x}) := by
  have : IsLocalRing (R ⧸ Ideal.span {x}) :=
    have : Nontrivial (R ⧸ Ideal.span {x}) :=
      Quotient.nontrivial (by simpa [← Submodule.ideal_span_singleton_smul])
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  simp only [isCohenMacaulayLocalRing_def,
    ← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim reg mem,
    ← depth_quotient_span_regular_succ_eq_depth x reg mem, WithBot.coe_add, WithBot.coe_one]
  exact withBotENat_add_coe_cancel _ _ 1

lemma quotient_regular_sequence_isCohenMacaulay_iff_isCohenMacaulay [IsLocalRing R]
    [IsNoetherianRing R] (rs : List R) (reg : IsWeaklyRegular R rs)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) : IsCohenMacaulayLocalRing R ↔
    IsCohenMacaulayLocalRing (R ⧸ Ideal.ofList rs) := by
  have : IsLocalRing (R ⧸ Ideal.ofList rs) :=
    have : Nontrivial (R ⧸ Ideal.ofList rs) :=
      Submodule.Quotient.nontrivial_of_lt_top _
        (lt_of_le_of_lt (span_le.mpr mem) (Ne.lt_top IsPrime.ne_top'))
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.ofList rs)) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have reg' : IsRegular R rs :=
    ⟨reg, by simpa using ((span_le.mpr mem).trans_lt IsPrime.ne_top'.lt_top).ne_top.symm⟩
  simp only [isCohenMacaulayLocalRing_def,
    ← ringKrullDim_regular_sequence_add_length_eq_ringKrullDim rs reg',
    ← depth_quotient_regular_sequence_add_length_eq_depth rs reg mem, WithBot.coe_add]
  exact withBotENat_add_coe_cancel _ _ rs.length
