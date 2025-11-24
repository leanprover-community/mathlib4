/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.LocalProperties.Injective

/-!

# Relation of Injective Dimension with Localizations

-/

@[expose] public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory Limits

variable {R}

lemma injectiveDimension_eq_iSup_localizedModule_prime [Small.{v, u} R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) : injectiveDimension M =
    ⨆ (p : PrimeSpectrum R), injectiveDimension (M.localizedModule p.1.primeCompl) := by
  have aux (n : ℕ) : injectiveDimension M ≤ n ↔ ⨆ (p : PrimeSpectrum R), injectiveDimension
    (M.localizedModule p.1.primeCompl) ≤ n := by
    simp only [injectiveDimension_le_iff, iSup_le_iff]
    induction n generalizing M
    · simp only [HasInjectiveDimensionLE, zero_add, ← injective_iff_hasInjectiveDimensionLT_one]
      refine ⟨fun h p ↦ ?_, fun h ↦ ?_⟩
      · let _ : Small.{v} (Localization p.asIdeal.primeCompl) :=
          small_of_surjective Localization.mkHom_surjective
        let _ : Module.Injective R M := Module.injective_module_of_injective_object R M
        rw [← Module.injective_iff_injective_object]
        exact Module.injective_of_isLocalizedModule p.1.primeCompl
          (M.localizedModule_mkLinearMap p.1.primeCompl)
      · rw [← Module.injective_iff_injective_object]
        apply Module.injective_of_localization_maximal (fun p hp ↦ ?_)
        let _ : Small.{v} (Localization.AtPrime p) :=
          small_of_surjective Localization.mkHom_surjective
        have hp' : p.IsPrime := hp.isPrime
        have : Module.Injective (Localization.AtPrime p) (M.localizedModule p.primeCompl) := by
          rw [Module.injective_iff_injective_object]
          exact h ⟨p, hp'⟩
        rw [← Module.Baer.iff_injective] at this ⊢
        exact Module.Baer.of_equiv (LinearEquiv.extendScalarsOfIsLocalization p.primeCompl
          (Localization.AtPrime p) (IsLocalizedModule.linearEquiv p.primeCompl
          (M.localizedModule_mkLinearMap p.primeCompl)
          (LocalizedModule.mkLinearMap p.primeCompl M))) this
    · rename_i n ih
      have ei : EnoughInjectives (ModuleCat.{v} R) := inferInstance
      rcases ei.1 M with ⟨I, inj, f, monof⟩
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have S_exact : S.ShortExact := {
        exact := ShortComplex.exact_cokernel f
        epi_g := coequalizer.π_epi }
      have S_exact' : Function.Exact (ConcreteCategory.hom S.f) (ConcreteCategory.hom S.g) :=
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp S_exact.1
      have Sp_exact' (p : PrimeSpectrum R) := IsLocalizedModule.map_exact p.1.primeCompl
        (S.X₁.localizedModule_mkLinearMap p.1.primeCompl)
        (S.X₂.localizedModule_mkLinearMap p.1.primeCompl)
        (S.X₃.localizedModule_mkLinearMap p.1.primeCompl)
        _ _ S_exact'
      let Sp (p : PrimeSpectrum R) : ShortComplex (ModuleCat.{v} (Localization.AtPrime p.1)) := {
        f := ModuleCat.localizedModule_map p.1.primeCompl S.f
        g := ModuleCat.localizedModule_map p.1.primeCompl S.g
        zero := by
          ext x
          simp [ModuleCat.localizedModule_map, Function.Exact.apply_apply_eq_zero (Sp_exact' p)]}
      have Sp_exact (p : PrimeSpectrum R) : (Sp p).ShortExact := {
        exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (Sp_exact' p)
        mono_f := (ModuleCat.mono_iff_injective _).mpr
          (IsLocalizedModule.map_injective p.1.primeCompl
            (S.X₁.localizedModule_mkLinearMap p.1.primeCompl)
            (S.X₂.localizedModule_mkLinearMap p.1.primeCompl)
            _ (((ModuleCat.mono_iff_injective _).mp S_exact.2)))
        epi_g := (ModuleCat.epi_iff_surjective _).mpr
          (IsLocalizedModule.map_surjective p.1.primeCompl
            (S.X₂.localizedModule_mkLinearMap p.1.primeCompl)
            (S.X₃.localizedModule_mkLinearMap p.1.primeCompl)
            _ ((ModuleCat.epi_iff_surjective _).mp S_exact.3)) }
      have ih' := ih S.X₃
      simp only [HasInjectiveDimensionLE] at ih' ⊢
      rw [← S_exact.hasInjectiveDimensionLT_X₃_iff n inj, ih']
      have injp (p : PrimeSpectrum R) : Injective (Sp p).X₂ := by
        rw [← Module.injective_iff_injective_object]
        have : Module.Injective R I := Module.injective_module_of_injective_object R I
        let _ : Small.{v} (Localization p.1.primeCompl) :=
          small_of_surjective Localization.mkHom_surjective
        exact Module.injective_of_isLocalizedModule p.1.primeCompl
          (I.localizedModule_mkLinearMap p.1.primeCompl)
      exact (forall_congr' (fun p ↦ (Sp_exact p).hasInjectiveDimensionLT_X₃_iff n (injp p)))
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  by_cases eqbot : N = ⊥
  · simp only [eqbot, le_bot_iff, injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
      iSup_eq_bot, ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]
    refine ⟨fun h p ↦ LocalizedModule.instSubsingleton _, fun h ↦ ?_⟩
    apply Module.subsingleton_of_localization_maximal (R := R)
      (fun p ↦ LocalizedModule p.primeCompl M) (fun p ↦ LocalizedModule.mkLinearMap p.primeCompl M)
    intro p hp
    exact h ⟨p, hp.isPrime⟩
  · by_cases eqtop : N.unbot eqbot = ⊤
    · have : N = ⊤ := (WithBot.coe_unbot _ eqbot).symm.trans (WithBot.coe_inj.mpr eqtop)
      simp [this]
    · let n := (N.unbot eqbot).toNat
      have : N = n := (WithBot.coe_unbot _ eqbot).symm.trans
        (WithBot.coe_inj.mpr (ENat.coe_toNat eqtop).symm)
      simpa only [this] using aux n

lemma injectiveDimension_eq_iSup_localizedModule_maximal [Small.{v, u} R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) : injectiveDimension M =
    ⨆ (p : MaximalSpectrum R), injectiveDimension (M.localizedModule p.1.primeCompl) := by
  have aux (n : ℕ) : injectiveDimension M ≤ n ↔ ⨆ (p : MaximalSpectrum R), injectiveDimension
    (M.localizedModule p.1.primeCompl) ≤ n := by
    simp only [injectiveDimension_le_iff, iSup_le_iff]
    induction n generalizing M
    · simp only [HasInjectiveDimensionLE, zero_add, ← injective_iff_hasInjectiveDimensionLT_one]
      refine ⟨fun h p ↦ ?_, fun h ↦ ?_⟩
      · let _ : Small.{v} (Localization p.asIdeal.primeCompl) :=
          small_of_surjective Localization.mkHom_surjective
        let _ : Module.Injective R M := Module.injective_module_of_injective_object R M
        rw [← Module.injective_iff_injective_object]
        exact Module.injective_of_isLocalizedModule p.1.primeCompl
          (M.localizedModule_mkLinearMap p.1.primeCompl)
      · rw [← Module.injective_iff_injective_object]
        apply Module.injective_of_localization_maximal (fun p hp ↦ ?_)
        let _ : Small.{v} (Localization.AtPrime p) :=
          small_of_surjective Localization.mkHom_surjective
        have : Module.Injective (Localization.AtPrime p) (M.localizedModule p.primeCompl) := by
          rw [Module.injective_iff_injective_object]
          exact h ⟨p, hp⟩
        rw [← Module.Baer.iff_injective] at this ⊢
        exact Module.Baer.of_equiv (LinearEquiv.extendScalarsOfIsLocalization p.primeCompl
          (Localization.AtPrime p) (IsLocalizedModule.linearEquiv p.primeCompl
          (M.localizedModule_mkLinearMap p.primeCompl)
          (LocalizedModule.mkLinearMap p.primeCompl M))) this
    · rename_i n ih
      have ei : EnoughInjectives (ModuleCat.{v} R) := inferInstance
      rcases ei.1 M with ⟨I, inj, f, monof⟩
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have S_exact : S.ShortExact := {
        exact := ShortComplex.exact_cokernel f
        epi_g := coequalizer.π_epi }
      have S_exact' : Function.Exact (ConcreteCategory.hom S.f) (ConcreteCategory.hom S.g) :=
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp S_exact.1
      have Sp_exact' (p : MaximalSpectrum R) := IsLocalizedModule.map_exact p.1.primeCompl
        (S.X₁.localizedModule_mkLinearMap p.1.primeCompl)
        (S.X₂.localizedModule_mkLinearMap p.1.primeCompl)
        (S.X₃.localizedModule_mkLinearMap p.1.primeCompl)
        _ _ S_exact'
      let Sp (p : MaximalSpectrum R) : ShortComplex (ModuleCat.{v} (Localization.AtPrime p.1)) := {
        f := ModuleCat.localizedModule_map p.1.primeCompl S.f
        g := ModuleCat.localizedModule_map p.1.primeCompl S.g
        zero := by
          ext x
          simp [ModuleCat.localizedModule_map, Function.Exact.apply_apply_eq_zero (Sp_exact' p)]}
      have Sp_exact (p : MaximalSpectrum R) : (Sp p).ShortExact := {
        exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (Sp_exact' p)
        mono_f := (ModuleCat.mono_iff_injective _).mpr
          (IsLocalizedModule.map_injective p.1.primeCompl
            (S.X₁.localizedModule_mkLinearMap p.1.primeCompl)
            (S.X₂.localizedModule_mkLinearMap p.1.primeCompl)
            _ (((ModuleCat.mono_iff_injective _).mp S_exact.2)))
        epi_g := (ModuleCat.epi_iff_surjective _).mpr
          (IsLocalizedModule.map_surjective p.1.primeCompl
            (S.X₂.localizedModule_mkLinearMap p.1.primeCompl)
            (S.X₃.localizedModule_mkLinearMap p.1.primeCompl)
            _ ((ModuleCat.epi_iff_surjective _).mp S_exact.3)) }
      have ih' := ih S.X₃
      simp only [HasInjectiveDimensionLE] at ih' ⊢
      rw [← S_exact.hasInjectiveDimensionLT_X₃_iff n inj, ih']
      have injp (p : MaximalSpectrum R) : Injective (Sp p).X₂ := by
        rw [← Module.injective_iff_injective_object]
        have : Module.Injective R I := Module.injective_module_of_injective_object R I
        let _ : Small.{v} (Localization p.1.primeCompl) :=
          small_of_surjective Localization.mkHom_surjective
        exact Module.injective_of_isLocalizedModule p.1.primeCompl
          (I.localizedModule_mkLinearMap p.1.primeCompl)
      exact (forall_congr' (fun p ↦ (Sp_exact p).hasInjectiveDimensionLT_X₃_iff n (injp p)))
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  by_cases eqbot : N = ⊥
  · simp only [eqbot, le_bot_iff, injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
      iSup_eq_bot, ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]
    refine ⟨fun h p ↦ LocalizedModule.instSubsingleton _, fun h ↦ ?_⟩
    apply Module.subsingleton_of_localization_maximal (R := R)
      (fun p ↦ LocalizedModule p.primeCompl M) (fun p ↦ LocalizedModule.mkLinearMap p.primeCompl M)
    intro p hp
    exact h ⟨p, hp⟩
  · by_cases eqtop : N.unbot eqbot = ⊤
    · have : N = ⊤ := (WithBot.coe_unbot _ eqbot).symm.trans (WithBot.coe_inj.mpr eqtop)
      simp [this]
    · let n := (N.unbot eqbot).toNat
      have : N = n := (WithBot.coe_unbot _ eqbot).symm.trans
        (WithBot.coe_inj.mpr (ENat.coe_toNat eqtop).symm)
      simpa only [this] using aux n

open Limits in
lemma injectiveDimension_le_injectiveDimension_of_isLocalizedModule [Small.{v, u} R]
    [IsNoetherianRing R] (S : Submonoid R) (M : ModuleCat.{v} R) :
    injectiveDimension (M.localizedModule S) ≤ injectiveDimension M := by
  have aux (n : ℕ) : injectiveDimension M ≤ n → injectiveDimension (M.localizedModule S) ≤ n := by
    simp only [injectiveDimension_le_iff]
    let _ : Small.{v, u} (Localization S) :=
      small_of_surjective Localization.mkHom_surjective
    induction n generalizing M
    · simp only [HasInjectiveDimensionLE, zero_add, ← injective_iff_hasInjectiveDimensionLT_one]
      rw [← Module.injective_iff_injective_object, ← Module.injective_iff_injective_object]
      intro _
      exact Module.injective_of_isLocalizedModule S (M.localizedModule_mkLinearMap S)
    · rename_i n ih
      have ei : EnoughInjectives (ModuleCat.{v} R) := inferInstance
      rcases ei.1 M with ⟨I, inj, f, monof⟩
      let T := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have T_exact : T.ShortExact := {
        exact := ShortComplex.exact_cokernel f
        epi_g := coequalizer.π_epi }
      have T_exact' : Function.Exact (ConcreteCategory.hom T.f) (ConcreteCategory.hom T.g) :=
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp T_exact.1
      have TS_exact' := IsLocalizedModule.map_exact S
        (T.X₁.localizedModule_mkLinearMap S)
        (T.X₂.localizedModule_mkLinearMap S)
        (T.X₃.localizedModule_mkLinearMap S)
        _ _ T_exact'
      let TS : ShortComplex (ModuleCat.{v} (Localization S)) := {
        f := ModuleCat.localizedModule_map S T.f
        g := ModuleCat.localizedModule_map S T.g
        zero := by
          ext x
          simp [ModuleCat.localizedModule_map, Function.Exact.apply_apply_eq_zero TS_exact']}
      have TS_exact : TS.ShortExact := {
        exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr TS_exact'
        mono_f := (ModuleCat.mono_iff_injective _).mpr (IsLocalizedModule.map_injective S
          (T.X₁.localizedModule_mkLinearMap S) (T.X₂.localizedModule_mkLinearMap S)
            _ ((ModuleCat.mono_iff_injective T.f).mp T_exact.2))
        epi_g := (ModuleCat.epi_iff_surjective _).mpr (IsLocalizedModule.map_surjective S
          (T.X₂.localizedModule_mkLinearMap S) (T.X₃.localizedModule_mkLinearMap S)
            _ ((ModuleCat.epi_iff_surjective T.g).mp T_exact.3)) }
      let _ : Injective TS.X₂ := by
        rw [← Module.injective_iff_injective_object]
        have : Module.Injective R I := Module.injective_module_of_injective_object R I
        let _ : Small.{v} (Localization S) := small_of_surjective Localization.mkHom_surjective
        exact Module.injective_of_isLocalizedModule S (I.localizedModule_mkLinearMap S)
      simp only [HasInjectiveDimensionLE]
      rw [← T_exact.hasInjectiveDimensionLT_X₃_iff n ‹_›,
        ← TS_exact.hasInjectiveDimensionLT_X₃_iff n ‹_›]
      exact ih T.X₃
  refine le_of_forall_ge (fun N ↦ ?_)
  by_cases eqbot : N = ⊥
  · simp only [eqbot, le_bot_iff, injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
      ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]
    intro _
    apply LocalizedModule.instSubsingleton _
  · by_cases eqtop : N.unbot eqbot = ⊤
    · have : N = ⊤ := (WithBot.coe_unbot _ eqbot).symm.trans (WithBot.coe_inj.mpr eqtop)
      simp [this]
    · let n := (N.unbot eqbot).toNat
      have : N = n := (WithBot.coe_unbot _ eqbot).symm.trans
        (WithBot.coe_inj.mpr (ENat.coe_toNat eqtop).symm)
      simpa only [this] using aux n
