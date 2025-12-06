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
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.LocalProperties.Injective

/-!

# Relation of Injective Dimension with Localizations

-/

@[expose] public section

universe v u

variable {R : Type u} [CommRing R]

open CategoryTheory Limits

instance [Small.{v} R] [IsNoetherianRing R] (S : Submonoid R) :
    (ModuleCat.localizedModule_functor.{v} S).PreservesInjectiveObjects where
  injective_obj X {inj} := by
    let _ : Small.{v, u} (Localization S) := small_of_surjective Localization.mkHom_surjective
    rw [← Module.injective_iff_injective_object] at inj ⊢
    simpa [ModuleCat.localizedModule_functor] using
      Module.injective_of_isLocalizedModule S (X.localizedModuleMkLinearMap S)

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
          (M.localizedModuleMkLinearMap p.1.primeCompl)
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
          (M.localizedModuleMkLinearMap p.primeCompl)
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
        (S.X₁.localizedModuleMkLinearMap p.1.primeCompl)
        (S.X₂.localizedModuleMkLinearMap p.1.primeCompl)
        (S.X₃.localizedModuleMkLinearMap p.1.primeCompl)
        _ _ S_exact'
      let Sp (p : PrimeSpectrum R) := S.map (ModuleCat.localizedModule_functor p.1.primeCompl)
      have Sp_exact (p : PrimeSpectrum R) : (Sp p).ShortExact :=
        S_exact.map_of_exact (ModuleCat.localizedModule_functor p.asIdeal.primeCompl)
      have ih' := ih S.X₃
      simp only [HasInjectiveDimensionLE] at ih' ⊢
      rw [← S_exact.hasInjectiveDimensionLT_X₃_iff n inj, ih']
      have injp (p : PrimeSpectrum R) : Injective (Sp p).X₂ :=
        (ModuleCat.localizedModule_functor.{v} p.1.primeCompl).injective_obj _
      exact (forall_congr' (fun p ↦ (Sp_exact p).hasInjectiveDimensionLT_X₃_iff n (injp p)))
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
      iSup_eq_bot, ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]
    refine ⟨fun h p ↦ LocalizedModule.instSubsingleton _, fun h ↦ ?_⟩
    apply Module.subsingleton_of_localization_maximal (R := R)
      (fun p ↦ LocalizedModule p.primeCompl M) (fun p ↦ LocalizedModule.mkLinearMap p.primeCompl M)
    intro p hp
    exact h ⟨p, hp.isPrime⟩
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n

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
          (M.localizedModuleMkLinearMap p.1.primeCompl)
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
          (M.localizedModuleMkLinearMap p.primeCompl)
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
        (S.X₁.localizedModuleMkLinearMap p.1.primeCompl)
        (S.X₂.localizedModuleMkLinearMap p.1.primeCompl)
        (S.X₃.localizedModuleMkLinearMap p.1.primeCompl)
        _ _ S_exact'
      let Sp (p : MaximalSpectrum R) := S.map (ModuleCat.localizedModule_functor p.1.primeCompl)
      have Sp_exact (p : MaximalSpectrum R) : (Sp p).ShortExact :=
        S_exact.map_of_exact (ModuleCat.localizedModule_functor p.asIdeal.primeCompl)
      have ih' := ih S.X₃
      simp only [HasInjectiveDimensionLE] at ih' ⊢
      rw [← S_exact.hasInjectiveDimensionLT_X₃_iff n inj, ih']
      have injp (p : MaximalSpectrum R) : Injective (Sp p).X₂ :=
        (ModuleCat.localizedModule_functor.{v} p.1.primeCompl).injective_obj _
      exact (forall_congr' (fun p ↦ (Sp_exact p).hasInjectiveDimensionLT_X₃_iff n (injp p)))
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
      iSup_eq_bot, ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]
    refine ⟨fun h p ↦ LocalizedModule.instSubsingleton _, fun h ↦ ?_⟩
    apply Module.subsingleton_of_localization_maximal (R := R)
      (fun p ↦ LocalizedModule p.primeCompl M) (fun p ↦ LocalizedModule.mkLinearMap p.primeCompl M)
    intro p hp
    exact h ⟨p, hp⟩
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n

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
      exact Module.injective_of_isLocalizedModule S (M.localizedModuleMkLinearMap S)
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
        (T.X₁.localizedModuleMkLinearMap S)
        (T.X₂.localizedModuleMkLinearMap S)
        (T.X₃.localizedModuleMkLinearMap S)
        _ _ T_exact'
      let TS := T.map (ModuleCat.localizedModule_functor S)
      have TS_exact : TS.ShortExact :=
        T_exact.map_of_exact (ModuleCat.localizedModule_functor S)
      let _ : Injective TS.X₂ :=
        (ModuleCat.localizedModule_functor.{v} S).injective_obj _
      intro h
      exact (TS_exact.hasInjectiveDimensionLT_X₃_iff n ‹_›).mp
        (ih T.X₃ ((T_exact.hasInjectiveDimensionLT_X₃_iff n ‹_›).mpr h))
  refine le_of_forall_ge (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
      ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]
    intro _
    apply LocalizedModule.instSubsingleton _
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n
