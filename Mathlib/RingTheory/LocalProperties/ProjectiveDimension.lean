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
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.LocalProperties.Projective

/-!
# The Projective Dimension Equal to Supremum over Localizations

In this file, we proved that projective dimension equal to supremum over localizations

# Main definition and results

-/

@[expose] public section

universe v u

variable {R : Type u} [CommRing R]

open CategoryTheory

instance [Small.{v} R] (S : Submonoid R) :
    (ModuleCat.localizedModule_functor.{v} S).PreservesProjectiveObjects where
  projective_obj X {proj} := by
    let _ : Small.{v, u} (Localization S) := small_of_surjective Localization.mkHom_surjective
    rw [← IsProjective.iff_projective] at proj ⊢
    simpa [ModuleCat.localizedModule_functor] using
      Module.projective_of_isLocalizedModule S (X.localizedModuleMkLinearMap S)

lemma projectiveDimension_eq_iSup_localizedModule_prime [Small.{v, u} R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] : projectiveDimension M =
    ⨆ (p : PrimeSpectrum R), projectiveDimension (M.localizedModule p.1.primeCompl) := by
  have aux (n : ℕ) : projectiveDimension M ≤ n ↔ ⨆ (p : PrimeSpectrum R), projectiveDimension
    (M.localizedModule p.1.primeCompl) ≤ n := by
    simp only [projectiveDimension_le_iff, iSup_le_iff]
    induction n generalizing M
    · simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
      refine ⟨fun h p ↦ ?_, fun h ↦ ?_⟩
      · let _ : Small.{v, u} (Localization p.asIdeal.primeCompl) :=
          small_of_surjective Localization.mkHom_surjective
        rw [← IsProjective.iff_projective]
        exact Module.projective_of_isLocalizedModule p.1.primeCompl
          (M.localizedModuleMkLinearMap p.1.primeCompl)
      · rw [← IsProjective.iff_projective]
        let _ : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
        apply Module.projective_of_localization_maximal (fun p hp ↦ ?_)
        have hp' : p.IsPrime := hp.isPrime
        have : Module.Projective (Localization.AtPrime p) (M.localizedModule p.primeCompl) := by
          let _ : Small.{v, u} (Localization.AtPrime p) :=
            small_of_surjective Localization.mkHom_surjective
          rw [IsProjective.iff_projective]
          exact h ⟨p, hp'⟩
        exact Module.Projective.of_equiv (LinearEquiv.extendScalarsOfIsLocalization p.primeCompl
          (Localization.AtPrime p) (IsLocalizedModule.linearEquiv p.primeCompl
          (M.localizedModuleMkLinearMap p.primeCompl)
          (LocalizedModule.mkLinearMap p.primeCompl M)))
    · rename_i n ih _
      rcases Module.Finite.exists_fin' R M with ⟨m, f', hf'⟩
      let f := f'.comp ((Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)).trans
        (Finsupp.linearEquivFunOnFinite R R (Fin m))).1
      have surjf : Function.Surjective f := by simpa [f] using hf'
      let S : ShortComplex (ModuleCat.{v} R) := {
        f := ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
        g := ModuleCat.ofHom.{v} f
        zero := by
          ext x
          simp }
      have S_exact' : Function.Exact (ConcreteCategory.hom S.f) (ConcreteCategory.hom S.g) := by
        intro x
        simp [S]
      have S_exact : S.ShortExact := {
        exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr S_exact'
        mono_f := (ModuleCat.mono_iff_injective S.f).mpr (LinearMap.ker f).injective_subtype
        epi_g := (ModuleCat.epi_iff_surjective S.g).mpr surjf}
      let _ : Module.Finite R S.X₂ := by
        simp [S, Module.Finite.equiv (Shrink.linearEquiv R R).symm, Finite.of_fintype (Fin m)]
      let _ : Module.Free R (Shrink.{v, u} R) :=  Module.Free.of_equiv (Shrink.linearEquiv R R).symm
      let _ : Module.Free R S.X₂ := Module.Free.finsupp R (Shrink.{v, u} R) _
      have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
      let Sp (p : PrimeSpectrum R) := S.map (ModuleCat.localizedModule_functor p.1.primeCompl)
      have Sp_exact (p : PrimeSpectrum R) : (Sp p).ShortExact :=
        S_exact.map_of_exact (ModuleCat.localizedModule_functor p.asIdeal.primeCompl)
      have ih' := ih (ModuleCat.of R (LinearMap.ker f))
      have projp (p : PrimeSpectrum R) : Projective (Sp p).X₂ :=
        (ModuleCat.localizedModule_functor.{v} p.1.primeCompl).projective_obj_of_projective proj
      simp only [HasProjectiveDimensionLE] at ih' ⊢
      rw [S_exact.hasProjectiveDimensionLT_X₃_iff n proj, ih']
      exact (forall_congr' (fun p ↦ (Sp_exact p).hasProjectiveDimensionLT_X₃_iff n (projp p))).symm
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
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

lemma projectiveDimension_eq_iSup_localizedModule_maximal [Small.{v, u} R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] : projectiveDimension M =
    ⨆ (p : MaximalSpectrum R), projectiveDimension (M.localizedModule p.1.primeCompl) := by
  have aux (n : ℕ) : projectiveDimension M ≤ n ↔ ⨆ (p : MaximalSpectrum R), projectiveDimension
    (M.localizedModule p.1.primeCompl) ≤ n := by
    simp only [projectiveDimension_le_iff, iSup_le_iff]
    induction n generalizing M
    · simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
      refine ⟨fun h p ↦ ?_, fun h ↦ ?_⟩
      · let _ : Small.{v, u} (Localization p.asIdeal.primeCompl) :=
          small_of_surjective Localization.mkHom_surjective
        rw [← IsProjective.iff_projective]
        exact Module.projective_of_isLocalizedModule p.1.primeCompl
          (M.localizedModuleMkLinearMap p.1.primeCompl)
      · rw [← IsProjective.iff_projective]
        let _ : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
        apply Module.projective_of_localization_maximal (fun p hp ↦ ?_)
        have : Module.Projective (Localization.AtPrime p) (M.localizedModule p.primeCompl) := by
          let _ : Small.{v, u} (Localization.AtPrime p) :=
            small_of_surjective Localization.mkHom_surjective
          rw [IsProjective.iff_projective]
          exact h ⟨p, hp⟩
        exact Module.Projective.of_equiv (LinearEquiv.extendScalarsOfIsLocalization p.primeCompl
          (Localization.AtPrime p) (IsLocalizedModule.linearEquiv p.primeCompl
          (M.localizedModuleMkLinearMap p.primeCompl)
          (LocalizedModule.mkLinearMap p.primeCompl M)))
    · rename_i n ih _
      rcases Module.Finite.exists_fin' R M with ⟨m, f', hf'⟩
      let f := f'.comp ((Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)).trans
        (Finsupp.linearEquivFunOnFinite R R (Fin m))).1
      have surjf : Function.Surjective f := by simpa [f] using hf'
      let S : ShortComplex (ModuleCat.{v} R) := {
        f := ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
        g := ModuleCat.ofHom.{v} f
        zero := by
          ext x
          simp }
      have S_exact' : Function.Exact (ConcreteCategory.hom S.f) (ConcreteCategory.hom S.g) := by
        intro x
        simp [S]
      have S_exact : S.ShortExact := {
        exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr S_exact'
        mono_f := (ModuleCat.mono_iff_injective S.f).mpr (LinearMap.ker f).injective_subtype
        epi_g := (ModuleCat.epi_iff_surjective S.g).mpr surjf}
      let _ : Module.Finite R S.X₂ := by
        simp [S, Module.Finite.equiv (Shrink.linearEquiv R R).symm, Finite.of_fintype (Fin m)]
      let _ : Module.Free R (Shrink.{v, u} R) :=  Module.Free.of_equiv (Shrink.linearEquiv R R).symm
      let _ : Module.Free R S.X₂ := Module.Free.finsupp R (Shrink.{v, u} R) _
      have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
      let Sp (p : MaximalSpectrum R) := S.map (ModuleCat.localizedModule_functor p.1.primeCompl)
      have Sp_exact (p : MaximalSpectrum R) : (Sp p).ShortExact :=
        S_exact.map_of_exact (ModuleCat.localizedModule_functor p.asIdeal.primeCompl)
      have ih' := ih (ModuleCat.of R (LinearMap.ker f))
      have projp (p : MaximalSpectrum R) : Projective (Sp p).X₂ :=
        (ModuleCat.localizedModule_functor.{v} p.1.primeCompl).projective_obj_of_projective proj
      simp only [HasProjectiveDimensionLE] at ih' ⊢
      rw [S_exact.hasProjectiveDimensionLT_X₃_iff n proj, ih']
      exact (forall_congr' (fun p ↦ (Sp_exact p).hasProjectiveDimensionLT_X₃_iff n (projp p))).symm
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
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
lemma projectiveDimension_le_projectiveDimension_of_isLocalizedModule [Small.{v, u} R]
    (S : Submonoid R) (M : ModuleCat.{v} R) :
    projectiveDimension (M.localizedModule S) ≤ projectiveDimension M := by
  have aux (n : ℕ) : projectiveDimension M ≤ n → projectiveDimension (M.localizedModule S) ≤ n := by
    simp only [projectiveDimension_le_iff]
    let _ : Small.{v, u} (Localization S) :=
      small_of_surjective Localization.mkHom_surjective
    induction n generalizing M
    · simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
      rw [← IsProjective.iff_projective, ← IsProjective.iff_projective]
      intro _
      exact Module.projective_of_isLocalizedModule S (M.localizedModuleMkLinearMap S)
    · rename_i n ih
      rcases ModuleCat.enoughProjectives.1 M with ⟨⟨P, f⟩⟩
      let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
      have T_exact : T.ShortExact := {
        exact := ShortComplex.exact_kernel f
        mono_f := equalizer.ι_mono
        epi_g := ‹_›}
      have T_exact' : Function.Exact (ConcreteCategory.hom T.f) (ConcreteCategory.hom T.g) :=
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp T_exact.1
      have TS_exact' := IsLocalizedModule.map_exact S
        (T.X₁.localizedModuleMkLinearMap S)
        (T.X₂.localizedModuleMkLinearMap S)
        (T.X₃.localizedModuleMkLinearMap S)
        _ _ T_exact'
      let TS := T.map (ModuleCat.localizedModule_functor S)
      have TS_exact : TS.ShortExact := {
        exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr TS_exact'
        mono_f := (ModuleCat.mono_iff_injective _).mpr (IsLocalizedModule.map_injective S
          (T.X₁.localizedModuleMkLinearMap S) (T.X₂.localizedModuleMkLinearMap S)
            _ ((ModuleCat.mono_iff_injective T.f).mp T_exact.2))
        epi_g := (ModuleCat.epi_iff_surjective _).mpr (IsLocalizedModule.map_surjective S
          (T.X₂.localizedModuleMkLinearMap S) (T.X₃.localizedModuleMkLinearMap S)
            _ ((ModuleCat.epi_iff_surjective T.g).mp T_exact.3)) }
      let _ : Projective TS.X₂ := (ModuleCat.localizedModule_functor.{v} S).projective_obj _
      intro h
      exact (TS_exact.hasProjectiveDimensionLT_X₃_iff n ‹_›).mpr
        (ih (kernel f) ((T_exact.hasProjectiveDimensionLT_X₃_iff n ‹_›).mp h))
  refine le_of_forall_ge (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
      ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]
    intro _
    apply LocalizedModule.instSubsingleton _
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n
