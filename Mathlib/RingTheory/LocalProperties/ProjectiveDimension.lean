/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.RingTheory.LocalProperties.Projective

/-!
# The Projective Dimension Equal to Supremum over Localizations

In this file, we proved that projective dimension equal to supremum over localizations

# Main definition and results

-/

@[expose] public section

universe v u

variable {R : Type u} [CommRing R]

namespace ModuleCat

open CategoryTheory

set_option backward.isDefEq.respectTransparency false in
instance [Small.{v} R] (S : Submonoid R) :
    (ModuleCat.localizedModuleFunctor.{v} S).PreservesProjectiveObjects where
  projective_obj X {proj} := by
    have : Small.{v} (Localization S) := small_of_surjective Localization.mkHom_surjective
    rw [← IsProjective.iff_projective] at proj ⊢
    simpa [ModuleCat.localizedModuleFunctor] using
      Module.projective_of_isLocalizedModule S (X.localizedModuleMkLinearMap S)

open Limits in
lemma localizedModule_hasProjectiveDimensionLE [Small.{v, u} R] (n : ℕ) (S : Submonoid R)
    (M : ModuleCat.{v} R) [projle : HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE (M.localizedModule S) n := by
  have : Small.{v} (Localization S) := small_of_surjective Localization.mkHom_surjective
  induction n generalizing M with
  | zero =>
    simp only [HasProjectiveDimensionLE, zero_add] at projle ⊢
    rw [← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective] at projle ⊢
    exact Module.projective_of_isLocalizedModule S (M.localizedModuleMkLinearMap S)
  | succ n ih =>
    rcases ModuleCat.enoughProjectives.1 M with ⟨⟨P, f⟩⟩
    let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have T_exact : T.ShortExact := { exact := ShortComplex.exact_kernel f }
    have TS_exact' := IsLocalizedModule.map_exact S (T.X₁.localizedModuleMkLinearMap S)
      (T.X₂.localizedModuleMkLinearMap S) (T.X₃.localizedModuleMkLinearMap S)
      _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp T_exact.1)
    let TS := T.map (ModuleCat.localizedModuleFunctor S)
    have TS_exact : TS.ShortExact := T_exact.map_of_exact (ModuleCat.localizedModuleFunctor S)
    have : Projective TS.X₂ := (ModuleCat.localizedModuleFunctor.{v} S).projective_obj _
    have := (T_exact.hasProjectiveDimensionLT_X₃_iff n ‹_›).mp projle
    exact (TS_exact.hasProjectiveDimensionLT_X₃_iff n ‹_›).mpr (ih (kernel f))

lemma projectiveDimension_le_projectiveDimension_of_isLocalizedModule [Small.{v, u} R]
    (S : Submonoid R) (M : ModuleCat.{v} R) :
    projectiveDimension (M.localizedModule S) ≤ projectiveDimension M := by
  have aux (n : ℕ) : projectiveDimension M ≤ n → projectiveDimension (M.localizedModule S) ≤ n := by
    simp only [projectiveDimension_le_iff]
    intro h
    exact ModuleCat.localizedModule_hasProjectiveDimensionLE n S M
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

set_option backward.isDefEq.respectTransparency false in
lemma hasProjectiveDimensionLE_iff_forall_maximalSpectrum (n : ℕ) [Small.{v} R]
    [IsNoetherianRing R] (M : ModuleCat.{v} R) [Module.Finite R M] : HasProjectiveDimensionLE M n ↔
    ∀ (m : MaximalSpectrum R), HasProjectiveDimensionLE (M.localizedModule m.1.primeCompl) n := by
  induction n generalizing M with
  | zero =>
    simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
    refine ⟨fun h p ↦ ?_, fun h ↦ ?_⟩
    · have : Small.{v} (Localization p.asIdeal.primeCompl) :=
        small_of_surjective Localization.mkHom_surjective
      rw [← IsProjective.iff_projective]
      exact Module.projective_of_isLocalizedModule p.1.primeCompl
        (M.localizedModuleMkLinearMap p.1.primeCompl)
    · rw [← IsProjective.iff_projective]
      have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
      apply Module.projective_of_localization_maximal (fun p hp ↦ ?_)
      have : Module.Projective (Localization.AtPrime p) (M.localizedModule p.primeCompl) := by
        have : Small.{v} (Localization.AtPrime p) :=
          small_of_surjective Localization.mkHom_surjective
        rw [IsProjective.iff_projective]
        exact h ⟨p, hp⟩
      exact Module.Projective.of_equiv (LinearEquiv.extendScalarsOfIsLocalization p.primeCompl
        (Localization.AtPrime p) (IsLocalizedModule.linearEquiv p.primeCompl
        (M.localizedModuleMkLinearMap p.primeCompl)
        (LocalizedModule.mkLinearMap p.primeCompl M)))
  | succ n ih =>
    rcases Module.exists_finite_presentation R M with ⟨P, _, _, _, _, f, surjf⟩
    let S := f.shortComplexKer
    have S_exact := LinearMap.shortExact_shortComplexKer surjf
    have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
    let Sp (p : MaximalSpectrum R) := S.map (ModuleCat.localizedModuleFunctor p.1.primeCompl)
    have Sp_exact (p : MaximalSpectrum R) : (Sp p).ShortExact :=
      S_exact.map_of_exact (ModuleCat.localizedModuleFunctor p.asIdeal.primeCompl)
    specialize ih (ModuleCat.of R (LinearMap.ker f))
    have projp (p : MaximalSpectrum R) : Projective (Sp p).X₂ :=
      (ModuleCat.localizedModuleFunctor.{v} p.1.primeCompl).projective_obj_of_projective proj
    simp only [HasProjectiveDimensionLE] at ih ⊢
    rw [S_exact.hasProjectiveDimensionLT_X₃_iff n proj, ih]
    exact (forall_congr' (fun p ↦ (Sp_exact p).hasProjectiveDimensionLT_X₃_iff n (projp p))).symm

lemma hasProjectiveDimensionLE_iff_forall_primeSpectrum (n : ℕ) [Small.{v} R]
    [IsNoetherianRing R] (M : ModuleCat.{v} R) [Module.Finite R M] : HasProjectiveDimensionLE M n ↔
    ∀ (p : PrimeSpectrum R), HasProjectiveDimensionLE (M.localizedModule p.1.primeCompl) n :=
  ⟨fun _ p ↦ M.localizedModule_hasProjectiveDimensionLE n p.1.primeCompl,
    fun h ↦ (M.hasProjectiveDimensionLE_iff_forall_maximalSpectrum n).mpr
    fun m ↦ h ⟨m.1, Ideal.IsMaximal.isPrime' m.1⟩⟩

lemma projectiveDimension_eq_iSup_localizedModule_prime [Small.{v} R]
    [IsNoetherianRing R] (M : ModuleCat.{v} R) [Module.Finite R M] : projectiveDimension M =
    ⨆ (p : PrimeSpectrum R), projectiveDimension (M.localizedModule p.1.primeCompl) := by
  have aux (n : ℕ) : projectiveDimension M ≤ n ↔ ⨆ (p : PrimeSpectrum R), projectiveDimension
    (M.localizedModule p.1.primeCompl) ≤ n := by
    simp only [projectiveDimension_le_iff, iSup_le_iff]
    exact M.hasProjectiveDimensionLE_iff_forall_primeSpectrum n
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

lemma projectiveDimension_eq_iSup_localizedModule_maximal [Small.{v} R]
    [IsNoetherianRing R] (M : ModuleCat.{v} R) [Module.Finite R M] : projectiveDimension M =
    ⨆ (p : MaximalSpectrum R), projectiveDimension (M.localizedModule p.1.primeCompl) := by
  have aux (n : ℕ) : projectiveDimension M ≤ n ↔ ⨆ (p : MaximalSpectrum R), projectiveDimension
    (M.localizedModule p.1.primeCompl) ≤ n := by
    simp only [projectiveDimension_le_iff, iSup_le_iff]
    exact M.hasProjectiveDimensionLE_iff_forall_maximalSpectrum n
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

end ModuleCat
