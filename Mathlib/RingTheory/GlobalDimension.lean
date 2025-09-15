/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Localization.Module
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
/-!
# The Global Dimension of a Ring
-/

--set_option pp.universes true

universe u v

variable (R : Type u) [CommRing R]

open CategoryTheory IsLocalRing RingTheory.Sequence

section ProjectiveDimension

variable {C : Type u} [Category.{v, u} C] [Abelian C]

--projectiveDimension should be `-∞` when `X = 0`

noncomputable def projectiveDimension (X : C) : WithBot ℕ∞ :=
  sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i → HasProjectiveDimensionLT X i}

/-
noncomputable def nonnegProjectiveDimension (X : C) : ℕ∞ :=
  sInf (({(n : ℕ) | HasProjectiveDimensionLT X n}).image WithTop.some)
-/

lemma projectiveDimension_eq_of_iso (X Y : C) (e : X ≅ Y) :
    projectiveDimension X = projectiveDimension Y := by
  simp only [projectiveDimension]
  congr! 5
  exact ⟨fun h ↦ hasProjectiveDimensionLT_of_iso e _,
    fun h ↦ hasProjectiveDimensionLT_of_iso e.symm _⟩

lemma hasProjectiveDimensionLT_of_projectiveDimension_lt (X : C) (n : ℕ)
    (h : projectiveDimension X < n) : HasProjectiveDimensionLT X n := by
  have : projectiveDimension X ∈ _ := csInf_mem (by
    use ⊤
    simp)
  simp only [Set.mem_setOf_eq] at this
  exact this n h

lemma projectiveDimension_le_iff (X : C) (n : ℕ) : projectiveDimension X ≤ n ↔
    HasProjectiveDimensionLE X n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · apply hasProjectiveDimensionLT_of_projectiveDimension_lt X (n + 1)
    exact lt_of_le_of_lt h (Nat.cast_lt.mpr (lt_add_one n))
  · apply sInf_le
    simp only [Set.mem_setOf_eq, Nat.cast_lt]
    intro i hi
    exact hasProjectiveDimensionLT_of_ge X (n + 1) i hi

lemma projectiveDimension_ge_iff (X : C) (n : ℕ) : n ≤ projectiveDimension X  ↔
    ¬ HasProjectiveDimensionLT X n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [projectiveDimension, le_sInf_iff, Set.mem_setOf_eq] at h
    by_contra lt
    by_cases eq0 : n = 0
    · have := h ⊥ (fun i _ ↦ (hasProjectiveDimensionLT_of_ge X n i (by simp [eq0])))
      simp [eq0] at this
    · have : ∀ (i : ℕ), (n - 1 : ℕ) < (i : WithBot ℕ∞) → HasProjectiveDimensionLT X i := by
        intro i hi
        exact hasProjectiveDimensionLT_of_ge X n i (Nat.le_of_pred_lt (Nat.cast_lt.mp hi))
      have not := Nat.cast_le.mp (h (n - 1 : ℕ) this)
      omega
  · simp only [projectiveDimension, le_sInf_iff, Set.mem_setOf_eq]
    intro m hm
    by_contra nle
    exact h (hm _ (lt_of_not_ge nle))

lemma projectiveDimension_eq_bot_iff (X : C) : projectiveDimension X = ⊥ ↔
    Limits.IsZero X := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : HasProjectiveDimensionLT X 0 := by
      apply hasProjectiveDimensionLT_of_projectiveDimension_lt X 0
      simp [h, bot_lt_iff_ne_bot]
    exact isZero_of_hasProjectiveDimensionLT_zero X
  · rw [eq_bot_iff]
    apply sInf_le
    intro i _
    have := h.hasProjectiveDimensionLT_zero
    apply hasProjectiveDimensionLT_of_ge X 0 i (Nat.zero_le i)

lemma projectiveDimension_eq_find (X : C) (h : ∃ n, HasProjectiveDimensionLE X n)
    (nzero : ¬ Limits.IsZero X) [DecidablePred (HasProjectiveDimensionLE X)] :
    projectiveDimension X = Nat.find h := by
  apply le_antisymm ((projectiveDimension_le_iff _ _).mpr (Nat.find_spec h))
  apply (projectiveDimension_ge_iff _ _).mpr
  by_cases eq0 : Nat.find h = 0
  · simp only [eq0]
    by_contra
    exact nzero (isZero_of_hasProjectiveDimensionLT_zero X)
  · rw [← Nat.succ_pred_eq_of_ne_zero eq0]
    exact (Nat.find_min h (Nat.sub_one_lt eq0))
/-
lemma projectiveDimension_eq_nonnegProjectiveDimension_of_not_zero (X : C) (h : ¬ Limits.IsZero X) :
    nonnegProjectiveDimension X = projectiveDimension X :=  by
  sorry
-/

lemma projectiveDimension_ne_top_iff (X : C) : projectiveDimension X ≠ ⊤ ↔
    ∃ n, HasProjectiveDimensionLE X n := by
  simp only [projectiveDimension, ne_eq, sInf_eq_top, Set.mem_setOf_eq, not_forall]
  refine ⟨fun ⟨x, hx, ne⟩ ↦ ?_, fun ⟨n, hn⟩ ↦ ?_⟩
  · by_cases eqbot : x = ⊥
    · use 0
      have := hx 0 (by simp [eqbot, bot_lt_iff_ne_bot])
      exact instHasProjectiveDimensionLTSucc X 0
    · have : x.unbot eqbot ≠ ⊤ := by
        by_contra eq
        rw [← WithBot.coe_inj, WithBot.coe_unbot, WithBot.coe_top] at eq
        exact ne eq
      use (x.unbot eqbot).toNat
      have eq : x = (x.unbot eqbot).toNat := (WithBot.coe_unbot x eqbot).symm.trans
        (WithBot.coe_inj.mpr (ENat.coe_toNat this).symm)
      have : x < ((x.unbot eqbot).toNat + 1 : ℕ) := by
        nth_rw 1 [eq]
        exact Nat.cast_lt.mpr (lt_add_one _)
      exact hx ((x.unbot eqbot).toNat + 1 : ℕ) this
  · use n
    simpa using ⟨fun i hi ↦ hasProjectiveDimensionLT_of_ge X (n + 1) i hi,
      WithBot.coe_inj.not.mpr (ENat.coe_ne_top n)⟩

/-
lemma nonnegProjectiveDimension_ne_top_iff (X : C) : nonnegProjectiveDimension X ≠ ⊤ ↔
    ∃ n, HasProjectiveDimensionLE X n := by
  sorry
-/

--needed
open Limits Abelian in
lemma hasProjectiveDimensionLT_one_iff (X : C) :
    Projective X ↔ HasProjectiveDimensionLT X 1 := by
  letI := HasExt.standard C
  refine ⟨fun h ↦ inferInstance, fun ⟨h⟩ ↦ ⟨?_⟩⟩
  intro Z Y f g epi
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have S_exact : S.ShortExact := {
    exact := ShortComplex.exact_kernel g
    mono_f := equalizer.ι_mono
    epi_g := epi}
  have : IsZero (AddCommGrp.of (Ext X S.X₁ 1)) := by
    let _ := h 1 (le_refl 1) (Y := S.X₁)
    exact AddCommGrp.isZero_of_subsingleton _
  have exac := Ext.covariant_sequence_exact₃' X S_exact 0 1 (zero_add 1)
  have surj: Function.Surjective ((Ext.mk₀ S.g).postcomp X (add_zero 0)) :=
    (AddCommGrp.epi_iff_surjective _).mp (exac.epi_f (this.eq_zero_of_tgt _))
  rcases surj (Ext.mk₀ f) with ⟨f', hf'⟩
  use Ext.addEquiv₀ f'
  simp only [AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply] at hf'
  rw [← Ext.mk₀_addEquiv₀_apply f', Ext.mk₀_comp_mk₀] at hf'
  exact (Ext.mk₀_bijective X Y).1 hf'

end ProjectiveDimension

variable [IsNoetherianRing R]

local instance [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] (S : Submonoid R) :
    Small.{v} (LocalizedModule S M) :=
  small_of_surjective (IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M))



variable {R}

noncomputable def ModuleCat.localizedModule [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    ModuleCat.{v} (Localization S) :=
  ModuleCat.of.{v} _ (Shrink.{v} (LocalizedModule S M))

noncomputable local instance [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    Module R (M.localizedModule S) :=
  inferInstanceAs (Module R (Shrink.{v} (LocalizedModule S M)))

noncomputable def ModuleCat.localizedModule_mkLinearMap [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : M →ₗ[R] (M.localizedModule S) :=
  (Shrink.linearEquiv.{v} R _).symm.toLinearMap.comp (LocalizedModule.mkLinearMap S M)

instance ModuleCat.localizedModule_isLocalizedModule [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : IsLocalizedModule S (M.localizedModule_mkLinearMap S) := by
  simpa [ModuleCat.localizedModule_mkLinearMap] using IsLocalizedModule.of_linearEquiv _ _ _

instance [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    IsScalarTower R (Localization S) (M.localizedModule S) :=
  (equivShrink (LocalizedModule S M)).symm.isScalarTower R (Localization S)

noncomputable def ModuleCat.localizedModule_map [Small.{v} R] {M N : ModuleCat.{v} R}
    (S : Submonoid R) (f : M ⟶ N) : (M.localizedModule S) ⟶ (N.localizedModule S) :=
  ModuleCat.ofHom.{v} <| IsLocalizedModule.mapExtendScalars S (M.localizedModule_mkLinearMap S)
    (N.localizedModule_mkLinearMap S) (Localization S) (ModuleCat.homLinearEquiv (S := R) f)

lemma projectiveDimension_eq_iSup_localizedModule_prime (M : ModuleCat.{v} R) [Module.Finite R M]
    [Small.{v, u} R] : projectiveDimension M = ⨆ (p : PrimeSpectrum R), projectiveDimension
    (M.localizedModule p.1.primeCompl) := by
  have aux (n : ℕ) : projectiveDimension M ≤ n ↔ ⨆ (p : PrimeSpectrum R), projectiveDimension
    (M.localizedModule p.1.primeCompl) ≤ n := by
    simp only [projectiveDimension_le_iff, iSup_le_iff]
    induction' n with n ih generalizing M
    · simp only [HasProjectiveDimensionLE, zero_add, ← hasProjectiveDimensionLT_one_iff]
      refine ⟨fun h p ↦ ?_, fun h ↦ ?_⟩
      · let _ : Small.{v, u} (Localization p.asIdeal.primeCompl) :=
          small_of_surjective Localization.mkHom_surjective
        rw [← IsProjective.iff_projective]
        exact Module.projective_of_isLocalizedModule p.1.primeCompl
          (M.localizedModule_mkLinearMap p.1.primeCompl)
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
          (M.localizedModule_mkLinearMap p.primeCompl)
          (LocalizedModule.mkLinearMap p.primeCompl M)))
    · rcases Module.Finite.exists_fin' R M with ⟨m, f', hf'⟩
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
      let _ := S.X₁.localizedModule_isLocalizedModule
      let _ := S.X₂.localizedModule_isLocalizedModule
      let _ := S.X₃.localizedModule_isLocalizedModule
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
            _ (LinearMap.ker f).injective_subtype)
        epi_g := (ModuleCat.epi_iff_surjective _).mpr
          (IsLocalizedModule.map_surjective p.1.primeCompl
            (S.X₂.localizedModule_mkLinearMap p.1.primeCompl)
            (S.X₃.localizedModule_mkLinearMap p.1.primeCompl)
            _ surjf) }
      have ih' := ih (ModuleCat.of R (LinearMap.ker f))
      let _ (p : PrimeSpectrum R) : Module.Free (Localization.AtPrime p.1) (Sp p).X₂ :=
        Module.free_of_isLocalizedModule p.1.primeCompl
        (S.X₂.localizedModule_mkLinearMap p.1.primeCompl)
      have projp (p : PrimeSpectrum R) :=
        ModuleCat.projective_of_categoryTheory_projective (Sp p).X₂
      simp only [HasProjectiveDimensionLE] at ih' ⊢
      rw [S_exact.hasProjectiveDimensionLT_X₃_iff n proj, ih']
      exact (forall_congr' (fun p ↦ (Sp_exact p).hasProjectiveDimensionLT_X₃_iff n (projp p))).symm
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  by_cases eqbot : N = ⊥
  · simp only [eqbot, le_bot_iff, projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
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

lemma projectiveDimension_eq_iSup_localizedModule_maximal (M : ModuleCat.{v} R) [Module.Finite R M]
    [Small.{v, u} R] : projectiveDimension M = ⨆ (p : MaximalSpectrum R), projectiveDimension
    (M.localizedModule p.1.primeCompl) := by
  have aux (n : ℕ) : projectiveDimension M ≤ n ↔ ⨆ (p : MaximalSpectrum R), projectiveDimension
    (M.localizedModule p.1.primeCompl) ≤ n := by
    simp only [projectiveDimension_le_iff, iSup_le_iff]
    induction' n with n ih generalizing M
    · simp only [HasProjectiveDimensionLE, zero_add, ← hasProjectiveDimensionLT_one_iff]
      refine ⟨fun h p ↦ ?_, fun h ↦ ?_⟩
      · let _ : Small.{v, u} (Localization p.asIdeal.primeCompl) :=
          small_of_surjective Localization.mkHom_surjective
        rw [← IsProjective.iff_projective]
        exact Module.projective_of_isLocalizedModule p.1.primeCompl
          (M.localizedModule_mkLinearMap p.1.primeCompl)
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
          (M.localizedModule_mkLinearMap p.primeCompl)
          (LocalizedModule.mkLinearMap p.primeCompl M)))
    · rcases Module.Finite.exists_fin' R M with ⟨m, f', hf'⟩
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
      let _ := S.X₁.localizedModule_isLocalizedModule
      let _ := S.X₂.localizedModule_isLocalizedModule
      let _ := S.X₃.localizedModule_isLocalizedModule
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
            _ (LinearMap.ker f).injective_subtype)
        epi_g := (ModuleCat.epi_iff_surjective _).mpr
          (IsLocalizedModule.map_surjective p.1.primeCompl
            (S.X₂.localizedModule_mkLinearMap p.1.primeCompl)
            (S.X₃.localizedModule_mkLinearMap p.1.primeCompl)
            _ surjf) }
      have ih' := ih (ModuleCat.of R (LinearMap.ker f))
      let _ (p : MaximalSpectrum R) : Module.Free (Localization.AtPrime p.1) (Sp p).X₂ :=
        Module.free_of_isLocalizedModule p.1.primeCompl
        (S.X₂.localizedModule_mkLinearMap p.1.primeCompl)
      have projp (p : MaximalSpectrum R) :=
        ModuleCat.projective_of_categoryTheory_projective (Sp p).X₂
      simp only [HasProjectiveDimensionLE] at ih' ⊢
      rw [S_exact.hasProjectiveDimensionLT_X₃_iff n proj, ih']
      exact (forall_congr' (fun p ↦ (Sp_exact p).hasProjectiveDimensionLT_X₃_iff n (projp p))).symm
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  by_cases eqbot : N = ⊥
  · simp only [eqbot, le_bot_iff, projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
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
omit [IsNoetherianRing R] in
lemma projectiveDimension_le_projectiveDimension_of_isLocalizedModule [Small.{v, u} R]
    (S : Submonoid R) (M : ModuleCat.{v} R) :
    projectiveDimension (M.localizedModule S) ≤ projectiveDimension M := by
  have aux (n : ℕ) : projectiveDimension M ≤ n → projectiveDimension (M.localizedModule S) ≤ n := by
    simp only [projectiveDimension_le_iff]
    let _ : Small.{v, u} (Localization S) :=
      small_of_surjective Localization.mkHom_surjective
    induction' n with n ih generalizing M
    · simp only [HasProjectiveDimensionLE, zero_add, ← hasProjectiveDimensionLT_one_iff]
      rw [← IsProjective.iff_projective, ← IsProjective.iff_projective]
      intro _
      exact Module.projective_of_isLocalizedModule S (M.localizedModule_mkLinearMap S)
    · rcases ModuleCat.enoughProjectives.1 M with ⟨⟨P, f⟩⟩
      let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
      have T_exact : T.ShortExact := {
        exact := ShortComplex.exact_kernel f
        mono_f := equalizer.ι_mono
        epi_g := ‹_›}
      have T_exact' : Function.Exact (ConcreteCategory.hom T.f) (ConcreteCategory.hom T.g) :=
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp T_exact.1
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
      let _ : Projective TS.X₂ := by
        rw [← IsProjective.iff_projective]
        have : Module.Projective R T.X₂ := (IsProjective.iff_projective _).mpr ‹_›
        exact Module.projective_of_isLocalizedModule S (T.X₂.localizedModule_mkLinearMap S)
      simp only [HasProjectiveDimensionLE]
      rw [T_exact.hasProjectiveDimensionLT_X₃_iff n ‹_›,
        TS_exact.hasProjectiveDimensionLT_X₃_iff n ‹_›]
      exact ih (kernel f)
  refine le_of_forall_ge (fun N ↦ ?_)
  by_cases eqbot : N = ⊥
  · simp only [eqbot, le_bot_iff, projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
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

section GlobalDimension

variable (R : Type u) [CommRing R]

open Abelian

local instance [Small.{v} R] (I : Ideal R) : Small.{v} (R ⧸ I) :=
  small_of_surjective Ideal.Quotient.mk_surjective

local instance [Small.{v} R] : CategoryTheory.HasExt.{max u v} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{max u v} (ModuleCat.{v} R)

open Limits in
lemma ext_subsingleton_of_quotients [Small.{v} R] (M : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ I : Ideal R, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M (n + 1))) :
    ∀ N : ModuleCat.{v} R, Subsingleton (Ext N M (n + 1)) := by
  induction' n with n ih generalizing M
  · have : Injective M := by
      rw [← Module.injective_iff_injective_object, ← Module.Baer.iff_injective]
      intro I g

      sorry
    intro N
    exact subsingleton_of_forall_eq 0 (fun e ↦ Ext.eq_zero_of_injective e)
  · let ei : EnoughInjectives (ModuleCat R) := inferInstance
    rcases ei.1 M with ⟨⟨I, inj, f, mono⟩⟩
    let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have S_exact : S.ShortExact := {
      exact := ShortComplex.exact_cokernel f
      mono_f := ‹_›
      epi_g := coequalizer.π_epi}
    have (N : ModuleCat R) : Subsingleton (Ext N M (n + 1 + 1)) ↔
      Subsingleton (Ext N (cokernel f) (n + 1)) := by
      have (m : ℕ) : Subsingleton (AddCommGrp.of (Ext N S.X₂ (m + 1))) :=
        subsingleton_of_forall_eq 0 Ext.eq_zero_of_injective
      have := ComposableArrows.Exact.isIso_map'
        (Ext.covariantSequence_exact N S_exact (n + 1) (n + 1 + 1) rfl) 1 (by decide)
        (IsZero.eq_zero_of_src (AddCommGrp.of (Ext N S.X₂ (n + 1))).isZero_of_subsingleton _)
        (IsZero.eq_zero_of_tgt (AddCommGrp.of (Ext N S.X₂ (n + 1 + 1))).isZero_of_subsingleton _)
      exact (@asIso _ _ _ _ _ this).addCommGroupIsoToAddEquiv.subsingleton_congr.symm
    simp only [this] at h ⊢
    exact ih (cokernel f) h

noncomputable def globalDimension : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{v} R), projectiveDimension M

lemma globalDimension_eq_bot_iff [Small.{v} R] : globalDimension.{u, v} R = ⊥ ↔ Subsingleton R := by
  simp only [globalDimension, iSup_eq_bot, projectiveDimension_eq_bot_iff,
    ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun h ↦ ?_, fun h M ↦ Module.subsingleton R M⟩
  let _ := h (ModuleCat.of R (Shrink.{v} R))
  exact (equivShrink.{v} R).subsingleton

lemma globalDimension_le_iff (n : ℕ) : globalDimension.{u, v} R ≤ n ↔
    ∀ M : ModuleCat.{v} R, HasProjectiveDimensionLE M n := by
  simp [globalDimension, projectiveDimension_le_iff]

lemma globalDimension_le_tfae [Small.{v} R] (n : ℕ) :
    [globalDimension.{u, v} R ≤ n,
    ∀ M : ModuleCat.{v} R, Module.Finite R M → HasProjectiveDimensionLE M n,
    ∀ m ≥ n, ∀ (N M : ModuleCat.{v} R), Subsingleton (Ext N M m)].TFAE := by
  sorry

lemma globalDimension_eq_iSup_loclization_prime : globalDimension.{u, v} R =
    ⨆ (p : PrimeSpectrum R), globalDimension.{u, v} (Localization.AtPrime p.1) := by
  sorry

lemma globalDimension_eq_iSup_loclization_maximal : globalDimension.{u, v} R =
    ⨆ (p : MaximalSpectrum R), globalDimension.{u, v} (Localization.AtPrime p.1) := by
  sorry

end GlobalDimension
