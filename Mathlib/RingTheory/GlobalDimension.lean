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
/-!
# The Global Dimension of a Ring
-/

--set_option pp.universes true

universe u v

variable (R : Type u) [CommRing R]

open CategoryTheory IsLocalRing RingTheory.Sequence

def HasGlobalDimensionLE (n : ℕ) : Prop :=
  ∀ (M : ModuleCat.{v} R), HasProjectiveDimensionLE M n

noncomputable def globalDimension : ℕ∞ :=
  sInf (({(n : ℕ) | HasGlobalDimensionLE.{u, v} R n}).image WithTop.some)

lemma HasGlobalDimensionLE_iff (n : ℕ) : HasGlobalDimensionLE R n ↔ globalDimension R ≤ n := by
  sorry

section ProjectiveDimension

variable {C : Type u} [Category.{v, u} C] [Abelian C]

--projectiveDimension should be `-∞` when `X = 0`

noncomputable def projectiveDimension (X : C) : WithBot ℕ∞ :=
  sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i → HasProjectiveDimensionLT X i}

noncomputable def nonnegProjectiveDimension (X : C) : ℕ∞ :=
  sInf (({(n : ℕ) | HasProjectiveDimensionLT X n}).image WithTop.some)

lemma projectiveDimension_eq_of_iso (X Y : C) (e : X ≅ Y) :
    projectiveDimension X = projectiveDimension Y := by
  sorry

lemma projectiveDimension_le_iff (X : C) (n : ℕ) : projectiveDimension X ≤ n ↔
    HasProjectiveDimensionLE X n := by
  sorry

lemma projectiveDimension_eq_bot_iff (X : C) : projectiveDimension X = ⊥ ↔
    Limits.IsZero X := by
  sorry

lemma projectiveDimension_eq_nonnegProjectiveDimension_of_not_zero (X : C) (h : ¬ Limits.IsZero X) :
    nonnegProjectiveDimension X = projectiveDimension X :=  by
  sorry

lemma projectiveDimension_ne_top_iff (X : C) : projectiveDimension X ≠ ⊤ ↔
    ∃ n, HasProjectiveDimensionLE X n := by
  sorry

lemma nonnegProjectiveDimension_ne_top_iff (X : C) : nonnegProjectiveDimension X ≠ ⊤ ↔
    ∃ n, HasProjectiveDimensionLE X n := by
  sorry

lemma hasProjectiveDimensionLT_one_iff (X : C) : Projective X ↔ HasProjectiveDimensionLT X 1 := by
  refine ⟨fun h ↦ inferInstance, fun h ↦ ?_⟩

  sorry

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
      --Module.projective_of_isLocalizedModule
      --Module.projective_of_localization_maximal
      sorry
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
  · simp only [eqbot, le_bot_iff, projectiveDimension_eq_bot_iff, iSup_eq_bot,
      ModuleCat.isZero_iff_subsingleton]
    simp only [ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]

    sorry
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
      --Module.projective_of_isLocalizedModule
      --Module.projective_of_localization_maximal
      sorry
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
  · simp only [eqbot, le_bot_iff, projectiveDimension_eq_bot_iff, iSup_eq_bot,
      ModuleCat.isZero_iff_subsingleton]
    simp only [ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]

    sorry
  · by_cases eqtop : N.unbot eqbot = ⊤
    · have : N = ⊤ := (WithBot.coe_unbot _ eqbot).symm.trans (WithBot.coe_inj.mpr eqtop)
      simp [this]
    · let n := (N.unbot eqbot).toNat
      have : N = n := (WithBot.coe_unbot _ eqbot).symm.trans
        (WithBot.coe_inj.mpr (ENat.coe_toNat eqtop).symm)
      simpa only [this] using aux n

lemma globalDimension_eq_iSup_loclization_prime : globalDimension.{u, v} R =
    ⨆ (p : PrimeSpectrum R), globalDimension.{u, v} (Localization.AtPrime p.1) := by
  sorry

lemma globalDimension_eq_iSup_loclization_maximal : globalDimension.{u, v} R =
    ⨆ (p : MaximalSpectrum R), globalDimension.{u, v} (Localization.AtPrime p.1) := by
  sorry
