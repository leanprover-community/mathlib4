/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.LocalProperties.Projective

/-!
# The Global Dimension of a Ring

In this file, we define the projective dimension of an module and global dimension of ring
and their basic properties.

# Main definition and results

* `projectiveDimension` : Given `X : C` where `C` is abelian,
  return its projective dimension as `WithBot ℕ∞`

* `globalDimension` : The global (homological) dimension of a (commutative) ring defined as
  the supremum of projective dimension over all modules.

-/

@[expose] public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory

local instance [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] (S : Submonoid R) :
    Small.{v} (LocalizedModule S M) :=
  small_of_surjective (IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M))

variable {R}

/-- Shrink of `LocalizedModule S M` in category which `M` belongs. -/
noncomputable def ModuleCat.localizedModule [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    ModuleCat.{v} (Localization S) :=
  ModuleCat.of.{v} _ (Shrink.{v} (LocalizedModule S M))

/-- The `R` module structure on `M.localizedModule S` given by the
`R` module structure on (Shrink.{v} (LocalizedModule S M)) -/
noncomputable local instance [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    Module R (M.localizedModule S) :=
  inferInstanceAs (Module R (Shrink.{v} (LocalizedModule S M)))

/-- The corresponding linear map to make `M.localizedModule` is localized module of `M`. -/
noncomputable def ModuleCat.localizedModule_mkLinearMap [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : M →ₗ[R] (M.localizedModule S) :=
  (Shrink.linearEquiv.{v} R _).symm.toLinearMap.comp (LocalizedModule.mkLinearMap S M)

instance ModuleCat.localizedModule_isLocalizedModule [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : IsLocalizedModule S (M.localizedModule_mkLinearMap S) := by
  simpa [ModuleCat.localizedModule_mkLinearMap] using IsLocalizedModule.of_linearEquiv _ _ _

instance [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    IsScalarTower R (Localization S) (M.localizedModule S) :=
  (equivShrink (LocalizedModule S M)).symm.isScalarTower R (Localization S)

/-- The category version of `IsLocalizedModule.mapExtendScalars`. -/
noncomputable def ModuleCat.localizedModule_map [Small.{v} R] {M N : ModuleCat.{v} R}
    (S : Submonoid R) (f : M ⟶ N) : (M.localizedModule S) ⟶ (N.localizedModule S) :=
  ModuleCat.ofHom.{v} <| IsLocalizedModule.mapExtendScalars S (M.localizedModule_mkLinearMap S)
    (N.localizedModule_mkLinearMap S) (Localization S) (ModuleCat.homLinearEquiv (S := R) f)

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
      exact Module.projective_of_isLocalizedModule S (M.localizedModule_mkLinearMap S)
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
