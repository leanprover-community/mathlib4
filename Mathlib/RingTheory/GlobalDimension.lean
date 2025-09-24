/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Ideal.Quotient.Operations
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

--set_option pp.universes true

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
    · simp only [HasProjectiveDimensionLE, zero_add, ← hasProjectiveDimensionLT_one_iff]
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

section GlobalDimension

variable (R : Type u) [CommRing R]

open Abelian

local instance small_of_quotient [Small.{v} R] (I : Ideal R) : Small.{v} (R ⧸ I) :=
  small_of_surjective Ideal.Quotient.mk_surjective


section

universe w

variable [UnivLE.{v, w}]

local instance hasExt_of_small [Small.{v} R] : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

open Limits in
lemma injective_of_quotients_ext_one_subsingleton [Small.{v} R] (M : ModuleCat.{v} R)
    (h : ∀ (I : Ideal R), Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v, u} (R ⧸ I))) M 1)) :
    Injective M := by
  rw [← Module.injective_iff_injective_object, ← Module.Baer.iff_injective]
  intro I g
  let Sf := (Shrink.linearEquiv.{v} R R).symm.toLinearMap.comp
    (I.subtype.comp (Shrink.linearEquiv.{v} R I).toLinearMap)
  let Sg := (Shrink.linearEquiv.{v} R (R ⧸ I)).symm.toLinearMap.comp
    ((Ideal.Quotient.mkₐ R I).toLinearMap.comp (Shrink.linearEquiv.{v} R R).toLinearMap)
  have exac : Function.Exact Sf Sg := by
    intro x
    have (z : R) : z ∈ I ↔ ∃ y, ↑((equivShrink ↥I).symm y) = z := by
      refine ⟨fun h ↦ ?_, fun ⟨y, hy⟩ ↦ by simp [← hy]⟩
      use (equivShrink I) ⟨z, h⟩
      simp
    simpa [Sf, Sg, Ideal.Quotient.eq_zero_iff_mem, AddEquiv.symm_apply_eq]
      using this ((equivShrink R).symm x)
  have inj : Function.Injective Sf := by
    simpa [Sf] using LinearEquiv.injective (Shrink.linearEquiv R I)
  have surj : Function.Surjective Sg := by
    simpa [Sg] using Ideal.Quotient.mk_surjective
  let S : ShortComplex (ModuleCat.{v} R) := {
    f := ModuleCat.ofHom Sf
    g := ModuleCat.ofHom Sg
    zero := by
      ext x
      simp [Function.Exact.apply_apply_eq_zero exac] }
  have S_exact : S.ShortExact := {
    exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac
    mono_f := (ModuleCat.mono_iff_injective _).mpr inj
    epi_g := (ModuleCat.epi_iff_surjective _).mpr surj }
  have : IsZero (AddCommGrp.of (Ext (ModuleCat.of R (Shrink.{v, u} (R ⧸ I))) M 1)) :=
    @AddCommGrp.isZero_of_subsingleton _ (h I)
  have exac := Ext.contravariant_sequence_exact₁' S_exact M 0 1 rfl
  have surj : Function.Surjective ((Ext.mk₀ S.f).precomp M (add_zero 0)) :=
    (AddCommGrp.epi_iff_surjective _).mp (exac.epi_f (this.eq_zero_of_tgt _))
  let f := g.comp (Shrink.linearEquiv R I).toLinearMap
  rcases surj (Ext.mk₀ (ModuleCat.ofHom f)) with ⟨f', hf'⟩
  simp only [Ext.bilinearComp_apply_apply] at hf'
  rw [← Ext.mk₀_addEquiv₀_apply f', Ext.mk₀_comp_mk₀] at hf'
  have eqcomp := congrArg ModuleCat.Hom.hom ((Ext.mk₀_bijective _ _).1 hf')
  simp only [← LinearMap.comp_assoc, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearEquiv.eq_comp_toLinearMap_iff, S, Sf, f] at eqcomp
  use (ModuleCat.Hom.hom (Ext.addEquiv₀ f')).comp (Shrink.linearEquiv R R).symm.toLinearMap
  intro x hx
  simp only [LinearMap.coe_comp, Function.comp_apply, ← eqcomp, LinearEquiv.coe_coe,
    Submodule.coe_subtype]
  congr

open Limits in
lemma ext_subsingleton_of_quotients [Small.{v} R] (M : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ I : Ideal R, Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M (n + 1))) :
    ∀ N : ModuleCat.{v} R, Subsingleton (Ext.{w} N M (n + 1)) := by
  induction n generalizing M
  · have : Injective M := injective_of_quotients_ext_one_subsingleton R M h
    intro N
    exact subsingleton_of_forall_eq 0 (fun e ↦ Ext.eq_zero_of_injective e)
  · rename_i n ih
    let ei : EnoughInjectives (ModuleCat R) := inferInstance
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

end

/-- The global (homological) dimension of a (commutative) ring defined as
the supremum of projective dimension over all modules. -/
noncomputable def globalDimension : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{v} R), projectiveDimension.{v} M

lemma globalDimension_eq_bot_iff [Small.{v} R] : globalDimension.{v} R = ⊥ ↔ Subsingleton R := by
  simp only [globalDimension, iSup_eq_bot, projectiveDimension_eq_bot_iff,
    ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun h ↦ ?_, fun h M ↦ Module.subsingleton R M⟩
  let _ := h (ModuleCat.of R (Shrink.{v} R))
  exact (equivShrink.{v} R).subsingleton

lemma globalDimension_le_iff (n : ℕ) : globalDimension.{v} R ≤ n ↔
    ∀ M : ModuleCat.{v} R, HasProjectiveDimensionLE M n := by
  simp [globalDimension, projectiveDimension_le_iff]

local instance hasExt_standard :
  HasExt.{max (max (v + 1) u) v, v, max (v + 1) u} (ModuleCat.{v} R) :=
  CategoryTheory.HasExt.standard (ModuleCat.{v} R)

lemma globalDimension_le_tfae [Small.{v} R] (n : ℕ) : [globalDimension.{v} R ≤ n,
    ∀ M : ModuleCat.{v} R, Module.Finite R M → HasProjectiveDimensionLE M n,
    ∀ m ≥ n + 1, ∀ (N M : ModuleCat.{v} R), Subsingleton (Ext N M m)].TFAE := by
  tfae_have 1 → 2 := by
    simpa only [globalDimension, iSup_le_iff, projectiveDimension_le_iff]
      using fun h M _ ↦ h M
  tfae_have 2 → 3 := by
    intro h m ge N M
    have eq : m - 1 + 1 = m := by omega
    have (I : Ideal R) :
      Subsingleton (Ext (ModuleCat.of R (Shrink.{v, u} (R ⧸ I))) M (m - 1 + 1)) := by
      simpa only [eq] using (h (ModuleCat.of R (Shrink.{v, u} (R ⧸ I)))
        (Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm)).1 m ge (Y := M)
    rw [← eq]
    exact ext_subsingleton_of_quotients.{v, u, max u (v + 1)} R M (m - 1) this N
  tfae_have 3 → 1 := by
    intro h
    simp only [globalDimension, iSup_le_iff, projectiveDimension_le_iff]
    intro M
    exact ⟨fun m hm {N} ↦ h m hm M N⟩
  tfae_finish

lemma globalDimension_eq_sup_projectiveDimension_finite [Small.{v, u} R] : globalDimension.{v} R =
    ⨆ (M : ModuleCat.{v} R), ⨆ (_ : Module.Finite R M), projectiveDimension.{v} M := by
  have aux (n : ℕ): globalDimension.{v} R ≤ n ↔
    ⨆ (M : ModuleCat.{v} R), ⨆ (_ : Module.Finite R M), projectiveDimension.{v} M ≤ n := by
    simpa only [iSup_le_iff, projectiveDimension_le_iff] using (globalDimension_le_tfae R n).out 0 1
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  by_cases eqbot : N = ⊥
  · simp only [eqbot, le_bot_iff, globalDimension_eq_bot_iff, iSup_eq_bot,
      projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun h M _ ↦ Module.subsingleton R M, fun h ↦ ?_⟩
    let _ := h (ModuleCat.of R (Shrink.{v} R)) (Module.Finite.equiv (Shrink.linearEquiv R R).symm)
    exact (equivShrink.{v} R).subsingleton
  · by_cases eqtop : N.unbot eqbot = ⊤
    · have : N = ⊤ := (WithBot.coe_unbot _ eqbot).symm.trans (WithBot.coe_inj.mpr eqtop)
      simp [this]
    · let n := (N.unbot eqbot).toNat
      have : N = n := (WithBot.coe_unbot _ eqbot).symm.trans
        (WithBot.coe_inj.mpr (ENat.coe_toNat eqtop).symm)
      simpa only [this] using aux n

lemma globalDimension_eq_iSup_loclization_prime [Small.{v, u} R] [IsNoetherianRing R] :
    globalDimension.{v} R =
    ⨆ (p : PrimeSpectrum R), globalDimension.{v} (Localization.AtPrime p.1) := by
  apply le_antisymm
  · simp only [globalDimension_eq_sup_projectiveDimension_finite, iSup_le_iff]
    intro M fin
    simp only [projectiveDimension_eq_iSup_localizedModule_prime M, iSup_le_iff]
    intro p
    exact le_trans (le_iSup _ (M.localizedModule p.asIdeal.primeCompl))
      (le_iSup (fun (p : PrimeSpectrum R) ↦ globalDimension (Localization.AtPrime p.asIdeal)) p)
  · simp only [iSup_le_iff, globalDimension]
    intro p Mp
    let _ : Module R Mp := Module.compHom Mp (algebraMap R (Localization.AtPrime p.1))
    have : IsScalarTower R (Localization.AtPrime p.1) Mp :=
      ModuleCat.Algebra.instIsScalarTowerCarrier
    apply le_trans (le_trans _ (projectiveDimension_le_projectiveDimension_of_isLocalizedModule
      p.1.primeCompl (ModuleCat.of R Mp)))
      (le_iSup (fun (M : ModuleCat.{v} R) ↦ projectiveDimension M) (ModuleCat.of R Mp))
    let _ := isLocalizedModule_id p.1.primeCompl Mp (Localization.AtPrime p.1)
    exact le_of_eq (projectiveDimension_eq_of_iso (LinearEquiv.extendScalarsOfIsLocalization
      p.1.primeCompl (Localization.AtPrime p.1) (IsLocalizedModule.linearEquiv p.1.primeCompl
      ((ModuleCat.of R Mp).localizedModule_mkLinearMap p.1.primeCompl)
      LinearMap.id)).symm.toModuleIso)

lemma globalDimension_eq_iSup_loclization_maximal [Small.{v, u} R] [IsNoetherianRing R] :
    globalDimension.{v} R =
    ⨆ (p : MaximalSpectrum R), globalDimension.{v} (Localization.AtPrime p.1) := by
  apply le_antisymm
  · simp only [globalDimension_eq_sup_projectiveDimension_finite, iSup_le_iff]
    intro M fin
    simp only [projectiveDimension_eq_iSup_localizedModule_maximal M, iSup_le_iff]
    intro p
    exact le_trans (le_iSup _ (M.localizedModule p.asIdeal.primeCompl))
      (le_iSup (fun (p : MaximalSpectrum R) ↦ globalDimension (Localization.AtPrime p.asIdeal)) p)
  · simp only [iSup_le_iff, globalDimension]
    intro p Mp
    let _ : Module R Mp := Module.compHom Mp (algebraMap R (Localization.AtPrime p.1))
    have : IsScalarTower R (Localization.AtPrime p.1) Mp :=
      ModuleCat.Algebra.instIsScalarTowerCarrier
    apply le_trans (le_trans _ (projectiveDimension_le_projectiveDimension_of_isLocalizedModule
      p.1.primeCompl (ModuleCat.of R Mp)))
      (le_iSup (fun (M : ModuleCat.{v} R) ↦ projectiveDimension M) (ModuleCat.of R Mp))
    let _ := isLocalizedModule_id p.1.primeCompl Mp (Localization.AtPrime p.1)
    exact le_of_eq (projectiveDimension_eq_of_iso (LinearEquiv.extendScalarsOfIsLocalization
      p.1.primeCompl (Localization.AtPrime p.1) (IsLocalizedModule.linearEquiv p.1.primeCompl
      ((ModuleCat.of R Mp).localizedModule_mkLinearMap p.1.primeCompl)
      LinearMap.id)).symm.toModuleIso)

end GlobalDimension
