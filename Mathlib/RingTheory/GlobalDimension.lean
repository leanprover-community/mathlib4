/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Baer
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-!
# The Global Dimension of a Ring

In this file, we define the global dimension of ring and proved some of its basic properties.

# Main definition and results

* `globalDimension` : The global (homological) dimension of a (commutative) ring defined as
  the supremum of projective dimension over all modules.

* `globalDimension_le_tfae` : For natrual number `n`, `globalDimension R ≤ n` iff all
  finitely generated modules over `R` has projective dimension not exceeding `n` iff for all
  `i ≥ n + 1`, `Ext N M i` vanish.

* `globalDimension_eq_sup_projectiveDimension_finite` : Global dimension is equal to the supremum of
  projective dimension over finitely generated modules.

# TODO

1. Take injective dimension into consideration in `globalDimension_le_tfae`.
2. Reduce vanishing of all `Ext N M i`, `i ≥ n + 1` to vanishing of `Ext N M (n + 1)`.
3. Prove that global dimension is invariant of universe if assuming `Small.{v} R`.

-/

@[expose] public section

universe v u

open CategoryTheory

section GlobalDimension

variable (R : Type u) [CommRing R]

open Abelian

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

lemma globalDimension_le_tfae [Small.{v} R] (n : ℕ) :
    [globalDimension.{v} R ≤ n,
    ∀ M : ModuleCat.{v} R, [Module.Finite R M] → HasProjectiveDimensionLE M n,
    ∀ m ≥ n + 1, ∀ (N M : ModuleCat.{v} R), Subsingleton (Ext N M m),
    ∀ M : ModuleCat.{v} R, HasInjectiveDimensionLE M n].TFAE := by
  tfae_have 1 → 2 := by
    simpa only [globalDimension, iSup_le_iff, projectiveDimension_le_iff]
      using fun h M _ ↦ h M
  tfae_have 2 → 3 := by
    exact fun h m ge N M ↦ ext_subsingleton_of_quotients M m
      (fun I ↦ ((h (ModuleCat.of R (Shrink.{v} (R ⧸ I)))).subsingleton _ _ _ ge M)) N
  tfae_have 3 → 1 := by
    intro h
    simp only [globalDimension, iSup_le_iff, projectiveDimension_le_iff]
    intro M
    exact HasProjectiveDimensionLT.mk (fun i hi {N} e ↦ @Subsingleton.eq_zero _ _ (h i hi M N) e)
  tfae_have 3 → 4 := by
    intro h M
    exact HasInjectiveDimensionLT.mk (fun i hi {N} e ↦ @Subsingleton.eq_zero _ _ (h i hi N M) e)
  tfae_have 4 → 3 := by
    intro h i hi N M
    exact (h M).subsingleton _ _ i hi N
  tfae_finish

lemma globalDimension_eq_sup_projectiveDimension_finite [Small.{v} R] : globalDimension.{v} R =
    ⨆ (M : ModuleCat.{v} R), ⨆ (_ : Module.Finite R M), projectiveDimension.{v} M := by
  have aux (n : ℕ): globalDimension.{v} R ≤ n ↔
    ⨆ (M : ModuleCat.{v} R), ⨆ (_ : Module.Finite R M), projectiveDimension.{v} M ≤ n := by
    simpa only [iSup_le_iff, projectiveDimension_le_iff] using (globalDimension_le_tfae R n).out 0 1
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, globalDimension_eq_bot_iff, iSup_eq_bot,
      projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun h M _ ↦ Module.subsingleton R M, fun h ↦ ?_⟩
    let _ := h (ModuleCat.of R (Shrink.{v} R)) (Module.Finite.equiv (Shrink.linearEquiv R R).symm)
    exact (equivShrink.{v} R).subsingleton
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n

lemma globalDimension_eq_sup_injectiveDimension [Small.{v} R] : globalDimension.{v} R =
    ⨆ (M : ModuleCat.{v} R), injectiveDimension.{v} M := by
  have aux (n : ℕ): globalDimension.{v} R ≤ n ↔
    ⨆ (M : ModuleCat.{v} R), injectiveDimension.{v} M ≤ n := by
    simpa only [iSup_le_iff, injectiveDimension_le_iff] using (globalDimension_le_tfae R n).out 0 3
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, globalDimension_eq_bot_iff, iSup_eq_bot,
      injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun h M ↦ Module.subsingleton R M, fun h ↦ ?_⟩
    let _ := h (ModuleCat.of R (Shrink.{v} R))
    exact (equivShrink.{v} R).subsingleton
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n

lemma globalDimension_eq_iSup_loclization_prime [Small.{v} R] [IsNoetherianRing R] :
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
    let _ : IsScalarTower R (Localization.AtPrime p.1) Mp := IsScalarTower.of_compHom _ _ _
    apply le_trans (le_trans _ (projectiveDimension_le_projectiveDimension_of_isLocalizedModule
      p.1.primeCompl (ModuleCat.of R Mp)))
      (le_iSup (fun (M : ModuleCat.{v} R) ↦ projectiveDimension M) (ModuleCat.of R Mp))
    let _ := isLocalizedModule_id p.1.primeCompl Mp (Localization.AtPrime p.1)
    exact le_of_eq (projectiveDimension_eq_of_iso (LinearEquiv.extendScalarsOfIsLocalization
      p.1.primeCompl (Localization.AtPrime p.1) (IsLocalizedModule.linearEquiv p.1.primeCompl
      ((ModuleCat.of R Mp).localizedModuleMkLinearMap p.1.primeCompl)
      LinearMap.id)).symm.toModuleIso)

lemma globalDimension_eq_iSup_loclization_maximal [Small.{v} R] [IsNoetherianRing R] :
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
    have : IsScalarTower R (Localization.AtPrime p.1) Mp := IsScalarTower.of_compHom _ _ _
    apply le_trans (le_trans _ (projectiveDimension_le_projectiveDimension_of_isLocalizedModule
      p.1.primeCompl (ModuleCat.of R Mp)))
      (le_iSup (fun (M : ModuleCat.{v} R) ↦ projectiveDimension M) (ModuleCat.of R Mp))
    let _ := isLocalizedModule_id p.1.primeCompl Mp (Localization.AtPrime p.1)
    exact le_of_eq (projectiveDimension_eq_of_iso (LinearEquiv.extendScalarsOfIsLocalization
      p.1.primeCompl (Localization.AtPrime p.1) (IsLocalizedModule.linearEquiv p.1.primeCompl
      ((ModuleCat.of R Mp).localizedModuleMkLinearMap p.1.primeCompl)
      LinearMap.id)).symm.toModuleIso)

end GlobalDimension
