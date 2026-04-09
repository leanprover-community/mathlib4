/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Baer
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Finiteness.Small
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

1. Reduce vanishing of all `Ext N M i`, `i ≥ n + 1` to vanishing of `Ext N M (n + 1)`.
2. Prove that global dimension is invariant of universe if assuming `Small.{v} R`.

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
    ∀ (N M : ModuleCat.{v} R), Subsingleton (Ext N M (n + 1)),
    ∀ M : ModuleCat.{v} R, HasInjectiveDimensionLE M n].TFAE := by
  tfae_have 1 → 2 := by
    simpa only [globalDimension, iSup_le_iff, projectiveDimension_le_iff]
      using fun h M _ ↦ h M
  tfae_have 2 → 3 := fun h N M ↦ (ModuleCat.hasInjectiveDimensionLT_of_quotients M (n + 1)
    (fun I ↦ ((h (ModuleCat.of R (Shrink.{v} (R ⧸ I)))).subsingleton _ _ _ (le_refl _)
    M))).subsingleton _ _ _ (le_refl _) N
  tfae_have 3 → 1 := by
    intro h
    simp only [globalDimension, iSup_le_iff, projectiveDimension_le_iff]
    exact fun M ↦ hasProjectiveDimensionLT_of_enoughInjectives M _ (h M)
  tfae_have 3 → 4 := fun h M ↦ hasInjectiveDimensionLT_of_enoughProjectives M _ (h · M)
  tfae_have 4 → 3 := fun h N M ↦ (h M).subsingleton _ _ _ (le_refl _) N
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

/-- Global dimension is invariant of universe level when assume ring itself small. -/
lemma globalDimension_eq_of_small [Small.{v} R] :
    globalDimension.{v} R = globalDimension.{u} R := by
  apply le_antisymm
  · rw [globalDimension_eq_sup_projectiveDimension_finite]
    simp only [iSup_le_iff]
    intro M hM
    let := Module.Finite.small.{u} R M
    let e : M ≃ₗ[R] ModuleCat.of R (Shrink.{u} M) := (Shrink.linearEquiv R M).symm
    rw [ModuleCat.projectiveDimension_eq_of_linearEquiv e]
    exact le_iSup _ _
  · rw [globalDimension_eq_sup_projectiveDimension_finite]
    simp only [iSup_le_iff]
    intro M hM
    let := Module.Finite.small.{v} R M
    let e : M ≃ₗ[R] ModuleCat.of R (Shrink.{v} M) := (Shrink.linearEquiv R M).symm
    rw [ModuleCat.projectiveDimension_eq_of_linearEquiv e]
    exact le_iSup _ _

universe u' in
attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma globalDimension_eq_of_ringEquiv (R' : Type u') [CommRing R']
    (e : R ≃+* R') : globalDimension.{u} R = globalDimension.{u'} R' := by
  apply le_antisymm
  · rw [globalDimension_eq_sup_projectiveDimension_finite]
    simp only [iSup_le_iff]
    intro M hM
    let : Small.{u'} R := Small.mk' e.toEquiv
    let := Module.Finite.small.{u'} R M
    let : Module R' (Shrink.{u'} M) := Module.compHom _ e.symm.toRingHom
    let e' : (ModuleCat.of R' (Shrink.{u'} M)) ≃ₛₗ[RingHomClass.toRingHom e.symm] M  := {
      __ := (Shrink.linearEquiv R M)
      map_smul' r m := map_smul (Shrink.linearEquiv R M) (e.symm r) _ }
    rw [← ModuleCat.projectiveDimension_eq_of_semiLinearEquiv e.symm e']
    exact le_iSup _ _
  · rw [globalDimension_eq_sup_projectiveDimension_finite]
    simp only [iSup_le_iff]
    intro M hM
    let : Small.{u} R' := Small.mk' e.symm.toEquiv
    let := Module.Finite.small.{u} R' M
    let : Module R (Shrink.{u} M) := Module.compHom _ e.toRingHom
    let e' : (ModuleCat.of R (Shrink.{u} M)) ≃ₛₗ[RingHomClass.toRingHom e] M  := {
      __ := (Shrink.linearEquiv R' M)
      map_smul' r m := map_smul (Shrink.linearEquiv R' M) (e r) _ }
    rw [← ModuleCat.projectiveDimension_eq_of_semiLinearEquiv e e']
    exact le_iSup _ _

variable {R} in
lemma globalDimension_localization_le [Small.{v} R] (S : Submonoid R) :
    globalDimension.{v} (Localization S) ≤ globalDimension.{v} R := by
  simp only [iSup_le_iff, globalDimension]
  intro M
  let _ : Module R M := Module.compHom M (algebraMap R (Localization S))
  have : IsScalarTower R (Localization S) M := IsScalarTower.of_compHom _ _ _
  apply (le_of_eq_of_le _ (ModuleCat.projectiveDimension_le_projectiveDimension_of_isLocalizedModule
    S (ModuleCat.of R M))).trans (le_iSup _ (ModuleCat.of R M))
  let _ := isLocalizedModule_id S M (Localization S)
  exact (projectiveDimension_eq_of_iso (LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.linearEquiv S ((ModuleCat.of R M).localizedModuleMkLinearMap S)
    LinearMap.id)).symm.toModuleIso)

lemma globalDimension_eq_iSup_loclization_prime [Small.{v} R] [IsNoetherianRing R] :
    globalDimension.{v} R =
    ⨆ (p : PrimeSpectrum R), globalDimension.{v} (Localization.AtPrime p.1) := by
  apply le_antisymm
  · simp only [globalDimension_eq_sup_projectiveDimension_finite, iSup_le_iff]
    intro M fin
    simp only [M.projectiveDimension_eq_iSup_localizedModule_prime, iSup_le_iff]
    intro p
    exact (le_iSup _ (M.localizedModule p.1.primeCompl)).trans
      (le_iSup (fun (p : PrimeSpectrum R) ↦ globalDimension (Localization.AtPrime p.1)) p)
  · refine iSup_le_iff.mpr (fun p ↦ ?_)
    exact globalDimension_localization_le p.1.primeCompl

lemma globalDimension_eq_iSup_loclization_maximal [Small.{v} R] [IsNoetherianRing R] :
    globalDimension.{v} R =
    ⨆ (p : MaximalSpectrum R), globalDimension.{v} (Localization.AtPrime p.1) := by
  apply le_antisymm
  · simp only [globalDimension_eq_sup_projectiveDimension_finite, iSup_le_iff]
    intro M fin
    simp only [M.projectiveDimension_eq_iSup_localizedModule_maximal, iSup_le_iff]
    exact fun m ↦ (le_iSup _ (M.localizedModule m.1.primeCompl)).trans
      (le_iSup (fun (p : MaximalSpectrum R) ↦ globalDimension (Localization.AtPrime p.1)) m)
  · refine iSup_le_iff.mpr (fun m ↦ ?_)
    exact globalDimension_localization_le m.1.primeCompl

end GlobalDimension
