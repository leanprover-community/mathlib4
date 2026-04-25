/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Category Language Baer Criterion
-/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]

open CategoryTheory Abelian

namespace ModuleCat

set_option backward.isDefEq.respectTransparency false in
lemma ext_quotient_one_subsingleton_iff [Small.{v} R] (M : ModuleCat.{v} R) (I : Ideal R) :
    Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M 1) ↔
    ∀ g : I →ₗ[R] M, ∃ g' : R →ₗ[R] M, ∀ (x : R) (mem : x ∈ I), g' x = g ⟨x, mem⟩ := by
  have exact : Function.Exact I.subtype I.mkQ := LinearMap.exact_subtype_mkQ I
  let S := ModuleCat.shortComplexOfConj (Shrink.linearEquiv R I) (Shrink.linearEquiv R R)
    (Shrink.linearEquiv R (R ⧸ I)) _ _  exact.linearMap_comp_eq_zero
  have S_exact : S.ShortExact :=
    ModuleCat.shortComplexOfConj_shortExact _ _ _ _ _ exact I.subtype_injective I.mkQ_surjective
  have : Projective S.X₂ := by dsimp [S]; infer_instance
  have : Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M 1) ↔
    Function.Surjective ((Ext.mk₀ S.f).precomp M (add_zero 0)) := by
    apply Iff.trans _ ((Ext.contravariant_sequence_exact₁' S_exact M 0 1 rfl).epi_f_iff.symm.trans
      (AddCommGrpCat.epi_iff_surjective _))
    refine ⟨fun h ↦ ((@AddCommGrpCat.isZero_of_subsingleton _ h).eq_zero_of_tgt _), fun h ↦ ?_⟩
    exact AddCommGrpCat.subsingleton_of_isZero ((Ext.contravariant_sequence_exact₃' S_exact M 0 1
      rfl).isZero_X₂ h ((@AddCommGrpCat.isZero_of_subsingleton _
      (Ext.subsingleton_of_projective S.X₂ M 0)).eq_zero_of_tgt _))
  refine this.trans ⟨fun h ↦ fun g ↦ ?_, fun h ↦ fun e ↦ ?_⟩
  · obtain ⟨f', hf'⟩ := h (Ext.mk₀ (ModuleCat.ofHom (g.comp (Shrink.linearEquiv R I).toLinearMap)))
    rw [Ext.bilinearComp_apply_apply, ← Ext.mk₀_addEquiv₀_apply f', Ext.mk₀_comp_mk₀] at hf'
    use (Ext.addEquiv₀ f').hom.comp (Shrink.linearEquiv R R).symm.toLinearMap
    intro x hx
    have := ConcreteCategory.congr_hom ((Ext.mk₀_bijective _ _).1 hf')
      ((Shrink.linearEquiv R I).symm ⟨x, hx⟩)
    simpa [S]
  · obtain ⟨g', hg'⟩ := h ((Ext.addEquiv₀ e).hom.comp (Shrink.linearEquiv R I).symm.toLinearMap)
    use Ext.mk₀ (ModuleCat.ofHom (g'.comp (Shrink.linearEquiv R R).toLinearMap))
    rw [Ext.bilinearComp_apply_apply, Ext.mk₀_comp_mk₀, ← Ext.mk₀_addEquiv₀_apply e]
    congr
    ext x
    simp_all [S]

lemma injective_of_subsingleton_ext_quotient_one [Small.{v} R] (M : ModuleCat.{v} R)
    (h : ∀ (I : Ideal R), Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M 1)) :
    Injective M := by
  rw [← Module.injective_iff_injective_object, ← Module.Baer.iff_injective]
  exact fun I ↦ (ext_quotient_one_subsingleton_iff M I).mp (h I)

open Limits in
lemma hasInjectiveDimensionLE_of_quotients [Small.{v} R] (M : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ I : Ideal R, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M (n + 1))) :
    HasInjectiveDimensionLE M n := by
  induction n generalizing M with
  | zero =>
    have : Injective M := injective_of_subsingleton_ext_quotient_one M h
    infer_instance
  | succ n ih =>
    let ip : InjectivePresentation M := (EnoughInjectives.presentation M).some
    let S := ip.shortComplex
    have (N : ModuleCat R) : Subsingleton (Ext N M (n + 2)) ↔
        Subsingleton (Ext N (cokernel ip.3) (n + 1)) := by
      have := Ext.subsingleton_of_injective N S.X₂
      have : IsIso (AddCommGrpCat.ofHom (ip.shortExact_shortComplex.extClass.postcomp N rfl)) :=
        (Ext.covariantSequence_exact N ip.shortExact_shortComplex (n + 1) (n + 2) rfl).isIso_map'
          1 (by decide) ((AddCommGrpCat.of _).isZero_of_subsingleton.eq_zero_of_src _)
            ((AddCommGrpCat.of _).isZero_of_subsingleton.eq_zero_of_tgt  _)
      exact (asIso (AddCommGrpCat.ofHom (ip.shortExact_shortComplex.extClass.postcomp N
        rfl))).addCommGroupIsoToAddEquiv.subsingleton_congr.symm
    simp only [this] at h
    exact (ip.shortExact_shortComplex.hasInjectiveDimensionLT_X₃_iff n inferInstance).mp (ih _ h)

lemma hasInjectiveDimensionLT_of_quotients [Small.{v} R] (M : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ I : Ideal R, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M n)) :
    HasInjectiveDimensionLT M n := by
  match n with
  | 0 =>
    apply Limits.IsZero.hasInjectiveDimensionLT_zero
    rw [ModuleCat.isZero_iff_subsingleton]
    refine ((Ext.homEquiv₀.trans ModuleCat.homEquiv).trans ?_).subsingleton_congr.mp (h ⊥)
    exact ((((Shrink.linearEquiv _ _).trans
      (Submodule.quotEquivOfEqBot _ rfl)).congrLeft M R).trans
        (LinearMap.ringLmapEquivSelf R R M)).toEquiv
  | n + 1 => exact hasInjectiveDimensionLE_of_quotients M n  h

end ModuleCat
