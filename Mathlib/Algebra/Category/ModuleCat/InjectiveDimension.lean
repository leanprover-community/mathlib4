/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Ulift
import Mathlib.CategoryTheory.Abelian.Injective.Dimension
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!

# Injective Dimension in ModuleCat

-/

universe u u' v v'

variable {R : Type u} [CommRing R]

open CategoryTheory Abelian

private instance small_of_quotient [Small.{v} R] (I : Ideal R) : Small.{v} (R ⧸ I) :=
  small_of_surjective Ideal.Quotient.mk_surjective

section

universe w

variable [UnivLE.{v, w}]

private instance hasExt_of_small [Small.{v} R] : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

open Limits in
lemma injective_of_subsingleton_ext_quotient_one [Small.{v} R] (M : ModuleCat.{v} R)
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
  have : IsZero (AddCommGrpCat.of (Ext (ModuleCat.of R (Shrink.{v, u} (R ⧸ I))) M 1)) :=
    @AddCommGrpCat.isZero_of_subsingleton _ (h I)
  have exac := Ext.contravariant_sequence_exact₁' S_exact M 0 1 rfl
  have surj : Function.Surjective ((Ext.mk₀ S.f).precomp M (add_zero 0)) :=
    (AddCommGrpCat.epi_iff_surjective _).mp (exac.epi_f (this.eq_zero_of_tgt _))
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
lemma ext_subsingleton_of_quotients' [Small.{v} R] (M : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ I : Ideal R, Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M (n + 1))) :
    ∀ N : ModuleCat.{v} R, Subsingleton (Ext.{w} N M (n + 1)) := by
  induction n generalizing M
  · have : Injective M := injective_of_subsingleton_ext_quotient_one M h
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
      have (m : ℕ) : Subsingleton (AddCommGrpCat.of (Ext N S.X₂ (m + 1))) :=
        subsingleton_of_forall_eq 0 Ext.eq_zero_of_injective
      have := ComposableArrows.Exact.isIso_map'
        (Ext.covariantSequence_exact N S_exact (n + 1) (n + 1 + 1) rfl) 1 (by decide)
        (IsZero.eq_zero_of_src (AddCommGrpCat.of (Ext N S.X₂ (n + 1))).isZero_of_subsingleton _)
        (IsZero.eq_zero_of_tgt (AddCommGrpCat.of (Ext N S.X₂ (n + 1 + 1))).isZero_of_subsingleton _)
      exact (@asIso _ _ _ _ _ this).addCommGroupIsoToAddEquiv.subsingleton_congr.symm
    simp only [this] at h ⊢
    exact ih (cokernel f) h

lemma ext_subsingleton_of_quotients [Small.{v} R] (M : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ I : Ideal R, Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M n)) :
    ∀ N : ModuleCat.{v} R, Subsingleton (Ext.{w} N M n) := by
  match n with
  | 0 =>
    let e₀ := (Shrink.linearEquiv R (R ⧸ (⊥ : Ideal R))).trans
      (AlgEquiv.quotientBot R R).toLinearEquiv
    have := (Ext.homEquiv₀.subsingleton_congr.mp (h ⊥))
    rw [ModuleCat.homAddEquiv.subsingleton_congr,
      ((e₀.congrLeft M R).trans (LinearMap.ringLmapEquivSelf R R M)).subsingleton_congr,
      ← ModuleCat.isZero_iff_subsingleton] at this
    intro N
    rw [Ext.homEquiv₀.subsingleton_congr]
    exact subsingleton_of_forall_eq 0 (fun y ↦ Limits.IsZero.eq_zero_of_tgt this y)
  | n + 1 => exact ext_subsingleton_of_quotients' M n  h

end

namespace CategoryTheory

section

lemma hasInjectiveDimensionLT_of_linearEquiv [Small.{v} R] [Small.{v'} R]
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R}
    (e' : M ≃ₗ[R] N) (n : ℕ) [HasInjectiveDimensionLT M n] :
    HasInjectiveDimensionLT N n := by
  apply (hasInjectiveDimensionLT_iff.{v'} _ n).mpr (fun i hi L x ↦ ?_)
  apply @Subsingleton.eq_zero _ _ ?_ x
  apply ext_subsingleton_of_quotients N i (fun I ↦ ?_)
  let e'' : (ModuleCat.of R (Shrink.{v} (R ⧸ I))) ≃ₗ[R] (ModuleCat.of R (Shrink.{v'} (R ⧸ I))) :=
    (Shrink.linearEquiv.{v} R (R ⧸ I)).trans (Shrink.linearEquiv.{v'} R (R ⧸ I)).symm
  rw [← (ModuleCat.extLinearEquivOfLinearEquiv.{v, v'} e'' e' i).subsingleton_congr]
  exact HasInjectiveDimensionLT.subsingleton.{v} M n i hi _

lemma injectiveDimension_eq_of_linearEquiv [Small.{v} R] [Small.{v'} R]
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R} (e : M ≃ₗ[R] N) :
    injectiveDimension M = injectiveDimension N := by
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot => simpa [injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton] using
      e.subsingleton_congr
  | coe n =>
    induction n with
    | top => simp
    | coe n =>
      norm_cast
      simp only [injectiveDimension_le_iff]
      refine ⟨fun h ↦ hasInjectiveDimensionLT_of_linearEquiv e (n + 1),
        fun h ↦ hasInjectiveDimensionLT_of_linearEquiv e.symm (n + 1)⟩

end

section

variable {R' : Type u'} [CommRing R'] (e : R ≃+* R')

lemma hasInjectiveDimensionLT_of_semiLinearEquiv [Small.{v} R] [Small.{v'} R']
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R'}
    (e' : letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
          letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
          M ≃ₛₗ[e.toRingHom] N) (n : ℕ) [HasInjectiveDimensionLT M n] :
    HasInjectiveDimensionLT N n := by
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
  apply (hasInjectiveDimensionLT_iff.{v'} _ n).mpr (fun i hi L x ↦ ?_)
  apply @Subsingleton.eq_zero _ _ ?_ x
  apply ext_subsingleton_of_quotients N i (fun I ↦ ?_)
  let e''' : (R ⧸ (I.comap e)) ≃ₛₗ[e.toRingHom] (R' ⧸ I) := {
    __ := Ideal.quotientEquiv (I.comap e) I e (I.map_comap_eq_self_of_equiv e).symm
    map_smul' r x := by
      rcases Ideal.Quotient.mk_surjective x with ⟨y, hy⟩
      simp [Ideal.quotientMap, ← hy, Algebra.smul_def] }
  let e'' : (ModuleCat.of R (Shrink.{v} (R ⧸ (I.comap e)))) ≃ₛₗ[e.toRingHom]
    (ModuleCat.of R' (Shrink.{v', u'} (R' ⧸ I))) :=
    ((Shrink.linearEquiv.{v} R _).trans e''').trans (Shrink.linearEquiv.{v'} R' _).symm
  rw [(ModuleCat.extSemiLinearEquivOfSemiLinearEquiv.{v, v'} e e'' e' i).subsingleton_congr]
  exact HasInjectiveDimensionLT.subsingleton.{v} M n i hi _

lemma injectiveDimension_eq_of_semiLinearEquiv [Small.{v} R] [Small.{v'} R']
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R'}
    (e' : letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
          letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
          M ≃ₛₗ[e.toRingHom] N) :
    injectiveDimension M = injectiveDimension N := by
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot => simpa [injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton] using
      e'.subsingleton_congr
  | coe n =>
    induction n with
    | top => simp
    | coe n =>
      norm_cast
      simp only [injectiveDimension_le_iff]
      refine ⟨fun h ↦ hasInjectiveDimensionLT_of_semiLinearEquiv e e' (n + 1),
        fun h ↦ hasInjectiveDimensionLT_of_semiLinearEquiv e.symm e'.symm (n + 1)⟩

end

end CategoryTheory
