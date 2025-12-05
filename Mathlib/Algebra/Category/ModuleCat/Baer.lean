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
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Category Language Baer Criterion
-/

@[expose] public section

universe u u' v v'

variable {R : Type u} [CommRing R]

open CategoryTheory Abelian

section

lemma ext_quotient_one_subsingleton_iff [Small.{v} R] (M : ModuleCat.{v} R) (I : Ideal R) :
    Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M 1) ↔
    ∀ g : I →ₗ[R] M, ∃ g' : R →ₗ[R] M, ∀ (x : R) (mem : x ∈ I), g' x = g ⟨x, mem⟩ := by
  let Sf := (Shrink.linearEquiv.{v} R R).symm.toLinearMap.comp
    (I.subtype.comp (Shrink.linearEquiv.{v} R I).toLinearMap)
  let Sg := (Shrink.linearEquiv.{v} R (R ⧸ I)).symm.toLinearMap.comp
    ((Ideal.Quotient.mkₐ R I).toLinearMap.comp (Shrink.linearEquiv.{v} R R).toLinearMap)
  have exac : Function.Exact Sf Sg := by
    intro x
    have (z : R) : z ∈ I ↔ ∃ y, ↑((equivShrink I).symm y) = z := by
      refine ⟨fun h ↦ ⟨(equivShrink I) ⟨z, h⟩, by simp⟩, fun ⟨y, hy⟩ ↦ by simp [← hy]⟩
    simpa [Sf, Sg, Ideal.Quotient.eq_zero_iff_mem, AddEquiv.symm_apply_eq]
      using this ((equivShrink R).symm x)
  have inj : Function.Injective Sf := by simpa [Sf] using (Shrink.linearEquiv R I).injective
  have surj : Function.Surjective Sg := by simpa [Sg] using Ideal.Quotient.mk_surjective
  let S : ShortComplex (ModuleCat.{v} R) := {
    f := ModuleCat.ofHom Sf
    g := ModuleCat.ofHom Sg
    zero := by
      ext x
      simp [exac.apply_apply_eq_zero] }
  have S_exact : S.ShortExact := {
    exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac
    mono_f := (ModuleCat.mono_iff_injective _).mpr inj
    epi_g := (ModuleCat.epi_iff_surjective _).mpr surj }
  have : Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M 1) ↔
    Function.Surjective ((Ext.mk₀ S.f).precomp M (add_zero 0)) := by
    apply Iff.trans _ ((Ext.contravariant_sequence_exact₁' S_exact M 0 1 rfl).epi_f_iff.symm.trans
      (AddCommGrpCat.epi_iff_surjective _))
    refine ⟨fun h ↦ ((@AddCommGrpCat.isZero_of_subsingleton _ h).eq_zero_of_tgt _), fun h ↦ ?_⟩
    exact AddCommGrpCat.subsingleton_of_isZero ((Ext.contravariant_sequence_exact₃' S_exact M 0 1
      rfl).isZero_X₂ h ((@AddCommGrpCat.isZero_of_subsingleton _
      (Ext.subsingleton_of_projective S.X₂ M 0)).eq_zero_of_tgt _))
  apply this.trans ⟨fun h ↦ fun g ↦ ?_, fun h ↦ fun e ↦ ?_⟩
  · let f := g.comp (Shrink.linearEquiv R I).toLinearMap
    rcases h (Ext.mk₀ (ModuleCat.ofHom f)) with ⟨f', hf'⟩
    rw [Ext.bilinearComp_apply_apply, ← Ext.mk₀_addEquiv₀_apply f', Ext.mk₀_comp_mk₀] at hf'
    have eqcomp := congrArg ModuleCat.Hom.hom ((Ext.mk₀_bijective _ _).1 hf')
    simp only [← LinearMap.comp_assoc, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearEquiv.eq_comp_toLinearMap_iff, S, Sf, f] at eqcomp
    use (ModuleCat.Hom.hom (Ext.addEquiv₀ f')).comp (Shrink.linearEquiv R R).symm.toLinearMap
    intro x hx
    simp only [LinearMap.coe_comp, Function.comp_apply, ← eqcomp, LinearEquiv.coe_coe,
      Submodule.coe_subtype]
    rfl
  · rcases h ((Ext.addEquiv₀ e).hom.comp (Shrink.linearEquiv R I).symm.toLinearMap) with ⟨g', hg'⟩
    use Ext.mk₀ (ModuleCat.ofHom (g'.comp (Shrink.linearEquiv R R).toLinearMap))
    rw [Ext.bilinearComp_apply_apply, Ext.mk₀_comp_mk₀, ← Ext.mk₀_addEquiv₀_apply e]
    congr
    ext x
    have eq : (Shrink.linearEquiv R R) (Sf x) = ((Shrink.linearEquiv R I) x).1 :=
      (Shrink.linearEquiv R R).apply_symm_apply _
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, S, eq, hg' _ ((Shrink.linearEquiv R I) x).2]
    exact congrArg _ ((Shrink.linearEquiv R I).symm_apply_apply _)

lemma injective_of_subsingleton_ext_quotient_one [Small.{v} R] (M : ModuleCat.{v} R)
    (h : ∀ (I : Ideal R), Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M 1)) :
    Injective M := by
  rw [← Module.injective_iff_injective_object, ← Module.Baer.iff_injective]
  exact fun I ↦ (ext_quotient_one_subsingleton_iff M I).mp (h I)

open Limits in
lemma ext_subsingleton_of_quotients' [Small.{v} R] (M : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ I : Ideal R, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M (n + 1))) :
    ∀ N : ModuleCat.{v} R, Subsingleton (Ext N M (n + 1)) := by
  induction n generalizing M
  · have : Injective M := injective_of_subsingleton_ext_quotient_one M h
    intro N
    exact subsingleton_of_forall_eq 0 (fun e ↦ Ext.eq_zero_of_injective e)
  · rename_i n ih
    let ei : EnoughInjectives (ModuleCat R) := inferInstance
    rcases ei.1 M with ⟨ip⟩
    let S := ip.shortComplex
    have (N : ModuleCat R) : Subsingleton (Ext N M (n + 2)) ↔
      Subsingleton (Ext N (cokernel ip.3) (n + 1)) := by
      let _ := Ext.subsingleton_of_injective N S.X₂
      have := (Ext.covariantSequence_exact N ip.shortComplex_shortExact (n + 1) (n + 2)
        rfl).isIso_map' 1 (by decide) ((AddCommGrpCat.of _).isZero_of_subsingleton.eq_zero_of_src _)
        ((AddCommGrpCat.of _).isZero_of_subsingleton.eq_zero_of_tgt  _)
      exact (@asIso _ _ _ _ _ this).addCommGroupIsoToAddEquiv.subsingleton_congr.symm
    simp only [this] at h ⊢
    exact ih (cokernel ip.3) h

lemma ext_subsingleton_of_quotients [Small.{v} R] (M : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ I : Ideal R, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M n)) :
    ∀ N : ModuleCat.{v} R, Subsingleton (Ext N M n) := by
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
