/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!

# Projective Dimension in ModuleCat

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v v' u u'

variable {R : Type u} [CommRing R]

open CategoryTheory Abelian Module

namespace ModuleCat

section

variable [Small.{v} R] {R' : Type u'} [CommRing R'] [Small.{v'} R'] (e : R ≃+* R')

variable {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R'}

attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma hasProjectiveDimensionLE_of_semiLinearEquiv (e' : M ≃ₛₗ[RingHomClass.toRingHom e] N)
    (n : ℕ) [HasProjectiveDimensionLE M n] : HasProjectiveDimensionLE N n := by
  induction n generalizing M N e' with
  | zero =>
    have : HasProjectiveDimensionLE M 0 := ‹_›
    simp only [HasProjectiveDimensionLE, zero_add] at this ⊢
    rw [← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective] at this ⊢
    exact Projective.of_equiv e'
  | succ n ih =>
    let S := M.projectiveShortComplex
    let S' := N.projectiveShortComplex
    have S_exact := M.shortExact_projectiveShortComplex
    have S'_exact := N.shortExact_projectiveShortComplex
    let eR : Shrink.{v} R ≃ₛₗ[RingHomClass.toRingHom e] Shrink.{v'} R' :=
      ((Shrink.linearEquiv R R).trans e.toSemilinearEquiv).trans (Shrink.linearEquiv R' R').symm
    let e2 : S.X₂ ≃ₛₗ[RingHomClass.toRingHom e] S'.X₂ :=
      (Finsupp.mapDomain.linearEquiv (Shrink R) R e').trans (Finsupp.mapRange.linearEquiv eR)
    have comm : S'.g.hom.comp e2.toLinearMap = e'.toLinearMap.comp S.g.hom := by
      ext m r
      simp [S, S', e2, eR, Basis.constr_apply, map_smulₛₗ]
    have : S.g.hom.ker = Submodule.comap e2.toLinearMap S'.g.hom.ker := by
      rw [← LinearMap.ker_comp, comm, LinearEquiv.ker_comp]
    rw [Submodule.comap_equiv_eq_map_symm] at this
    let eker : S.X₁ ≃ₛₗ[RingHomClass.toRingHom e] S'.X₁ :=
      (LinearEquiv.ofEq _ _ this).trans (e2.symm.submoduleMap S'.g.hom.ker).symm
    have := (S_exact.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp ‹_›
    exact (S'_exact.hasProjectiveDimensionLT_X₃_iff n inferInstance).mpr (ih eker)

@[deprecated (since := "2026-04-04")]
alias _root_.CategoryTheory.hasProjectiveDimensionLE_of_semiLinearEquiv :=
  hasProjectiveDimensionLE_of_semiLinearEquiv

attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma projectiveDimension_eq_of_semiLinearEquiv (e' : M ≃ₛₗ[RingHomClass.toRingHom e] N) :
    projectiveDimension M = projectiveDimension N := by
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot => simpa [projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton] using
      e'.subsingleton_congr
  | coe n =>
    induction n with
    | top => simp
    | coe n =>
      norm_cast
      simp only [projectiveDimension_le_iff]
      exact ⟨fun h ↦ hasProjectiveDimensionLE_of_semiLinearEquiv e e' n,
        fun h ↦ hasProjectiveDimensionLE_of_semiLinearEquiv e.symm e'.symm n⟩

@[deprecated (since := "2026-04-04")]
alias _root_.CategoryTheory.projectiveDimension_eq_of_semiLinearEquiv :=
  projectiveDimension_eq_of_semiLinearEquiv

end

section

variable [Small.{v} R] [Small.{v'} R] {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R}

lemma hasProjectiveDimensionLE_of_linearEquiv (e : M ≃ₗ[R] N)
    (n : ℕ) [HasProjectiveDimensionLE M n] : HasProjectiveDimensionLE N n :=
  hasProjectiveDimensionLE_of_semiLinearEquiv (RingEquiv.refl R) e n

@[deprecated (since := "2026-04-04")]
alias _root_.CategoryTheory.hasProjectiveDimensionLE_of_linearEquiv :=
  hasProjectiveDimensionLE_of_linearEquiv

lemma projectiveDimension_eq_of_linearEquiv (e : M ≃ₗ[R] N) :
    projectiveDimension M = projectiveDimension N :=
  projectiveDimension_eq_of_semiLinearEquiv (M := M) (N := N) (RingEquiv.refl R) e

@[deprecated (since := "2026-04-04")]
alias _root_.CategoryTheory.projectiveDimension_eq_of_linearEquiv :=
  projectiveDimension_eq_of_linearEquiv

end

lemma projectiveDimension_eq_zero_of_projective (M : ModuleCat.{v} R) [Nontrivial M]
    [Projective M] : projectiveDimension M = 0 := by
  simpa [projectiveDimension_eq_zero_iff, ModuleCat.isZero_iff_subsingleton,
    not_subsingleton_iff_nontrivial] using ⟨‹_›, ‹_›⟩

end ModuleCat
