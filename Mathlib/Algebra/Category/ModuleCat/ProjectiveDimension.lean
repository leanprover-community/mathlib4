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

@[expose] public section

universe v v' u u'

variable {R : Type u} [CommRing R]

open CategoryTheory Abelian Module

namespace CategoryTheory

section

variable {R' : Type u'} [CommRing R'] (e : R ≃+* R')

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma hasProjectiveDimensionLE_of_semiLinearEquiv [Small.{v} R] [Small.{v'} R']
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R'} (e' : M ≃ₛₗ[RingHomClass.toRingHom e] N)
    (n : ℕ) [h : HasProjectiveDimensionLE M n] : HasProjectiveDimensionLE N n := by
  induction n generalizing M N e' with
  | zero =>
    simp only [HasProjectiveDimensionLE, zero_add,
      ← projective_iff_hasProjectiveDimensionLT_one] at h ⊢
    rw [← IsProjective.iff_projective] at h ⊢
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
    let eker' : S.g.hom.ker ≃ₛₗ[RingHomClass.toRingHom e] S'.g.hom.ker :=
      (LinearEquiv.ofEq _ _ this).trans (e2.symm.submoduleMap S'.g.hom.ker).symm
    have : HasProjectiveDimensionLT S.X₁ (n + 1) :=
      (S_exact.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp h
    let eker : S.X₁ ≃ₛₗ[RingHomClass.toRingHom e] S'.X₁ := eker'
    apply (S'_exact.hasProjectiveDimensionLT_X₃_iff n inferInstance).mpr
    exact ih eker

attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma projectiveDimension_eq_of_semiLinearEquiv [Small.{v} R] [Small.{v'} R']
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R'} (e' : M ≃ₛₗ[RingHomClass.toRingHom e] N) :
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
      refine ⟨fun h ↦ hasProjectiveDimensionLE_of_semiLinearEquiv e e' n,
        fun h ↦ hasProjectiveDimensionLE_of_semiLinearEquiv e.symm e'.symm n⟩

end

section

lemma hasProjectiveDimensionLE_of_linearEquiv [Small.{v} R] [Small.{v'} R]
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R} (e' : M ≃ₗ[R] N)
    (n : ℕ) [h : HasProjectiveDimensionLE M n] : HasProjectiveDimensionLE N n :=
  hasProjectiveDimensionLE_of_semiLinearEquiv (RingEquiv.refl R) e' n

lemma projectiveDimension_eq_of_linearEquiv [Small.{v} R] [Small.{v'} R]
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R} (e : M ≃ₗ[R] N) :
    projectiveDimension M = projectiveDimension N :=
  projectiveDimension_eq_of_semiLinearEquiv (M := M) (N := N) (RingEquiv.refl R) e

end

end CategoryTheory
