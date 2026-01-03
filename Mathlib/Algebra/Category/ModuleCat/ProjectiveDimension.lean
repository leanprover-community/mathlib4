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

attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma hasProjectiveDimensionLE_of_semiLinearEquiv [Small.{v} R] [Small.{v'} R']
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R'} (e' : M ≃ₛₗ[RingHomClass.toRingHom e] N)
    (n : ℕ) [h : HasProjectiveDimensionLE M n] : HasProjectiveDimensionLE N n := by
  induction n generalizing M N e'
  · simp only [HasProjectiveDimensionLE, zero_add,
      ← projective_iff_hasProjectiveDimensionLT_one] at h ⊢
    rw [← IsProjective.iff_projective] at h ⊢
    exact Projective.of_ringEquiv e e'
  · rename_i n ih
    let b : Basis M R (M →₀ Shrink.{v} R) :=
      ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)⟩
    let f := (b.constr ℕ _root_.id)
    have surjf : Function.Surjective f :=
      fun m ↦ ⟨Finsupp.single m 1, by simp [f, b, Module.Basis.constr_apply]⟩
    let b' : Basis N R' (N →₀ Shrink.{v'} R') :=
      ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v'} R' R')⟩
    let eR : Shrink.{v} R ≃ₛₗ[RingHomClass.toRingHom e] Shrink.{v'} R' :=
      ((Shrink.linearEquiv R R).trans e.toSemilinearEquiv).trans (Shrink.linearEquiv R' R').symm
    let eP : (M →₀ Shrink.{v} R) ≃ₛₗ[RingHomClass.toRingHom e] (N →₀ Shrink.{v'} R') :=
      (Finsupp.mapDomain.linearEquiv (Shrink R) R e').trans (Finsupp.mapRange.linearEquiv eR)
    let g := ((e'.toLinearMap.comp f).comp eP.symm.toLinearMap)
    have surjg : Function.Surjective g := by simpa [g] using surjf
    let S : ShortComplex (ModuleCat.{v} R) := f.shortComplexKer
    have S_exact : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
    let S' : ShortComplex (ModuleCat.{v'} R') := g.shortComplexKer
    have S'_exact : S'.ShortExact := LinearMap.shortExact_shortComplexKer surjg
    have : HasProjectiveDimensionLT S.X₁ (n + 1) :=
      (S_exact.hasProjectiveDimensionLT_X₃_iff n (ModuleCat.projective_of_free b)).mp h
    have ker1 (x : LinearMap.ker f) : eP x.1 ∈ LinearMap.ker g := by
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        EmbeddingLike.map_eq_zero_iff, g]
      rw [← LinearMap.mem_ker.mp x.2]
      congr
      exact eP.symm_apply_apply x.1
    have ker2 (x : LinearMap.ker g) : eP.symm x.1 ∈ LinearMap.ker f := by
      have := LinearMap.mem_ker.mp x.2
      simp only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        EmbeddingLike.map_eq_zero_iff] at this
      exact this
    let eker' : LinearMap.ker f ≃ₛₗ[RingHomClass.toRingHom e] LinearMap.ker g := {
      toFun x := ⟨eP x.1, ker1 x⟩
      map_add' x y := by simp
      map_smul' r x := SetCoe.ext (eP.map_smulₛₗ _ _)
      invFun x := ⟨eP.symm x.1, ker2 x⟩
      left_inv := by
        rw [Function.leftInverse_iff_comp]
        exact funext (fun x ↦ SetCoe.ext (eP.symm_apply_apply x.1))
      right_inv := by
        rw [Function.rightInverse_iff_comp]
        exact funext (fun x ↦ SetCoe.ext (eP.apply_symm_apply x.1)) }
    let eker : S.X₁ ≃ₛₗ[RingHomClass.toRingHom e] S'.X₁ := eker'
    apply (S'_exact.hasProjectiveDimensionLT_X₃_iff n (ModuleCat.projective_of_free b')).mpr
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
