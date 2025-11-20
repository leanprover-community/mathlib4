/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!

# Projective Dimension in ModuleCat

-/

@[expose] public section

universe u u' v v'

variable {R : Type u} [CommRing R]

open CategoryTheory Abelian

namespace CategoryTheory

section

open Module in
lemma hasProjectiveDimensionLE_of_linearEquiv [Small.{v} R] [Small.{v'} R]
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R}
    (e' : M ≃ₗ[R] N) (n : ℕ) [h : HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE N n := by
  induction n generalizing M N e'
  · simp only [HasProjectiveDimensionLE, zero_add,
      ← projective_iff_hasProjectiveDimensionLT_one] at h ⊢
    rw [← IsProjective.iff_projective] at h ⊢
    exact Module.Projective.of_equiv e'
  · rename_i n ih
    let PM := ModuleCat.of R (M →₀ Shrink.{v} R)
    let b : Basis M R (M →₀ Shrink.{v} R) :=
      ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)⟩
    let f : PM ⟶ M := ModuleCat.ofHom (b.constr ℕ _root_.id)
    have epif : Epi f := by
      rw [ModuleCat.epi_iff_range_eq_top, LinearMap.range_eq_top]
      refine fun m ↦ ⟨Finsupp.single m 1, ?_⟩
      simp only [ModuleCat.hom_ofHom, f, b]
      rw [Basis.constr_apply]
      simp [Finsupp.mapRange.linearEquiv]
    have surjf := (ModuleCat.epi_iff_surjective f).mp epif
    let _ : Projective PM := ModuleCat.projective_of_free b
    let PN := ModuleCat.of R (N →₀ Shrink.{v'} R)
    let b' : Basis N R (N →₀ Shrink.{v'} R) :=
      ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v'} R R)⟩
    let _ : Projective PN := ModuleCat.projective_of_free b'
    let eR : Shrink.{v} R ≃ₗ[R] Shrink.{v'} R := sorry
    let eP : PM ≃ₗ[R] PN :=
      (Finsupp.mapDomain.linearEquiv (Shrink.{v} R) R e'.toEquiv).trans
      (Finsupp.mapRange.linearEquiv eR)
    let g : PN ⟶ N := ModuleCat.ofHom ((e'.toLinearMap.comp f.hom).comp eP.symm.toLinearMap)
    have epi : Epi g := by simpa [ModuleCat.epi_iff_surjective, g] using surjf

    sorry

lemma projectiveDimension_eq_of_linearEquiv [Small.{v} R] [Small.{v'} R]
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R} (e : M ≃ₗ[R] N) :
    projectiveDimension M = projectiveDimension N := by
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot => simpa [projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton] using
      e.subsingleton_congr
  | coe n =>
    induction n with
    | top => simp
    | coe n =>
      norm_cast
      simp only [projectiveDimension_le_iff]
      refine ⟨fun h ↦ hasProjectiveDimensionLE_of_linearEquiv e n,
        fun h ↦ hasProjectiveDimensionLE_of_linearEquiv e.symm n⟩

end

section

variable {R' : Type u'} [CommRing R'] (e : R ≃+* R')

open Module in
lemma hasProjectiveDimensionLE_of_semiLinearEquiv [Small.{v} R] [Small.{v'} R']
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R'}
    (e' : letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
          letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
          M ≃ₛₗ[e.toRingHom] N) (n : ℕ) [h : HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE N n := by
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
  induction n generalizing M N e'
  · simp only [HasProjectiveDimensionLE, zero_add,
      ← projective_iff_hasProjectiveDimensionLT_one] at h ⊢
    rw [← IsProjective.iff_projective] at h ⊢

    sorry
  · rename_i n ih
    let PM := ModuleCat.of R (M →₀ Shrink.{v} R)
    let b : Basis M R (M →₀ Shrink.{v} R) := ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)⟩
    let f : PM ⟶ M := ModuleCat.ofHom (b.constr ℕ _root_.id)
    have epif : Epi f := by
      rw [ModuleCat.epi_iff_range_eq_top, LinearMap.range_eq_top]
      refine fun m ↦ ⟨Finsupp.single m 1, ?_⟩
      simp only [ModuleCat.hom_ofHom, f, b]
      rw [Basis.constr_apply]
      simp [Finsupp.mapRange.linearEquiv]
    have surjf := (ModuleCat.epi_iff_surjective f).mp epif
    let _ : Projective PM := ModuleCat.projective_of_free b
    let PN := ModuleCat.of R' (N →₀ Shrink.{v'} R')
    let b' : Basis N R' (N →₀ Shrink.{v'} R') :=
      ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R' R')⟩
    let _ : Projective PN := ModuleCat.projective_of_free b'
    let eR : Shrink.{v} R ≃ₛₗ[e.toRingHom] Shrink.{v'} R' := sorry
    let eP : PM ≃ₛₗ[e.toRingHom] PN :=
      (Finsupp.mapDomain.linearEquiv (Shrink.{v} R) R e'.toEquiv).trans
      (Finsupp.mapRange.linearEquiv eR)
    let g : PN ⟶ N := ModuleCat.ofHom ((e'.toLinearMap.comp f.hom).comp eP.symm.toLinearMap)
    have epi : Epi g := by simpa [ModuleCat.epi_iff_surjective, g] using surjf

    sorry

lemma projectiveDimension_eq_of_semiLinearEquiv [Small.{v} R] [Small.{v'} R']
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R'}
    (e' : letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
          letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
          M ≃ₛₗ[e.toRingHom] N) :
    projectiveDimension M = projectiveDimension N := by
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
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

end CategoryTheory
