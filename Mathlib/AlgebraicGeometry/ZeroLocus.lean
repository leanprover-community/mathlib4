/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Restrict

/-!

# Zero locus on schemes

In this file we show some properties of the zero locus of a set of sections specific
to locally ringed spaces or schemes.

In the case of affine schemes, the zero locus corresponds under the `Scheme.isoSpec` isomorphism
to the zero locus in the sense of prime spectra. We provide API for reasoning about zero loci on affine
schemes to avoid using the `Scheme.isoSpec` isomorphism in applications.

## Main results

-/

universe u

open TopologicalSpace CategoryTheory Opposite

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace} {U : Opens X}

lemma Scheme.zeroLocus_primeSpectrum_zeroLocus' {X : LocallyRingedSpace}
    (s : Set (X.presheaf.obj (op ⊤))) :
    X.toΓSpecFun ⁻¹' PrimeSpectrum.zeroLocus s = X.toRingedSpace.zeroLocus s := by
  simp only [RingedSpace.zeroLocus]
  have (i : LocallyRingedSpace.Γ.obj (op X)) (_ : i ∈ s) : (X.toRingedSpace.basicOpen i).carrierᶜ =
        X.toΓSpecFun ⁻¹' (PrimeSpectrum.basicOpen i).carrierᶜ := by
    symm
    rw [Set.preimage_compl, X.toΓSpec_preim_basicOpen_eq i]
  erw [Set.iInter₂_congr this]
  rw [← Set.preimage_iInter₂]
  simp only [Scheme.Γ_obj, Opens.carrier_eq_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl]
  rw [← PrimeSpectrum.zeroLocus_iUnion₂]
  simp

lemma Scheme.zeroLocus_primeSpectrum_zeroLocus {X : Scheme} [IsAffine X] (s : Set (Scheme.Γ.obj (op X))) :
    X.isoSpec.hom.val.base '' X.toRingedSpace.zeroLocus s = PrimeSpectrum.zeroLocus s := by
  rw [← Scheme.zeroLocus_primeSpectrum_zeroLocus']
  show X.isoSpec.hom.val.base '' (X.isoSpec.hom.val.base ⁻¹' PrimeSpectrum.zeroLocus s) =
    PrimeSpectrum.zeroLocus s
  rw [Set.image_preimage_eq]
  apply Function.Bijective.surjective
  have : IsIso (X.isoSpec.hom.val.base) := inferInstance
  exact ConcreteCategory.bijective_of_isIso (X.isoSpec.hom.val.base)

lemma eq_zeroLocus_of_isClosed (X : Scheme) [IsAffine X] (s : Set X.carrier) (hs : IsClosed s) :
    ∃ I : Ideal (Scheme.Γ.obj (op X)), s = X.toRingedSpace.zeroLocus (I : Set (Scheme.Γ.obj (op X))) := by
  let A : CommRingCat := Scheme.Γ.obj (op X)
  let iso : X ≅ Spec A := Scheme.isoSpec X
  let Z : Set (Spec A) := iso.hom.val.base '' s
  have hZ : IsClosed Z :=
    (TopCat.homeoOfIso (asIso <| iso.hom.val.base)).isClosedMap _ hs
  obtain ⟨I, (hI : Z = _)⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hZ
  use I
  have : Function.Injective (Set.image iso.hom.val.base) := by
    simp only [Set.image_injective]
    exact (ConcreteCategory.bijective_of_isIso iso.hom.val.base).injective
  apply this
  show Z = _
  rw [hI]
  erw [Scheme.zeroLocus_primeSpectrum_zeroLocus]

lemma Scheme.zeroLocus_eq_top_iff {X : Scheme} [IsAffine X] (s : Set Γ(X, ⊤)) :
    X.toRingedSpace.zeroLocus s = ⊤ ↔ s ⊆ (nilradical Γ(X, ⊤)).carrier := by
  rw [← Scheme.zeroLocus_primeSpectrum_zeroLocus']
  simp only [Functor.op_obj, inducedFunctor_obj, LocallyRingedSpace.forgetToSheafedSpace_obj,
    LocallyRingedSpace.Γ_obj, Set.top_eq_univ, Set.preimage_eq_univ_iff, Scheme.Γ_obj]
  erw [← PrimeSpectrum.zeroLocus_eq_top_iff]
  have hfsurj : Function.Surjective (X.toΓSpecFun) := by
    apply Function.Bijective.surjective
    apply ConcreteCategory.bijective_of_isIso X.isoSpec.hom.val.base
  rw [hfsurj.range_eq]
  simp

lemma Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isAffine {X : Scheme}
    {U : Opens X} (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsNilpotent f ↔ X.basicOpen f = ⊥ := by
  constructor
  · intro h
    apply X.basicOpen_eq_bot_of_isNilpotent
    exact h
  · intro h
    let U' : Scheme := X ∣_ᵤ U
    let f' : Γ(U', ⊤) := sorry
    sorry

lemma Scheme.isNilpotent_of_basicOpen_eq_bot_of_quasiCompact {X : Scheme}
    {U : Opens X} (hU : IsCompact U.carrier) (f : Γ(X, U))
    (hf : X.basicOpen f = ⊥) : IsNilpotent f := by
  sorry
