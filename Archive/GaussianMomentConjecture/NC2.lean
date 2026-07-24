/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.SupportFaceBridge
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# NC2 from the one-variable Duistermaat--van der Kallen input

This module closes the post-geometry part of the modular GMC(2) descent
spine.  A hypothetical moment-null polynomial whose charges are not
one-sided supplies a nonzero integral lowest-face seed.  Universal
specialization carries all integral zero relations to a finite field while
preserving that seed.  Given the compact normalized height package, the
prime-dilated moment relation is therefore both zero and nonzero.  The one
remaining composition boundary is exposed honestly as `HeightWitnessSupplier`.
-/

open MvPolynomial Finset

namespace GMC2.NC2

noncomputable section

/-- Universal integral specialization reflects nonvanishing of the selected
face seed back to the rational complex face model. -/
theorem rational_face_seed_ne_zero
    {R : Type*} [CommRing R] [Algebra ℤ R]
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (hsubset : F ⊆ P.support) (m0 : ℕ) (w : ↥P.support → R)
    (huniversal : ∀ f : MvPolynomial ↥P.support ℤ,
      MvPolynomial.aeval (fun s : ↥P.support ↦ P.coeff s) f = 0 →
        MvPolynomial.aeval w f = 0)
    (hseedSpecial : MvPolynomial.aeval w
      (GMC2.IntegralFaceSeedDescent.liftedFaceSeedInt P F hsubset m0) ≠ 0) :
    MvPolynomial.aeval (fun s : ↥F ↦ P.coeff s)
      (GMC2.ConstantTermRelations.constantTermRelation
        (fun s : ↥F ↦ GMC2.charge s) m0) ≠ 0 := by
  have hseedComplexInt :
      MvPolynomial.aeval (fun s : ↥P.support ↦ P.coeff s)
          (GMC2.IntegralFaceSeedDescent.liftedFaceSeedInt
            P F hsubset m0) ≠ 0 := by
    intro hzero
    exact hseedSpecial (huniversal _ hzero)
  have hseedFaceInt :
      MvPolynomial.aeval (fun s : ↥F ↦ P.coeff s)
          (GMC2.IntegralRelations.constantTermRelationInt
            (fun s : ↥F ↦ GMC2.charge s) m0) ≠ 0 := by
    have h := hseedComplexInt
    rw [GMC2.IntegralFaceSeedDescent.aeval_liftedFaceSeedInt] at h
    exact h
  simpa only [GMC2.IntegralRelations.aeval_constantTermRelationInt_eq_rat]
    using hseedFaceInt

/-- The three normalized-residue height inputs, already transported from the
geometric face to the exact support of `P`. -/
structure NormalizedHeightPackage
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (m0 A0 : ℕ) : Prop where
  scaledFloor : ∀ p : ℕ, ∀ r ∈
      GMC2.NormalizedResidue.fullChannels p m0,
      GMC2.NormalizedMoment.IsBalanced
          (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) r →
      p * A0 ≤ GMC2.NormalizedMoment.channelHeight
          (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) r
  faceHeight : ∀ s ∈ Finset.piAntidiag
      (Finset.univ : Finset
        ↥(GMC2.SupportFaceBridge.supportFace P F)) m0,
      GMC2.NormalizedMoment.IsBalanced
          (fun t : ↥P.support ↦ (t : Fin 2 →₀ ℕ))
          (GMC2.ChannelDilation.extendByZero
            (GMC2.SupportFaceBridge.supportFace P F) s) →
      GMC2.NormalizedMoment.channelHeight
          (fun t : ↥P.support ↦ (t : Fin 2 →₀ ℕ))
          (GMC2.ChannelDilation.extendByZero
            (GMC2.SupportFaceBridge.supportFace P F) s) = A0
  offHeight : ∀ r ∈ Finset.piAntidiag
      (Finset.univ : Finset ↥P.support) m0,
      GMC2.NormalizedMoment.IsBalanced
          (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) r →
      ¬ GMC2.NormalizedResidue.SupportedOn
          (GMC2.SupportFaceBridge.supportFace P F) r →
      A0 + 1 ≤ GMC2.NormalizedMoment.channelHeight
          (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) r

/-- Convert the three full-support height statements into the exact shapes
consumed by normalized residue assembly. -/
theorem normalized_height_package_of_base
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (m0 A0 : ℕ)
    (H : GMC2.SupportFaceBridge.ReferenceHeightObligations P F m0 A0) :
    NormalizedHeightPackage P F m0 A0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro p r hr hbalanced
    apply H.scaledFullFloor p r
    · simpa only [GMC2.NormalizedResidue.fullChannels] using hr
    · exact hbalanced
  · intro s hs hbalanced
    apply H.faceBaseHeight
      (GMC2.ChannelDilation.extendByZero
        (GMC2.SupportFaceBridge.supportFace P F) s)
    · exact GMC2.NormalizedResidue.extendByZero_mem_piAntidiag
        (GMC2.SupportFaceBridge.supportFace P F) s hs
    · exact hbalanced
    · intro i hi
      by_contra hiFace
      exact hi (GMC2.ChannelDilation.extendByZero_of_notMem
        (GMC2.SupportFaceBridge.supportFace P F) s hiFace)
  · intro r hr hbalanced hnotSupported
    apply H.offFaceGap r hr hbalanced
    by_contra hnoOffFace
    apply hnotSupported
    intro i hiFace
    by_contra hri
    exact hnoOffFace ⟨i, hri, hiFace⟩

/-- The common normalized relation cannot be both universally specialized
from zero and nonzero by the Frobenius face residue. -/
theorem normalized_specialization_contradiction
    {R : Type*} [Field R]
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (m0 A0 : ℕ) (hsubset : F ⊆ P.support) (hm0 : 1 ≤ m0)
    (w : ↥P.support → R)
    (hnull : ∀ m : ℕ, 1 ≤ m → GMC2.E (P ^ m) = 0)
    (huniversal : ∀ f : MvPolynomial ↥P.support ℤ,
      MvPolynomial.aeval (fun s : ↥P.support ↦ P.coeff s) f = 0 →
        MvPolynomial.aeval w f = 0)
    (hseedSpecial : MvPolynomial.aeval w
      (GMC2.IntegralFaceSeedDescent.liftedFaceSeedInt P F hsubset m0) ≠ 0)
    (H : NormalizedHeightPackage P F m0 A0) : False := by
  have hfaceSpecial :
      GMC2.NormalizedResidue.faceConstantTerm
          (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) w
          (GMC2.SupportFaceBridge.supportFace P F) m0 ≠ 0 := by
    rw [← GMC2.SupportFaceBridge.aeval_liftedFaceSeedInt_eq_faceConstantTerm
      P F hsubset m0 w]
    exact hseedSpecial
  have hpMass : 1 ≤ p * m0 := by
    have hpPos : 0 < p := (Fact.out : Nat.Prime p).pos
    have hm0Pos : 0 < m0 := lt_of_lt_of_le Nat.zero_lt_one hm0
    exact Nat.mul_pos hpPos hm0Pos
  have hnormalizedComplex :
      MvPolynomial.aeval (fun s : ↥P.support ↦ P.coeff s)
          (GMC2.NormalizedMoment.normalizedMomentRelationInt
            (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ))
            (p * m0) (p * A0)) = 0 := by
    apply GMC2.NormalizedMoment.aeval_normalized_eq_zero_of_E_pow_eq_zero
    · intro r hr hbalanced
      apply H.scaledFloor p r
      · simpa only [GMC2.NormalizedResidue.fullChannels] using hr
      · exact hbalanced
    · rw [GMC2.SupportDescent.indexedPolynomial_support_eq]
      exact hnull (p * m0) hpMass
  have hnormalizedSpecial :
      MvPolynomial.aeval w
          (GMC2.NormalizedMoment.normalizedMomentRelationInt
            (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ))
            (p * m0) (p * A0)) = 0 :=
    huniversal _ hnormalizedComplex
  have hnormalizedSpecialNe :
      MvPolynomial.aeval w
          (GMC2.NormalizedMoment.normalizedMomentRelationInt
            (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ))
            (p * m0) (p * A0)) ≠ 0 :=
    GMC2.NormalizedResidue.aeval_normalizedMoment_ne_zero
      p m0 A0 (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) w
      (GMC2.SupportFaceBridge.supportFace P F)
      (H.scaledFloor p) H.faceHeight H.offHeight hfaceSpecial
  exact hnormalizedSpecialNe hnormalizedSpecial

/-- A compact supplier for the normalized height package attached to a
nonzero rational lowest-face seed.  This is the sole capstone premise left
explicit by this module. -/
structure HeightWitnessSupplier : Prop where
  supply : ∀ (P : MvPolynomial (Fin 2) ℂ)
      (F : Finset (Fin 2 →₀ ℕ)) (lambda delta : ℚ) (m0 : ℕ),
    (∀ s ∈ P.support,
      delta ≤ GMC2.radialExponentQ s - lambda * GMC2.chargeQ s) →
    (∀ s, s ∈ F ↔ s ∈ P.support ∧
      GMC2.radialExponentQ s - lambda * GMC2.chargeQ s = delta) →
    MvPolynomial.aeval (fun s : ↥F ↦ P.coeff s)
      (GMC2.ConstantTermRelations.constantTermRelation
        (fun s : ↥F ↦ GMC2.charge s) m0) ≠ 0 →
    ∃ A0, NormalizedHeightPackage P F m0 A0

/-- The one-variable DvdK input and the compact height-package supplier imply
the two-variable nullcone classification `NC2`. -/
theorem nc2_of_dvdK1_of_heightWitnessSupplier
    (hDvdK : GMC2.DvdKInterface.DvdK1)
    (hHeight : HeightWitnessSupplier) : GMC2.NC2 := by
  intro P hnull
  by_contra hP
  obtain ⟨lambda, delta, F, m0, hsubset, hm0, hlower, hface,
      A, D, w, hp, hchar, _hfinite, _hfield, _hunit, _hnonzero,
      huniversal, _hmomentFinite, hseedSpecial⟩ :=
    GMC2.IntegralFaceSeedDescent.exists_finite_field_moment_point_seed
      hDvdK P hnull hP
  have hseed := rational_face_seed_ne_zero
    P F hsubset m0 w huniversal hseedSpecial
  letI : Field D.ResidueField := D.fieldStructure
  letI : Algebra ℤ D.ResidueField := Ring.toIntAlgebra D.ResidueField
  letI : Fact D.p.Prime := ⟨hp⟩
  letI : CharP D.ResidueField D.p := hchar
  obtain ⟨A0, H⟩ := hHeight.supply
      P F lambda delta m0 hlower hface hseed
  exact normalized_specialization_contradiction
    D.p P F m0 A0 hsubset hm0 w hnull huniversal hseedSpecial H

/-- Direct GMC(2) endpoint obtained by composing the conditional nullcone
classification with the elementary charge reduction. -/
theorem gmc2_of_dvdK1_of_heightWitnessSupplier
    (hDvdK : GMC2.DvdKInterface.DvdK1)
    (hHeight : HeightWitnessSupplier)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (hnull : ∀ m : ℕ, 1 ≤ m → GMC2.E (P ^ m) = 0) :
    ∃ N : ℕ, ∀ m ≥ N, GMC2.E (Q * P ^ m) = 0 :=
  GMC2.gmc2_of_nc2
    (nc2_of_dvdK1_of_heightWitnessSupplier hDvdK hHeight) P Q hnull

end

end GMC2.NC2
