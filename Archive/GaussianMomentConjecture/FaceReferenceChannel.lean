/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.FaceDictionary
import Archive.GaussianMomentConjecture.FaceHeightFloor
import Archive.GaussianMomentConjecture.FaceSeedChannel
import Archive.GaussianMomentConjecture.NormalizedMoment
import Mathlib

set_option linter.minImports true

/-!
# A concrete reference channel from a nonzero lowest-face seed

A nonzero evaluated face constant-term relation contains a nonzero balanced
summand.  This module transports that summand through the exact bidegree
dictionary and packages its mass, charge, and height in the precise form used
by the lowest-face height-floor comparison.
-/

open MvPolynomial Finset

namespace GMC2.FaceReferenceChannel

noncomputable section

/-- For exact bidegrees on a face, the rational total charge is the rational
cast of the integral charge used by the constant-term relation. -/
theorem face_totalChargeQ_eq_cast_totalCharge
    (F : Finset (Fin 2 →₀ ℕ)) (r : ↥F → ℕ) :
    GMC2.FrobeniusFace.totalChargeQ
        (fun s : ↥F ↦ GMC2.FaceDictionary.exponentA s)
        (fun s : ↥F ↦ GMC2.FaceDictionary.exponentB s)
        Finset.univ r =
      ((GMC2.ConstantTermRelations.totalCharge
        (fun s : ↥F ↦ GMC2.charge s) r : ℤ) : ℚ) := by
  simp [GMC2.FrobeniusFace.totalChargeQ,
    GMC2.ConstantTermRelations.totalCharge,
    GMC2.FrobeniusFace.charge, GMC2.FaceDictionary.exponentA,
    GMC2.FaceDictionary.exponentB, GMC2.charge]

/-- The rational radial height of an exact-support channel is the cast of the
natural Wick channel height used by `NormalizedMoment`. -/
theorem face_radialHeightQ_eq_cast_channelHeight
    (F : Finset (Fin 2 →₀ ℕ)) (r : ↥F → ℕ) :
    GMC2.FrobeniusFace.radialHeightQ
        (fun s : ↥F ↦ GMC2.FaceDictionary.exponentA s)
        Finset.univ r =
      (GMC2.NormalizedMoment.channelHeight
        (fun s : ↥F ↦ (s : Fin 2 →₀ ℕ)) r : ℚ) := by
  simp [GMC2.FrobeniusFace.radialHeightQ,
    GMC2.FaceDictionary.exponentA,
    GMC2.NormalizedMoment.channelHeight,
    GMC2.MomentRelations.channelExponent]

/-- A nonzero mass-`m0` face seed supplies a concrete reference channel.

The conclusion retains its nonzero summand and packages the four hypotheses
needed by `GMC2.FaceHeightFloor.balanced_natural_height_floor_of_reference`:
equality-face support, rational charge zero, mass `m0`, and rational radial
height equal to the cast of the natural channel height `A0`. -/
theorem exists_reference_channel_of_nonzero_face_seed
    (F : Finset (Fin 2 →₀ ℕ)) (coefficient : ↥F → ℂ)
    (lambda delta : ℚ) (m0 : ℕ)
    (hface : ∀ s ∈ F,
      GMC2.FrobeniusFace.tiltedHeight
        GMC2.FaceDictionary.exponentA GMC2.FaceDictionary.exponentB lambda s = delta)
    (hseed : MvPolynomial.aeval coefficient
      (GMC2.ConstantTermRelations.constantTermRelation
        (fun s : ↥F ↦ GMC2.charge s) m0) ≠ 0) :
    ∃ (r0 : ↥F → ℕ) (A0 : ℕ),
      r0 ∈ Finset.piAntidiag (Finset.univ : Finset ↥F) m0 ∧
      GMC2.FaceHeightFloor.channelMass Finset.univ r0 = m0 ∧
      GMC2.ConstantTermRelations.totalCharge
        (fun s : ↥F ↦ GMC2.charge s) r0 = 0 ∧
      GMC2.FrobeniusFace.totalChargeQ
        (fun s : ↥F ↦ GMC2.FaceDictionary.exponentA s)
        (fun s : ↥F ↦ GMC2.FaceDictionary.exponentB s)
        Finset.univ r0 = 0 ∧
      A0 = GMC2.NormalizedMoment.channelHeight
        (fun s : ↥F ↦ (s : Fin 2 →₀ ℕ)) r0 ∧
      GMC2.FrobeniusFace.radialHeightQ
        (fun s : ↥F ↦ GMC2.FaceDictionary.exponentA s)
        Finset.univ r0 = (A0 : ℚ) ∧
      (∀ i ∈ (Finset.univ : Finset ↥F), r0 i ≠ 0 →
        GMC2.FrobeniusFace.tiltedHeight
          (fun s : ↥F ↦ GMC2.FaceDictionary.exponentA s)
          (fun s : ↥F ↦ GMC2.FaceDictionary.exponentB s)
          lambda i = delta) ∧
      (Nat.multinomial Finset.univ r0 : ℂ) *
        ∏ i, coefficient i ^ r0 i ≠ 0 := by
  obtain ⟨r0, hr0, hcharge, hterm⟩ :=
    GMC2.FaceSeedChannel.exists_nonzero_balanced_channel
      (fun s : ↥F ↦ GMC2.charge s) coefficient m0 hseed
  let A0 : ℕ := GMC2.NormalizedMoment.channelHeight
    (fun s : ↥F ↦ (s : Fin 2 →₀ ℕ)) r0
  have hmass : GMC2.FaceHeightFloor.channelMass Finset.univ r0 = m0 := by
    simpa [GMC2.FaceHeightFloor.channelMass] using
      (Finset.mem_piAntidiag.mp hr0).1
  have hbalanced :
      GMC2.FrobeniusFace.totalChargeQ
        (fun s : ↥F ↦ GMC2.FaceDictionary.exponentA s)
        (fun s : ↥F ↦ GMC2.FaceDictionary.exponentB s)
        Finset.univ r0 = 0 := by
    rw [face_totalChargeQ_eq_cast_totalCharge, hcharge]
    simp
  have hheight :
      GMC2.FrobeniusFace.radialHeightQ
        (fun s : ↥F ↦ GMC2.FaceDictionary.exponentA s)
        Finset.univ r0 = (A0 : ℚ) := by
    simpa [A0] using face_radialHeightQ_eq_cast_channelHeight F r0
  have hsupport : ∀ i ∈ (Finset.univ : Finset ↥F), r0 i ≠ 0 →
      GMC2.FrobeniusFace.tiltedHeight
        (fun s : ↥F ↦ GMC2.FaceDictionary.exponentA s)
        (fun s : ↥F ↦ GMC2.FaceDictionary.exponentB s)
        lambda i = delta := by
    intro i hi hri
    simpa [GMC2.FrobeniusFace.tiltedHeight, GMC2.FrobeniusFace.charge,
      GMC2.FaceDictionary.exponentA, GMC2.FaceDictionary.exponentB,
      GMC2.radialExponentQ, GMC2.chargeQ, GMC2.charge] using hface i i.property
  exact ⟨r0, A0, hr0, hmass, hcharge, hbalanced, rfl,
    hheight, hsupport, hterm⟩

end


end GMC2.FaceReferenceChannel

