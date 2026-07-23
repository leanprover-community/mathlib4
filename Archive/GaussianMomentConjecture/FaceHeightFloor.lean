/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.FrobeniusFace
import Mathlib

set_option linter.minImports true

/-!
# Height floors from a rational lowest face

This module isolates the channel-height comparison needed by the normalized
moment construction.  A weighted tilted-height identity turns a pointwise
supporting-line inequality into a radial-height floor for every balanced
channel.  A balanced reference channel supported on the equality face fixes
the floor at every multiple of its mass, and strict off-face use gives the
integral one-step gap used by the Frobenius factorial argument.
-/

open Finset

namespace GMC2FaceHeightFloor

variable {ι : Type*}

/-- Natural total multiplicity of a channel on a finite index set. -/
def channelMass (F : Finset ι) (r : ι → ℕ) : ℕ :=
  ∑ i ∈ F, r i

/-- The weighted sum of the tilted heights used by a channel. -/
def weightedTiltedHeightQ
    (a b : ι → ℤ) (lambda : ℚ) (F : Finset ι) (r : ι → ℕ) : ℚ :=
  ∑ i ∈ F, (r i : ℚ) * GMC2FrobeniusFace.tiltedHeight a b lambda i

/-- Rational mass is the cast of the natural channel mass. -/
theorem massQ_eq_natCast_channelMass
    (F : Finset ι) (r : ι → ℕ) :
    GMC2FrobeniusFace.massQ F r = (channelMass F r : ℚ) := by
  simp [GMC2FrobeniusFace.massQ, channelMass]

/-- Weighted tilted height is radial height minus slope times total charge. -/
theorem weightedTiltedHeightQ_eq_radial_sub_charge [DecidableEq ι]
    (a b : ι → ℤ) (lambda : ℚ) (F : Finset ι) (r : ι → ℕ) :
    weightedTiltedHeightQ a b lambda F r =
      GMC2FrobeniusFace.radialHeightQ a F r -
        lambda * GMC2FrobeniusFace.totalChargeQ a b F r := by
  calc
    weightedTiltedHeightQ a b lambda F r =
        ∑ i ∈ F,
          ((r i : ℚ) * (a i : ℚ) -
            lambda * ((r i : ℚ) * (GMC2FrobeniusFace.charge a b i : ℚ))) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [GMC2FrobeniusFace.tiltedHeight]
      ring
    _ = GMC2FrobeniusFace.radialHeightQ a F r -
        lambda * GMC2FrobeniusFace.totalChargeQ a b F r := by
      simp [GMC2FrobeniusFace.radialHeightQ,
        GMC2FrobeniusFace.totalChargeQ, Finset.sum_sub_distrib,
        Finset.mul_sum]

/-- A global tilted-height lower bound gives the common rational radial floor
for every balanced channel. -/
theorem balanced_radialHeight_floor [DecidableEq ι]
    (a b : ι → ℤ) (lambda delta : ℚ) (F : Finset ι) (r : ι → ℕ)
    (hlower : ∀ i ∈ F,
      delta ≤ GMC2FrobeniusFace.tiltedHeight a b lambda i)
    (hbalanced : GMC2FrobeniusFace.totalChargeQ a b F r = 0) :
    delta * GMC2FrobeniusFace.massQ F r ≤
      GMC2FrobeniusFace.radialHeightQ a F r := by
  calc
    delta * GMC2FrobeniusFace.massQ F r =
        ∑ i ∈ F, delta * (r i : ℚ) := by
      simp [GMC2FrobeniusFace.massQ, Finset.mul_sum]
    _ ≤ weightedTiltedHeightQ a b lambda F r := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [weightedTiltedHeightQ, mul_comm] using
        (mul_le_mul_of_nonneg_right (hlower i hi)
          (show 0 ≤ (r i : ℚ) by positivity))
    _ = GMC2FrobeniusFace.radialHeightQ a F r -
        lambda * GMC2FrobeniusFace.totalChargeQ a b F r :=
      weightedTiltedHeightQ_eq_radial_sub_charge a b lambda F r
    _ = GMC2FrobeniusFace.radialHeightQ a F r := by
      rw [hbalanced]
      ring

/-- Consumer form of the floor for a channel of specified natural mass `m`. -/
theorem balanced_radialHeight_floor_of_mass [DecidableEq ι]
    (a b : ι → ℤ) (lambda delta : ℚ) (F : Finset ι) (r : ι → ℕ) (m : ℕ)
    (hlower : ∀ i ∈ F,
      delta ≤ GMC2FrobeniusFace.tiltedHeight a b lambda i)
    (hbalanced : GMC2FrobeniusFace.totalChargeQ a b F r = 0)
    (hmass : channelMass F r = m) :
    (m : ℚ) * delta ≤ GMC2FrobeniusFace.radialHeightQ a F r := by
  have hfloor := balanced_radialHeight_floor
    a b lambda delta F r hlower hbalanced
  rw [massQ_eq_natCast_channelMass, hmass] at hfloor
  simpa only [mul_comm] using hfloor

/-- If every index used with nonzero multiplicity lies on the equality face,
a balanced channel attains the radial floor exactly. -/
theorem balanced_radialHeight_eq_of_supported_on_face [DecidableEq ι]
    (a b : ι → ℤ) (lambda delta : ℚ) (F : Finset ι) (r : ι → ℕ)
    (hsupport : ∀ i ∈ F, r i ≠ 0 →
      GMC2FrobeniusFace.tiltedHeight a b lambda i = delta)
    (hbalanced : GMC2FrobeniusFace.totalChargeQ a b F r = 0) :
    GMC2FrobeniusFace.radialHeightQ a F r =
      delta * GMC2FrobeniusFace.massQ F r := by
  have hweighted : weightedTiltedHeightQ a b lambda F r =
      delta * GMC2FrobeniusFace.massQ F r := by
    calc
      weightedTiltedHeightQ a b lambda F r =
          ∑ i ∈ F, delta * (r i : ℚ) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hri : r i = 0
        · simp [hri]
        · rw [hsupport i hi hri]
          ring
      _ = delta * GMC2FrobeniusFace.massQ F r := by
        simp [GMC2FrobeniusFace.massQ, Finset.mul_sum]
  calc
    GMC2FrobeniusFace.radialHeightQ a F r =
        weightedTiltedHeightQ a b lambda F r +
          lambda * GMC2FrobeniusFace.totalChargeQ a b F r := by
      rw [weightedTiltedHeightQ_eq_radial_sub_charge]
      ring
    _ = weightedTiltedHeightQ a b lambda F r := by
      rw [hbalanced]
      ring
    _ = delta * GMC2FrobeniusFace.massQ F r := hweighted

/-- A balanced equality-face channel of natural mass `m` attains `m * delta`. -/
theorem balanced_radialHeight_eq_floor_of_mass [DecidableEq ι]
    (a b : ι → ℤ) (lambda delta : ℚ) (F : Finset ι) (r : ι → ℕ) (m : ℕ)
    (hsupport : ∀ i ∈ F, r i ≠ 0 →
      GMC2FrobeniusFace.tiltedHeight a b lambda i = delta)
    (hbalanced : GMC2FrobeniusFace.totalChargeQ a b F r = 0)
    (hmass : channelMass F r = m) :
    GMC2FrobeniusFace.radialHeightQ a F r = (m : ℚ) * delta := by
  rw [balanced_radialHeight_eq_of_supported_on_face
    a b lambda delta F r hsupport hbalanced,
    massQ_eq_natCast_channelMass, hmass]
  ring

/-- Comparing a mass-`m0` equality-face reference channel of natural height
`A0` with any balanced mass-`p*m0` channel of natural height `A` gives the
height floor `p*A0 ≤ A`.  The explicit cast equalities are the interface for
identifying these radial sums with `GMC2NormalizedMoment.channelHeight`. -/
theorem balanced_natural_height_floor_of_reference [DecidableEq ι]
    (a b : ι → ℤ) (lambda delta : ℚ) (F : Finset ι)
    (r0 r : ι → ℕ) (m0 p A0 A : ℕ)
    (hlower : ∀ i ∈ F,
      delta ≤ GMC2FrobeniusFace.tiltedHeight a b lambda i)
    (hrefSupport : ∀ i ∈ F, r0 i ≠ 0 →
      GMC2FrobeniusFace.tiltedHeight a b lambda i = delta)
    (hrefBalanced : GMC2FrobeniusFace.totalChargeQ a b F r0 = 0)
    (hrefMass : channelMass F r0 = m0)
    (hrefHeight : GMC2FrobeniusFace.radialHeightQ a F r0 = (A0 : ℚ))
    (hbalanced : GMC2FrobeniusFace.totalChargeQ a b F r = 0)
    (hmass : channelMass F r = p * m0)
    (hheight : GMC2FrobeniusFace.radialHeightQ a F r = (A : ℚ)) :
    p * A0 ≤ A := by
  have href := balanced_radialHeight_eq_floor_of_mass
    a b lambda delta F r0 m0 hrefSupport hrefBalanced hrefMass
  have hrefQ : (A0 : ℚ) = (m0 : ℚ) * delta := by
    rw [← hrefHeight]
    exact href
  have hfloor := balanced_radialHeight_floor_of_mass
    a b lambda delta F r (p * m0) hlower hbalanced hmass
  rw [hheight] at hfloor
  have hcast : ((p * A0 : ℕ) : ℚ) ≤ (A : ℚ) := by
    calc
      ((p * A0 : ℕ) : ℚ) = (p : ℚ) * (A0 : ℚ) := by norm_num
      _ = (p : ℚ) * ((m0 : ℚ) * delta) := by rw [hrefQ]
      _ = ((p * m0 : ℕ) : ℚ) * delta := by
        push_cast
        ring
      _ ≤ (A : ℚ) := hfloor
  exact_mod_cast hcast

/-- Strict use of an off-face index by a balanced base channel of the same
mass as the reference gives `A0+1 ≤ A`.  This is exactly the gap hypothesis
consumed after dilation by
`GMC2FrobeniusResidue.prime_dvd_normalized_factorial_of_gap`. -/
theorem off_face_base_channel_natural_height_gap [DecidableEq ι]
    (a b : ι → ℤ) (lambda delta : ℚ) (F : Finset ι)
    (r0 r : ι → ℕ) (m0 A0 A : ℕ)
    (hlower : ∀ i ∈ F,
      delta ≤ GMC2FrobeniusFace.tiltedHeight a b lambda i)
    (hrefSupport : ∀ i ∈ F, r0 i ≠ 0 →
      GMC2FrobeniusFace.tiltedHeight a b lambda i = delta)
    (hrefBalanced : GMC2FrobeniusFace.totalChargeQ a b F r0 = 0)
    (hrefMass : channelMass F r0 = m0)
    (hrefHeight : GMC2FrobeniusFace.radialHeightQ a F r0 = (A0 : ℚ))
    (hbalanced : GMC2FrobeniusFace.totalChargeQ a b F r = 0)
    (hmass : channelMass F r = m0)
    (hheight : GMC2FrobeniusFace.radialHeightQ a F r = (A : ℚ))
    (j : ι) (hj : j ∈ F) (hrj : 0 < r j)
    (hstrict : delta < GMC2FrobeniusFace.tiltedHeight a b lambda j) :
    A0 + 1 ≤ A := by
  have href := balanced_radialHeight_eq_floor_of_mass
    a b lambda delta F r0 m0 hrefSupport hrefBalanced hrefMass
  have hoff := GMC2FrobeniusFace.balanced_height_strict_of_off_face
    a b lambda delta F r hlower hbalanced j hj hrj hstrict
  have hstrictQ : (A0 : ℚ) < (A : ℚ) := by
    calc
      (A0 : ℚ) = GMC2FrobeniusFace.radialHeightQ a F r0 := hrefHeight.symm
      _ = (m0 : ℚ) * delta := href
      _ = delta * GMC2FrobeniusFace.massQ F r := by
        rw [massQ_eq_natCast_channelMass, hmass]
        ring
      _ < GMC2FrobeniusFace.radialHeightQ a F r := hoff
      _ = (A : ℚ) := hheight
  have hstrictNat : A0 < A := by exact_mod_cast hstrictQ
  omega

end GMC2FaceHeightFloor

