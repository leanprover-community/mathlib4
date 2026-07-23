/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.FrobeniusResidue
import Mathlib

set_option linter.minImports true

/-!
# Three-case residue assembly for the GMC(2) Frobenius proof

The arithmetic lemmas in `FrobeniusResidue` kill two classes of
normalized moment channels: channels that are not componentwise `p`-dilated,
and dilated channels lying off the lowest face.  The remaining face channels
have the form `w_i x_i^p`.  This file performs the previously implicit finite
sum assembly and identifies the result with the Frobenius power of the face
sum.

The theorem is representation-independent.  A later transport layer must
instantiate `channels`, `dilated`, `face`, and `term` from the Wick-channel
data; that construction is deliberately not assumed here.
-/

open Finset

namespace GMC2ResidueAssembly

/-- The three residue cases assemble to the normalized identity (15): all
non-dilated and dilated-off-face channels vanish, while the face layer is the
Frobenius power of its undilated weighted sum. -/
theorem three_case_sum_eq_frobenius
    {R ι : Type*} [CommSemiring R]
    (p : ℕ) [ExpChar R p]
    (channels dilated face : Finset ι)
    (term : ι → R) (weight : ι → ℕ) (coefficient : ι → R)
    (hface_dilated : face ⊆ dilated)
    (hdilated_channels : dilated ⊆ channels)
    (hnondilated : ∀ i ∈ channels, i ∉ dilated → term i = 0)
    (hoffFace : ∀ i ∈ dilated, i ∉ face → term i = 0)
    (honFace : ∀ i ∈ face,
      term i = (weight i : R) * coefficient i ^ p) :
    ∑ i ∈ channels, term i =
      (∑ i ∈ face, (weight i : R) * coefficient i) ^ p := by
  have hface_channels : face ⊆ channels :=
    fun i hi => hdilated_channels (hface_dilated hi)
  have hrestrict :
      (∑ i ∈ face, term i) = ∑ i ∈ channels, term i := by
    apply Finset.sum_subset hface_channels
    intro i hiChannels hiFace
    by_cases hiDilated : i ∈ dilated
    · exact hoffFace i hiDilated hiFace
    · exact hnondilated i hiChannels hiDilated
  rw [← hrestrict]
  calc
    ∑ i ∈ face, term i =
        ∑ i ∈ face, (weight i : R) * coefficient i ^ p := by
          apply Finset.sum_congr rfl
          intro i hi
          exact honFace i hi
    _ = (∑ i ∈ face, (weight i : R) * coefficient i) ^ p := by
          symm
          exact GMC2FrobeniusResidue.weighted_sum_pow_char
            p face weight coefficient

/-- If the undilated face sum is nonzero in a domain, then the assembled
normalized moment residue is nonzero. -/
theorem three_case_sum_ne_zero
    {R ι : Type*} [CommRing R] [IsDomain R]
    (p : ℕ) [ExpChar R p]
    (channels dilated face : Finset ι)
    (term : ι → R) (weight : ι → ℕ) (coefficient : ι → R)
    (hface_dilated : face ⊆ dilated)
    (hdilated_channels : dilated ⊆ channels)
    (hnondilated : ∀ i ∈ channels, i ∉ dilated → term i = 0)
    (hoffFace : ∀ i ∈ dilated, i ∉ face → term i = 0)
    (honFace : ∀ i ∈ face,
      term i = (weight i : R) * coefficient i ^ p)
    (hfaceSum : ∑ i ∈ face, (weight i : R) * coefficient i ≠ 0) :
    ∑ i ∈ channels, term i ≠ 0 := by
  rw [three_case_sum_eq_frobenius p channels dilated face term weight coefficient
    hface_dilated hdilated_channels hnondilated hoffFace honFace]
  exact pow_ne_zero p hfaceSum

end GMC2ResidueAssembly

