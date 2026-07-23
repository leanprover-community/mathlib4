/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.LowestFaceBridge
import Mathlib

set_option linter.minImports true

/-!
# Packaged equality face on an exact polynomial support

The existence bridge returns explicit equality witnesses.  This module
packages their equality set as a `Finset`, records its exact membership law,
and proves that its charges still meet or straddle zero.  It is the shape
consumed by the finite face-channel and Frobenius layers.
-/

open MvPolynomial Finset

namespace GMC2

/-- A non-one-sided polynomial support has a rational lowest equality face
that is a subset of the exact support and still straddles charge zero. -/
theorem exists_rational_lowest_face_finset
    (P : MvPolynomial (Fin 2) ℂ) (hP : ¬ChargeOneSided P) :
    ∃ lambda delta : ℚ, ∃ F : Finset (Fin 2 →₀ ℕ),
      F ⊆ P.support ∧
      (∀ s ∈ P.support,
        delta ≤ radialExponentQ s - lambda * chargeQ s) ∧
      (∀ s, s ∈ F ↔ s ∈ P.support ∧
        radialExponentQ s - lambda * chargeQ s = delta) ∧
      GMC2LowestFaceExistence.ChargesStraddleZero F chargeQ := by
  obtain ⟨lambda, delta, hlower, hwitness⟩ :=
    exists_rational_lowest_face_of_not_chargeOneSided P hP
  let F : Finset (Fin 2 →₀ ℕ) :=
    P.support.filter fun s =>
      radialExponentQ s - lambda * chargeQ s = delta
  refine ⟨lambda, delta, F, ?_, hlower, ?_, ?_⟩
  · intro s hs
    exact (Finset.mem_filter.mp hs).1
  · intro s
    simp only [F, Finset.mem_filter]
  · rcases hwitness with hneutral | hopposite
    · left
      obtain ⟨s, hs, hcharge, hheight⟩ := hneutral
      refine ⟨s, ?_, hcharge⟩
      exact Finset.mem_filter.mpr ⟨hs, hheight⟩
    · right
      obtain ⟨s, hs, t, ht, hsneg, htpos, hsheight, htheight⟩ := hopposite
      constructor
      · exact ⟨s, Finset.mem_filter.mpr ⟨hs, hsheight⟩, hsneg⟩
      · exact ⟨t, Finset.mem_filter.mpr ⟨ht, htheight⟩, htpos⟩

end GMC2

