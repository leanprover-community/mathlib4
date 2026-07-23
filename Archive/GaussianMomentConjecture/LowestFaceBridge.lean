/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.ChargeGeometry
import Archive.GaussianMomentConjecture.LowestFaceExistence
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic

/-!
# Polynomial-support bridge to the rational lowest face

This module connects the exact `MvPolynomial` charge support used by `NC2At`
to the rational finite-data theorem in `LowestFaceExistence`.  Thus a
failure of `ChargeOneSided` now produces the rational supporting slope and a
balanced equality face directly on `P.support`.
-/

open MvPolynomial Finset

namespace GMC2

/-- Rational first exponent and rational charge of an exact bidegree. -/
def radialExponentQ (s : Fin 2 →₀ ℕ) : ℚ := s 0

/-- The charge of a monomial, as a rational number. -/
def chargeQ (s : Fin 2 →₀ ℕ) : ℚ := charge s

/-- The discrete NC2 obstruction is exactly the rational straddling predicate
consumed by the lowest-face existence theorem. -/
theorem chargesStraddleZero_of_chargeStraddlesZero
    (P : MvPolynomial (Fin 2) ℂ) (h : ChargeStraddlesZero P) :
    GMC2.LowestFaceExistence.ChargesStraddleZero P.support chargeQ := by
  rcases h with hzero | ⟨hminus, hplus⟩
  · left
    obtain ⟨s, hs, hq⟩ := hzero
    refine ⟨s, hs, ?_⟩
    change (charge s : ℚ) = 0
    exact_mod_cast hq
  · right
    constructor
    · obtain ⟨s, hs, hq⟩ := hminus
      refine ⟨s, hs, ?_⟩
      change (charge s : ℚ) < 0
      exact_mod_cast hq
    · obtain ⟨s, hs, hq⟩ := hplus
      refine ⟨s, hs, ?_⟩
      change (0 : ℚ) < (charge s : ℚ)
      exact_mod_cast hq

/-- Failure of strict charge one-sidedness produces a rational lowest
supporting face whose equality set still meets or straddles charge zero. -/
theorem exists_rational_lowest_face_of_not_chargeOneSided
    (P : MvPolynomial (Fin 2) ℂ) (hP : ¬ChargeOneSided P) :
    ∃ lambda delta : ℚ,
      (∀ s ∈ P.support,
        delta ≤ radialExponentQ s - lambda * chargeQ s) ∧
      ((∃ s ∈ P.support, chargeQ s = 0 ∧
          radialExponentQ s - lambda * chargeQ s = delta) ∨
        ∃ s ∈ P.support, ∃ t ∈ P.support,
          chargeQ s < 0 ∧ 0 < chargeQ t ∧
          radialExponentQ s - lambda * chargeQ s = delta ∧
          radialExponentQ t - lambda * chargeQ t = delta) := by
  apply GMC2.LowestFaceExistence.exists_rational_lowest_balanced_face
  exact chargesStraddleZero_of_chargeStraddlesZero P
    ((not_chargeOneSided_iff_straddlesZero P).mp hP)

end GMC2

