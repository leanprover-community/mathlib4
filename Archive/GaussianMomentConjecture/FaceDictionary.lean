/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.FrobeniusFace
import Archive.GaussianMomentConjecture.LowestFacePackage
import Mathlib.Data.Finsupp.Defs

/-!
# Dictionary between polynomial bidegrees and Frobenius-face coordinates

The existence layer uses `GMC2.charge` on natural Finsupp bidegrees, whereas
the face arithmetic layer accepts arbitrary integer exponent functions.  The
two representations are definitionally the same after the natural casts; the
lemmas here make that cross-module transport explicit.
-/

namespace GMC2.FaceDictionary

/-- Integer `Z`- and `W`-exponents of an exact bidegree. -/
def exponentA (s : Fin 2 →₀ ℕ) : ℤ := s 0

def exponentB (s : Fin 2 →₀ ℕ) : ℤ := s 1

@[simp] theorem charge_eq (s : Fin 2 →₀ ℕ) :
    GMC2.FrobeniusFace.charge exponentA exponentB s = GMC2.charge s := by
  simp [GMC2.FrobeniusFace.charge, exponentA, exponentB, GMC2.charge]

@[simp] theorem tiltedHeight_eq (lambda : ℚ) (s : Fin 2 →₀ ℕ) :
    GMC2.FrobeniusFace.tiltedHeight exponentA exponentB lambda s =
      GMC2.radialExponentQ s - lambda * GMC2.chargeQ s := by
  simp [GMC2.FrobeniusFace.tiltedHeight, GMC2.radialExponentQ, GMC2.chargeQ]
  norm_cast

end GMC2.FaceDictionary

