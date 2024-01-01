/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Torsion points on Weierstrass curves
-/

open Polynomial PolynomialPolynomial

universe u

namespace WeierstrassCurve.Affine

variable {R : Type u} [CommRing R] (W : Affine R)

noncomputable def divisionPolynomial (n : ℤ) : R[X][Y] :=
  EllDivSequence (Y - W.negPolynomial)
    (C <| 3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈)
    (C <| 2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 +
        10 * C W.b₈ * X ^ 2 + C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2))
    n

@[simp]
lemma divisionPolynomial_zero : W.divisionPolynomial 0 = 0 :=
  EllDivSequence_zero _ _ _

@[simp]
lemma divisionPolynomial_one : W.divisionPolynomial 1 = 1 :=
  EllDivSequence_one _ _ _

@[simp]
lemma divisionPolynomial_two : W.divisionPolynomial 2 = Y - W.negPolynomial :=
  EllDivSequence_two _ _ _

@[simp]
lemma divisionPolynomial_three : W.divisionPolynomial 3 =
    C (3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈) :=
  EllDivSequence_three _ _ _

@[simp]
lemma divisionPolynomial_four : W.divisionPolynomial 4 =
    C (2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
        C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)) *
      (Y - W.negPolynomial) :=
  EllDivSequence_four _ _ _

@[simp]
lemma divisionPolynomial_odd (m : ℕ) : W.divisionPolynomial (2 * (m + 2) + 1) =
    W.divisionPolynomial (m + 4) * W.divisionPolynomial (m + 2) ^ 3 -
      W.divisionPolynomial (m + 1) * W.divisionPolynomial (m + 3) ^ 3 :=
  EllDivSequence_odd _ _ _ m

@[simp]
lemma divisionPolynomial_even (m : ℕ) : W.divisionPolynomial (2 * (m + 3)) * (Y - W.negPolynomial) =
    W.divisionPolynomial (m + 2) ^ 2 * W.divisionPolynomial (m + 3) * W.divisionPolynomial (m + 5) -
      W.divisionPolynomial (m + 1) * W.divisionPolynomial (m + 3) *
          W.divisionPolynomial (m + 4) ^ 2 :=
  EllDivSequence_even _ _ _ m

@[simp]
lemma divisionPolynomial_neg (n : ℕ) : W.divisionPolynomial (-n) = -W.divisionPolynomial n :=
  EllDivSequence_neg _ _ _ n

end WeierstrassCurve.Affine
