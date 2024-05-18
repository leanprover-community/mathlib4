/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Junyan Xu
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Universal
import Mathlib.Data.Int.Parity
import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Division polynomials for elliptic curves

This file defines division polynomials for elliptic curves and show they give a formula for
scalar multiplication on the group of rational points in Jacobian coordinates.

-/

universe u

namespace WeierstrassCurve.DivisionPolynomial

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open Polynomial

noncomputable section

def ψ : ℤ → R[X][X] :=
  normEDS (2 * X + C (C W.a₁ * X + C W.a₃))
    (C <| 3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈)
    (C <| 2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3
      + 10 * C W.b₈ * X ^ 2 + C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2))

def φ (n : ℤ) : R[X][X] := C X * ψ W n ^ 2 - ψ W (n + 1) * ψ W (n - 1)

def universalψ : ℤ → Universal.Poly := ψ Universal.curve
def universalφ : ℤ → Universal.Poly := φ Universal.curve


def universalω : ℤ → Universal.Poly := sorry

open Universal.Coeff in
open MvPolynomial (X) in
lemma universalω_spec (n : ℤ) : universalψ n *
    (2 * universalω n + C (C (X A₁)) * universalφ n * universalψ n + C (C (X A₃)) * universalψ n ^ 3)
    = universalψ (2 * n) := sorry

def ω (n : ℤ) : R[X][X] := (universalω n).map <| mapRingHom
  (MvPolynomial.aeval <| Universal.Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom



open Jacobian

end

end WeierstrassCurve.DivisionPolynomial
