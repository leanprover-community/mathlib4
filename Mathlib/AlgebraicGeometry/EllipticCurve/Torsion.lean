/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Group

/-!
# Torsion points on Weierstrass curves
-/

open Polynomial PolynomialPolynomial

universe u v

variable {R : Type u} [CommRing R] (W' : WeierstrassCurve R) {F : Type v} [Field F]
  {W : WeierstrassCurve F}

-- TODO: relocate
/-- The evaluation of a bivariate polynomial over a ring `R` at a pair of elements of `R`. -/
noncomputable def evalEval (x y : R) (p : R[X][Y]) : R :=
  (p.eval <| C y).eval x

namespace WeierstrassCurve

-- TODO: define in `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`
/-- The bivariate polynomials $\omega_n$. -/
protected noncomputable def ω (W' : WeierstrassCurve R) (n : ℤ) : R[X][Y] :=
  sorry

-- TODO: prove in `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.ZSMul`
theorem Affine.Point.zsmul {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    (n • (some h).toJacobian).point = ⟦evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]⟧ :=
  sorry

end WeierstrassCurve
