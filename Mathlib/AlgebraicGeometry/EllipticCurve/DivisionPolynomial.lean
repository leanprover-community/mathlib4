/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Junyan Xu
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Universal
import Mathlib.Data.Int.Parity
import Mathlib.LinearAlgebra.SModEq
import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Division polynomials for elliptic curves

This file defines division polynomials for elliptic curves and show they give a formula for
scalar multiplication on the group of rational points in Jacobian coordinates.

-/

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)

open Polynomial

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

noncomputable section

open scoped PolynomialPolynomial

/-- The second division polynomial. -/
protected def ψ₂ : R[X][X] := 2 * Y + C (C W.a₁ * X + C W.a₃)
/- Implementation note: protect to force the use of dot notation,
   since ψ etc. are common variable names. -/

/-- A single variable polynomial congruent to the square of the second division polynomial
modulo the Weierstrass polynomial. -/
protected def ψ₂Sq : R[X] := 4 * X ^ 3 + C W.b₂ * X ^ 2 + 2 * C W.b₄ * X + C W.b₆

/-- The third division polynomial, in a single variable. -/
protected def ψ₃ : R[X] := 3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈

/-- The complement of the second division polynomial in the fourth, in a single variable. -/
protected def ψc₂ : R[X] := 2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3
  + 10 * C W.b₈ * X ^ 2 + C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)

/-- The "invariant" that is equal to the quotient `( )/ψ(n+1)ψ(n)ψ(n-1)`
modulo the Weierstrass polynomial for arbitary `n.` -/
def invar : R[X] := 6 * X ^ 2 + C W.b₂ * X + C W.b₄

/-- The `ψ` family of division polynomials is the normalised EDS given by the initial values
ψ₂, ψ₃, and ψc₂. `ψ n` gives the last (`Z`) coordinate in Jacobian coordinates of the scalar
multiplication by the integer `n` of a point on a Weierstrass curve. -/
protected def ψ : ℤ → R[X][X] := normEDS W.ψ₂ (C W.ψ₃) (C W.ψc₂)

/-- The `φ` family of division polynomials; `φ n` gives the first (`X`) coordinate in
Jacobian coordinates of the scalar multiplication by `n`. -/
protected def φ (n : ℤ) : R[X][X] := C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)

/-- The complement of ψ(n) in ψ(2n). -/
def ψc : ℤ → R[X][X] := compl₂EDS W.ψ₂ (C W.ψ₃) (C W.ψc₂)

open Affine (polynomial)
open EllSequence

open WeierstrassCurve (ψc₂ ψ₂ ψ₂Sq ψ₃ ψ φ ψc)

lemma ψ₂_sq : W.ψ₂ ^ 2 = C W.ψ₂Sq + 4 * polynomial W := by
  rw [Affine.polynomial, ψ₂, ψ₂Sq, b₂, b₄, b₆]; C_simp; ring

lemma ψc₂_add_ψ₂Sq_sq : W.ψc₂ + W.ψ₂Sq ^ 2 = W.invar * W.ψ₃ := by
  rw [ψc₂, ψ₂Sq, invar, ψ₃]
  linear_combination (norm := (C_simp; ring_nf)) congr(C $W.b_relation) * (@X R _) ^ 2

lemma ψc₂_add_ψ₂_pow_four :
    C W.ψc₂ + W.ψ₂ ^ 4 = C (W.invar * W.ψ₃) + 8 * polynomial W * (2 * polynomial W + C W.ψ₂Sq) := by
  simp_rw [show 4 = 2 * 2 by rfl, pow_mul, ψ₂_sq, add_sq,
    ← add_assoc, ← C_pow, ← C_add, ψc₂_add_ψ₂Sq_sq]; C_simp; ring

/-- The `ω` family of division polynomials: `ω n` gives the second (`Y`) coordinate in
Jacobian coordinates of the scalar multiplication by `n`. -/
protected def ω (n : ℤ) : R[X][X] :=
  redInvarDenom W.ψ₂ (C W.ψ₃) (C W.ψc₂) n *
    ((C (C W.a₁) * Y + C (3 * X ^ 2 + C (W.b₂ - 2 * W.a₂) * X + C (W.b₄ - W.a₄))) * C W.ψ₃
      + 4 * polynomial W * (2 * polynomial W + C W.ψ₂Sq))
  - invarNumAux W.ψ₂ (C W.ψ₃) (C W.ψc₂) n - (Y + C (C W.a₁ * X + C W.a₃)) * W.ψ n ^ 3

lemma φ_mul_ψ (n : ℤ) : W.φ n * W.ψ n = C X * W.ψ n ^ 3 - invarDenom W.ψ 1 n := by
  rw [φ, invarDenom]; ring

open WeierstrassCurve (ω)
lemma ω_spec (n : ℤ) :
    2 * W.ω n + C (C W.a₁) * W.φ n * W.ψ n + C (C W.a₃) * W.ψ n ^ 3 = W.ψc n := by
  rw [ψc, compl₂EDS_eq_redInvarNum_sub, redInvar_normEDS₂, ψc₂_add_ψ₂_pow_four,
    mul_assoc (C _), φ_mul_ψ, ψ, invarDenom_eq_redInvarDenom_mul, ω, ← ψ, invar, b₂, b₄, ψ₂]
  C_simp; ring

lemma ψc_spec (n : ℤ) : W.ψ n * W.ψc n = W.ψ (2 * n) := normEDS_mul_compl₂EDS _ _ _ _

@[simp] lemma map_ψ₂ : (W.map f).ψ₂ = W.ψ₂.map (mapRingHom f) := by simp [ψ₂]
@[simp] lemma map_ψ₃ : (W.map f).ψ₃ = W.ψ₃.map f := by simp [ψ₃]
@[simp] lemma map_ψc₂ : (W.map f).ψc₂ = W.ψc₂.map f := by simp [ψc₂]
@[simp] lemma map_ψ₂Sq : (W.map f).ψ₂Sq = W.ψ₂Sq.map f := by simp [ψ₂Sq]

@[simp] lemma map_ψ (n : ℤ) : (W.map f).ψ n = (W.ψ n).map (mapRingHom f) := by
  simp_rw [ψ, ← coe_mapRingHom, map_normEDS]; simp

@[simp] lemma map_φ (n : ℤ) : (W.map f).φ n = (W.φ n).map (mapRingHom f) := by simp [φ]

@[simp] lemma map_ω (n : ℤ) : (W.map f).ω n = (W.ω n).map (mapRingHom f) := by
  simp_rw [ω, ← coe_mapRingHom, map_sub, map_mul, map_redInvarDenom, map_invarNumAux]
  simp [Affine.map_polynomial]




open Jacobian

end

end WeierstrassCurve.DivisionPolynomial
