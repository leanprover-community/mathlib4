/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, David Kurniadi Angdinata
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Universal

/-!
# The omega division polynomials and related definitions

This file extends the division polynomial development from mathlib with the `ω` family of
division polynomials, the complement `ψc`, and the invariant `invar`, which are needed for
the `ZSMul` proof.

## Main definitions

 * `WeierstrassCurve.invar`: the "invariant" polynomial.
 * `WeierstrassCurve.ψc`: the complement of `ψ(n)` in `ψ(2n)`.
 * `WeierstrassCurve.ω`: the bivariate polynomials `ωₙ`.
 * `WeierstrassCurve.isEllSequence_ψ`: the `ψ` family forms an elliptic sequence.
-/

@[expose] public section
open Polynomial
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀,
    Polynomial.map_ofNat, Polynomial.map_one, map_C, map_X, Polynomial.map_neg, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_div, coe_mapRingHom,
    apply_ite <| mapRingHom _, WeierstrassCurve.map])

namespace WeierstrassCurve

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

noncomputable section

open Affine (polynomial polynomialX polynomialY negPolynomial)
open EllSequence
open WeierstrassCurve (ψ₂ ψ φ)

/-- The "invariant" that is equal to the quotient
`(ψ(n-1)²ψ(n+2)+ψ(n-2)ψ(n+1)²+ψ₂²ψ(n)³)/ψ(n+1)ψ(n)ψ(n-1)` for arbitrary `n`
modulo the Weierstrass polynomial. -/
def invar : R[X] := 6 * X ^ 2 + C W.b₂ * X + C W.b₄

/-- The complement of ψ(n) in ψ(2n). -/
def ψc : ℤ → R[X][Y] := compl₂EDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)

lemma isEllSequence_ψ : IsEllSequence W.ψ := IsEllSequence.normEDS

lemma C_Ψ₃_eq :
    C W.Ψ₃ = (3 * C X + CC W.a₂) * C W.Ψ₂Sq - polynomialX W ^ 2
      + CC W.a₁ * W.ψ₂ * polynomialX W - CC W.a₁ ^ 2 * polynomial W := by
  simp_rw [Ψ₃, Ψ₂Sq, polynomial, polynomialX, ψ₂, polynomialY, b₂, b₄, b₆, b₈, CC]; C_simp; ring

lemma preΨ₄_add_Ψ₂Sq_sq : W.preΨ₄ + W.Ψ₂Sq ^ 2 = W.invar * W.Ψ₃ := by
  rw [preΨ₄, Ψ₂Sq, invar, Ψ₃]
  linear_combination (norm := (C_simp; ring_nf)) congr(C $W.b_relation) * (@X R _) ^ 2

lemma preΨ₄_add_ψ₂_pow_four : C W.preΨ₄ + W.ψ₂ ^ 4 =
    C (W.invar * W.Ψ₃) + 8 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq) := by
  simp_rw [show 4 = 2 * 2 by rfl, pow_mul, ψ₂_sq, add_sq,
    ← add_assoc, ← C_pow, ← C_add, preΨ₄_add_Ψ₂Sq_sq]; C_simp; ring

lemma φ_mul_ψ (n : ℤ) : W.φ n * W.ψ n = C X * W.ψ n ^ 3 - invarDenom W.ψ 1 n := by
  rw [φ, invarDenom]; ring

/-- The `ω` family of division polynomials: `ω n` gives the second (`Y`) coordinate in
Jacobian coordinates of the scalar multiplication by `n`. -/
protected def ω (n : ℤ) : R[X][Y] :=
  redInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
    ((CC W.a₁ * polynomialY W - polynomialX W) * C W.Ψ₃
      + 4 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq))
  - compl₂EDSAux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3

open WeierstrassCurve (ω)

lemma ω_spec (n : ℤ) :
    2 * W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = W.ψc n := by
  rw [ψc, compl₂EDS_eq_redInvarNum_sub, redInvar_normEDS, preΨ₄_add_ψ₂_pow_four, mul_assoc (C _),
    φ_mul_ψ, ψ, invarDenom_eq_redInvarDenom_mul, ω, ← ψ, invar, b₂, b₄, ψ₂,
    polynomialY, polynomialX, negPolynomial]
  C_simp; ring

lemma two_mul_ω (n : ℤ) :
    2 * W.ω n = W.ψc n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 := by
  rw [← ω_spec]; abel

lemma ψc_spec (n : ℤ) : W.ψ n * W.ψc n = W.ψ (2 * n) := normEDS_mul_compl₂EDS _ _ _ _

@[simp] lemma ω_zero : W.ω 0 = 1 := by simp [ω]
@[simp] lemma ω_one : W.ω 1 = Y := by simp [ω, ψ₂, ← Affine.Y_sub_polynomialY]
@[simp] lemma ψc_neg (n : ℤ) : W.ψc (-n) = W.ψc n := by simp [ψc]

end

section Map

/-! ### Maps across ring homomorphisms -/

open WeierstrassCurve (Ψ Φ ψ φ ω)

variable (f : R →+* S)

open Affine EllSequence in
@[simp]
lemma map_ω (n : ℤ) : (W.map f).ω n = (W.ω n).map (mapRingHom f) := by
  simp_rw [ω, ← coe_mapRingHom, map_add, map_sub, map_mul, map_redInvarDenom, map_compl₂EDSAux,
    map_polynomial, map_polynomialX, map_polynomialY, map_negPolynomial, map_ψ₂, map_Ψ₃, map_preΨ₄,
    map_Ψ₂Sq, map_ψ]; simp

private lemma universal_ω_neg (n : ℤ) : letI W := Universal.curve
    W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 := by
  rw [← mul_cancel_left_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero Universal.Poly.two_ne_zero)]
  simp_rw [left_distrib, two_mul_ω, ψc_neg, ψ_neg, φ_neg]; ring

lemma ω_neg (n : ℤ) : W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 := by
  rw [← W.map_specialize, map_ω, universal_ω_neg, map_φ, map_ω, map_ψ]; simp

end Map

end WeierstrassCurve
