/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Negation and addition formulae for nonsingular points in affine coordinates

Let `W` be a Weierstrass curve over a field `F` with coefficients `aᵢ`. The nonsingular affine
points on `W` can be given negation and addition operations defined by a secant-and-tangent process.
* Given a nonsingular affine point `P`, its *negation* `-P` is defined to be the unique third
  nonsingular point of intersection between `W` and the vertical line through `P`.
  Explicitly, if `P` is `(x, y)`, then `-P` is `(x, -y - a₁x - a₃)`.
* Given two nonsingular affine points `P` and `Q`, their *addition* `P + Q` is defined to be the
  negation of the unique third nonsingular point of intersection between `W` and the line `L`
  through `P` and `Q`. Explicitly, let `P` be `(x₁, y₁)` and let `Q` be `(x₂, y₂)`.
    * If `x₁ = x₂` and `y₁ = -y₂ - a₁x₂ - a₃`, then `L` is vertical.
    * If `x₁ = x₂` and `y₁ ≠ -y₂ - a₁x₂ - a₃`, then `L` is the tangent of `W` at `P = Q`, and has
      slope `ℓ := (3x₁² + 2a₂x₁ + a₄ - a₁y₁) / (2y₁ + a₁x₁ + a₃)`.
    * Otherwise `x₁ ≠ x₂`, then `L` is the secant of `W` through `P` and `Q`, and has slope
      `ℓ := (y₁ - y₂) / (x₁ - x₂)`.

  In the last two cases, the `X`-coordinate of `P + Q` is then the unique third solution of the
  equation obtained by substituting the line `Y = ℓ(X - x₁) + y₁` into the Weierstrass equation,
  and can be written down explicitly as `x := ℓ² + a₁ℓ - a₂ - x₁ - x₂` by inspecting the
  coefficients of `X²`. The `Y`-coordinate of `P + Q`, after applying the final negation that maps
  `Y` to `-Y - a₁X - a₃`, is precisely `y := -(ℓ(x - x₁) + y₁) - a₁x - a₃`.

This file defines polynomials associated to negation and addition of nonsingular affine points,
including slopes of non-vertical lines. The actual group law on nonsingular points in affine
coordinates will be defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`.

## Main definitions

* `WeierstrassCurve.Affine.negY`: the `Y`-coordinate of `-P`.
* `WeierstrassCurve.Affine.addX`: the `X`-coordinate of `P + Q`.
* `WeierstrassCurve.Affine.negAddY`: the `Y`-coordinate of `-(P + Q)`.
* `WeierstrassCurve.Affine.addY`: the `Y`-coordinate of `P + Q`.

## Main statements

* `WeierstrassCurve.Affine.equation_neg`: negation preserves the Weierstrass equation.
* `WeierstrassCurve.Affine.nonsingular_neg`: negation preserves the nonsingular condition.
* `WeierstrassCurve.Affine.equation_add`: addition preserves the Weierstrass equation.
* `WeierstrassCurve.Affine.nonsingular_add`: addition preserves the nonsingular condition.

## Implementation notes

For ease of naming, the following conventions will be used in theorems about nonsingular affine
points `(x₁, y₁)` and `(x₂, y₂)` on a Weierstrass curve `W` over a commutative ring `R`.
* `X_eq` is the condition `x₁ = x₂`.
* `X_ne` is the condition `IsUnit <| x₁ - x₂` (which is equivalent to `x₁ ≠ x₂` if `R` is a field).
* `Y_eq` is the condition `y₁ = y₂` assuming `X_eq`.
* `Y_ne` is the condition `IsUnit <| y₁ - y₂` (which is equivalent to `y₁ ≠ y₂` if `R` is a field)
  assuming `X_eq`.
* `Y_eq'` is the condition `y₁ = W.negY x₂ y₂` assuming `X_eq`.
* `Y_ne'` is the condition `IsUnit <| y₁ - W.negY x₂ y₂` (which is equivalent to `y₁ ≠ W.negY x₂ y₂`
  if `R` is a field) assuming `X_eq`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, affine, negation, doubling, addition, group law
-/

open Polynomial

open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

local macro "derivative_simp" : tactic =>
  `(tactic| simp only [derivative_C, derivative_X, derivative_X_pow, derivative_neg, derivative_add,
    derivative_sub, derivative_mul, derivative_sq])

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_zero, eval_one, eval_neg, eval_add, eval_sub, eval_mul,
    eval_pow, evalEval])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀,
    Polynomial.map_ofNat, map_C, map_X, Polynomial.map_neg, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_div, coe_mapRingHom,
    WeierstrassCurve.map])

universe r s u v w

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Field F] [Field K] {W' : Affine R} {W : Affine F}

namespace Affine

/-! ## Negation formulae in affine coordinates -/

variable (W') in
/-- The negation polynomial `-Y - a₁X - a₃` associated to the negation of a nonsingular affine point
on a Weierstrass curve. -/
noncomputable def negPolynomial : R[X][Y] :=
  -(Y : R[X][Y]) - C (C W'.a₁ * X + C W'.a₃)

lemma Y_sub_polynomialY : Y - W'.polynomialY = W'.negPolynomial := by
  rw [polynomialY, negPolynomial]
  C_simp
  ring1

lemma Y_sub_negPolynomial : Y - W'.negPolynomial = W'.polynomialY := by
  rw [← Y_sub_polynomialY, sub_sub_cancel]

variable (W') in
/-- The `Y`-coordinate of `-(x, y)` for a nonsingular affine point `(x, y)` on a Weierstrass curve
`W`.

This depends on `W`, and has argument order: `x`, `y`. -/
@[simp]
def negY (x y : R) : R :=
  -y - W'.a₁ * x - W'.a₃

lemma negY_negY (x y : R) : W'.negY x (W'.negY x y) = y := by
  simp_rw [negY]
  ring1

lemma evalEval_negPolynomial (x y : R) : W'.negPolynomial.evalEval x y = W'.negY x y := by
  rw [negY, sub_sub, negPolynomial]
  eval_simp

@[deprecated (since := "2025-03-05")] alias eval_negPolynomial := evalEval_negPolynomial

lemma Y_sub_Y_mul_Y_sub_negY_of_X_eq {x₁ x₂ y₁ y₂ : R} (h₁ : W'.Equation x₁ y₁)
    (h₂ : W'.Equation x₂ y₂) (hx : x₁ = x₂) : (y₁ - y₂) * (y₁ - W'.negY x₂ y₂) = 0 := by
  linear_combination (norm := (rw [hx, negY]; ring1))
    (equation_iff ..).mp h₁ - (equation_iff ..).mp h₂

lemma Y_eq_or_Y_eq'_of_X_eq [NoZeroDivisors R] {x₁ x₂ y₁ y₂ : R} (h₁ : W'.Equation x₁ y₁)
    (h₂ : W'.Equation x₂ y₂) (hx : x₁ = x₂) : y₁ = y₂ ∨ y₁ = W'.negY x₂ y₂ := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := y₁), ← mul_eq_zero,
    Y_sub_Y_mul_Y_sub_negY_of_X_eq h₁ h₂ hx]

@[deprecated (since := "2025-05-26")] alias Y_eq_of_X_eq := Y_eq_or_Y_eq'_of_X_eq

lemma Y_eq'_of_Y_ne {x₁ x₂ y₁ y₂ : R} (h₁ : W'.Equation x₁ y₁) (h₂ : W'.Equation x₂ y₂)
    (hx : x₁ = x₂) (hy : IsUnit <| y₁ - y₂) : y₁ = W'.negY x₂ y₂ :=
  sub_eq_zero.mp <| hy.mul_right_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY_of_X_eq h₁ h₂ hx

lemma Y_eq_of_Y_ne' {x₁ x₂ y₁ y₂ : R} (h₁ : W'.Equation x₁ y₁) (h₂ : W'.Equation x₂ y₂)
    (hx : x₁ = x₂) (hy : IsUnit <| y₁ - W'.negY x₂ y₂) : y₁ = y₂ :=
  sub_eq_zero.mp <| hy.mul_left_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY_of_X_eq h₁ h₂ hx

@[deprecated (since := "2025-05-26")] alias Y_eq_of_Y_ne := Y_eq_of_Y_ne'

lemma equation_neg (x y : R) : W'.Equation x (W'.negY x y) ↔ W'.Equation x y := by
  rw [equation_iff, equation_iff, negY]
  congr! 1
  ring1

@[deprecated (since := "2025-02-01")] alias equation_neg_of := equation_neg
@[deprecated (since := "2025-02-01")] alias equation_neg_iff := equation_neg

lemma nonsingular_neg (x y : R) : W'.Nonsingular x (W'.negY x y) ↔ W'.Nonsingular x y := by
  rw [nonsingular_iff, equation_neg, negY, ← Ideal.span_pair_add_right_mul _ _ <| -W'.a₁,
    ← Ideal.span_pair_neg, nonsingular_iff]
  ring_nf

@[deprecated (since := "2025-02-01")] alias nonsingular_neg_of := nonsingular_neg
@[deprecated (since := "2025-02-01")] alias nonsingular_neg_iff := nonsingular_neg

/-! ## Slope formulae in affine coordinates -/

variable (W') in
/-- The line polynomial `ℓ(X - x) + y` associated to the line `Y = ℓ(X - x) + y` that passes through
a nonsingular affine point `(x, y)` on a Weierstrass curve `W` with a slope of `ℓ`.

This does not depend on `W`, and has argument order: `x`, `y`, `ℓ`. -/
noncomputable def linePolynomial (x y ℓ : R) : R[X] :=
  C ℓ * (X - C x) + C y

open scoped Classical in
variable (W) in
/-- The slope of the line through two nonsingular affine points `(x₁, y₁)` and `(x₂, y₂)` on a
Weierstrass curve `W`.

If `x₁ ≠ x₂`, then this line is the secant of `W` through `(x₁, y₁)` and `(x₂, y₂)`, and has slope
`(y₁ - y₂) / (x₁ - x₂)`. Otherwise, if `y₁ ≠ -y₂ - a₁x₂ - a₃`, then this line is the tangent of `W`
at `(x₁, y₁) = (x₂, y₂)`, and has slope `(3x₁² + 2a₂x₁ + a₄ - a₁y₁) / (y₁ - (-y₂ - a₁x₂ - a₃))`.
Otherwise, this line is vertical, in which case this returns the value `0`.

Note that this definition is only mathematically accurate if `x₁ = x₂` whenever `x₁ - x₂` is not a
unit, and if `y₁ = -y₂ - a₁x₂ - a₃` whenever `y₁ - (-y₂ - a₁x₂ - a₃)` is not a unit.

This depends on `W`, and has argument order: `x₁`, `x₂`, `y₁`, `y₂`. -/
noncomputable def slope (x₁ x₂ y₁ y₂ : R) : R :=
  if hx : IsUnit <| x₁ - x₂ then (y₁ - y₂) * hx.unit⁻¹ else if hy : IsUnit <| y₁ - W'.negY x₂ y₂
    then (3 * x₁ ^ 2 + 2 * W'.a₂ * x₁ + W'.a₄ - W'.a₁ * y₁) * hy.unit⁻¹ else 0

lemma slope_of_X_ne {x₁ x₂ y₁ y₂ : R} (hx : IsUnit <| x₁ - x₂) :
    W'.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) * hx.unit⁻¹ := by
  rw [slope, dif_pos hx]

lemma slope_of_X_ne_of_isField {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
    W.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) := by
  rw [← sub_ne_zero, ← isUnit_iff_ne_zero] at hx
  rw [slope_of_X_ne hx, Units.val_inv_eq_inv_val, hx.unit_spec, div_eq_mul_inv]

lemma slope_of_Y_ne' [Nontrivial R] {x₁ x₂ y₁ y₂ : R} (hx : x₁ = x₂)
    (hy : IsUnit <| y₁ - W'.negY x₂ y₂) :
    W'.slope x₁ x₂ y₁ y₂ = (3 * x₁ ^ 2 + 2 * W'.a₂ * x₁ + W'.a₄ - W'.a₁ * y₁) * hy.unit⁻¹ := by
  rw [slope, hx, sub_self, dif_neg not_isUnit_zero, dif_pos hy]

@[deprecated (since := "2025-05-26")] alias slope_of_Y_ne := slope_of_Y_ne'

lemma slope_of_Y_ne'_of_isField {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) : W.slope x₁ x₂ y₁ y₂ =
      (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.negY x₁ y₁) := by
  rw [← sub_ne_zero, ← isUnit_iff_ne_zero] at hy
  simp_rw [slope_of_Y_ne' hx hy, hx, Y_eq_of_Y_ne' h₁ h₂ hx hy, Units.val_inv_eq_inv_val,
    IsUnit.unit_spec, div_eq_mul_inv]

lemma slope_of_Y_ne'_eq_evalEval {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) :
    W.slope x₁ x₂ y₁ y₂ = -W.polynomialX.evalEval x₁ y₁ / W.polynomialY.evalEval x₁ y₁ := by
  rw [slope_of_Y_ne'_of_isField h₁ h₂ hx hy, evalEval_polynomialX, neg_sub, ← Y_sub_negPolynomial,
    evalEval_sub, evalEval_X, evalEval_negPolynomial]

@[deprecated (since := "2025-03-05")] alias slope_of_Y_ne_eq_evalEval := slope_of_Y_ne'_eq_evalEval
@[deprecated (since := "2025-03-05")] alias slope_of_Y_ne_eq_eval := slope_of_Y_ne'_eq_evalEval

lemma slope_of_Y_eq' [Nontrivial R] {x₁ x₂ y₁ y₂ : R} (hx : x₁ = x₂) (hy : y₁ = W'.negY x₂ y₂) :
    W'.slope x₁ x₂ y₁ y₂ = 0 := by
  rw [slope, hx, sub_self, dif_neg not_isUnit_zero, hy, sub_self, dif_neg not_isUnit_zero]

@[deprecated (since := "2025-05-26")] alias slope_of_Y_eq := slope_of_Y_eq'

/-! ## Addition formulae in affine coordinates -/

variable (W') in
/-- The addition polynomial obtained by substituting the line `Y = ℓ(X - x) + y` into the polynomial
`W(X, Y)` associated to a Weierstrass curve `W`. If such a line intersects `W` at another
nonsingular affine point `(x', y')` on `W`, then the roots of this polynomial are precisely `x`,
`x'`, and the `X`-coordinate of the addition of `(x, y)` and `(x', y')`.

This depends on `W`, and has argument order: `x`, `y`, `ℓ`. -/
noncomputable def addPolynomial (x y ℓ : R) : R[X] :=
  W'.polynomial.eval <| linePolynomial x y ℓ

lemma C_addPolynomial (x y ℓ : R) : C (W'.addPolynomial x y ℓ) =
    (Y - C (linePolynomial x y ℓ)) * (W'.negPolynomial - C (linePolynomial x y ℓ)) +
      W'.polynomial := by
  rw [addPolynomial, linePolynomial, polynomial, negPolynomial]
  eval_simp
  C_simp
  ring1

lemma addPolynomial_eq (x y ℓ : R) : W'.addPolynomial x y ℓ = -Cubic.toPoly
    ⟨1, -ℓ ^ 2 - W'.a₁ * ℓ + W'.a₂,
      2 * x * ℓ ^ 2 + (W'.a₁ * x - 2 * y - W'.a₃) * ℓ + (-W'.a₁ * y + W'.a₄),
      -x ^ 2 * ℓ ^ 2 + (2 * x * y + W'.a₃ * x) * ℓ - (y ^ 2 + W'.a₃ * y - W'.a₆)⟩ := by
  rw [addPolynomial, linePolynomial, polynomial, Cubic.toPoly]
  eval_simp
  C_simp
  ring1

variable (W') in
/-- The `X`-coordinate of `(x₁, y₁) + (x₂, y₂)` for two nonsingular affine points `(x₁, y₁)` and
`(x₂, y₂)` on a Weierstrass curve `W`, where the line through them has a slope of `ℓ`.

This depends on `W`, and has argument order: `x₁`, `x₂`, `ℓ`. -/
@[simp]
def addX (x₁ x₂ ℓ : R) : R :=
  ℓ ^ 2 + W'.a₁ * ℓ - W'.a₂ - x₁ - x₂

variable (W') in
/-- The `Y`-coordinate of `-((x₁, y₁) + (x₂, y₂))` for two nonsingular affine points `(x₁, y₁)` and
`(x₂, y₂)` on a Weierstrass curve `W`, where the line through them has a slope of `ℓ`.

This depends on `W`, and has argument order: `x₁`, `x₂`, `y₁`, `ℓ`. -/
@[simp]
def negAddY (x₁ x₂ y₁ ℓ : R) : R :=
  ℓ * (W'.addX x₁ x₂ ℓ - x₁) + y₁

variable (W') in
/-- The `Y`-coordinate of `(x₁, y₁) + (x₂, y₂)` for two nonsingular affine points `(x₁, y₁)` and
`(x₂, y₂)` on a Weierstrass curve `W`, where the line through them has a slope of `ℓ`.

This depends on `W`, and has argument order: `x₁`, `x₂`, `y₁`, `ℓ`. -/
@[simp]
def addY (x₁ x₂ y₁ ℓ : R) : R :=
  W'.negY (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ)

lemma addPolynomial_slope [Nontrivial R] {x₁ x₂ y₁ y₂ : R} (h₁ : W'.Equation x₁ y₁)
    (h₂ : W'.Equation x₂ y₂) (hxy : x₁ = x₂ → IsUnit (y₁ - W'.negY x₂ y₂))
    (hxx : x₁ ≠ x₂ → IsUnit (x₁ - x₂)) : W'.addPolynomial x₁ y₁ (W'.slope x₁ x₂ y₁ y₂) =
      -((X - C x₁) * (X - C x₂) * (X - C (W'.addX x₁ x₂ <| W'.slope x₁ x₂ y₁ y₂))) := by
  rw [addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective]
  by_cases hx : x₁ = x₂
  · have hy : IsUnit <| y₁ - W'.negY x₂ y₂ := hxy hx
    rcases hx, Y_eq_of_Y_ne' h₁ h₂ hx hy with ⟨rfl, rfl⟩
    rw [slope_of_Y_ne' rfl hy]
    ext
    · rfl
    · linear_combination (norm := (rw [addX]; ring1))
    · linear_combination (norm := (simp_rw [evalEval_polynomialX, addX, negY]; ring1))
        W'.polynomialX.evalEval x₁ y₁ * hy.mul_val_inv
    · linear_combination (norm := (simp_rw [evalEval_polynomialX, addX, negY]; ring1))
        -(equation_iff ..).mp h₂ - W'.polynomialX.evalEval x₁ y₁ * x₁ * hy.mul_val_inv
  · replace hx : IsUnit <| x₁ - x₂ := hxx hx
    rw [slope_of_X_ne hx]
    ext
    · rfl
    · linear_combination (norm := (rw [addX]; ring1))
    · linear_combination (norm := (rw [addX]; ring1)) -↑hx.unit⁻¹ * (equation_iff ..).mp h₁
        + ↑hx.unit⁻¹ * (equation_iff ..).mp h₂ + ((y₁ - y₂) ^ 2 * ↑hx.unit⁻¹
        + W'.a₁ * y₁ - (W'.a₂ + x₁ + x₂) * (x₁ + x₂) + x₁ * x₂ - W'.a₄) * hx.mul_val_inv
    · linear_combination (norm := (rw [addX]; ring1)) x₂ * ↑hx.unit⁻¹ * (equation_iff ..).mp h₁
        - x₁ * ↑hx.unit⁻¹ * (equation_iff ..).mp h₂ + (-x₁ * (y₁ - y₂) ^ 2 * ↑hx.unit⁻¹
        + (W'.a₃ + y₁) * y₁ + (W'.a₂ + x₁ + x₂) * x₁ * x₂ - W'.a₆) * hx.mul_val_inv

lemma C_addPolynomial_slope [Nontrivial R] {x₁ x₂ y₁ y₂ : R} (h₁ : W'.Equation x₁ y₁)
    (h₂ : W'.Equation x₂ y₂) (hxy : x₁ = x₂ → IsUnit (y₁ - W'.negY x₂ y₂))
    (hxx : x₁ ≠ x₂ → IsUnit (x₁ - x₂)) : C (W'.addPolynomial x₁ y₁ <| W'.slope x₁ x₂ y₁ y₂) =
      -(C (X - C x₁) * C (X - C x₂) * C (X - C (W'.addX x₁ x₂ <| W'.slope x₁ x₂ y₁ y₂))) := by
  rw [addPolynomial_slope h₁ h₂ hxy hxx]
  map_simp

lemma derivative_addPolynomial_slope [Nontrivial R] {x₁ x₂ y₁ y₂ : R} (h₁ : W'.Equation x₁ y₁)
    (h₂ : W'.Equation x₂ y₂) (hxy : x₁ = x₂ → IsUnit (y₁ - W'.negY x₂ y₂))
    (hxx : x₁ ≠ x₂ → IsUnit (x₁ - x₂)) :
    derivative (W'.addPolynomial x₁ y₁ <| W'.slope x₁ x₂ y₁ y₂) =
      -((X - C x₁) * (X - C x₂) + (X - C x₁) * (X - C (W'.addX x₁ x₂ <| W'.slope x₁ x₂ y₁ y₂)) +
          (X - C x₂) * (X - C (W'.addX x₁ x₂ <| W'.slope x₁ x₂ y₁ y₂))) := by
  rw [addPolynomial_slope h₁ h₂ hxy hxx]
  derivative_simp
  ring1

lemma equation_add_iff (x₁ x₂ y₁ ℓ : R) : W'.Equation (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ) ↔
    (W'.addPolynomial x₁ y₁ ℓ).eval (W'.addX x₁ x₂ ℓ) = 0 := by
  rw [Equation, negAddY, addPolynomial, linePolynomial, polynomial]
  eval_simp

lemma equation_negAdd [Nontrivial R] {x₁ x₂ y₁ y₂ : R} (h₁ : W'.Equation x₁ y₁)
    (h₂ : W'.Equation x₂ y₂) (hxy : x₁ = x₂ → IsUnit (y₁ - W'.negY x₂ y₂))
    (hxx : x₁ ≠ x₂ → IsUnit (x₁ - x₂)) : W'.Equation
      (W'.addX x₁ x₂ <| W'.slope x₁ x₂ y₁ y₂) (W'.negAddY x₁ x₂ y₁ <| W'.slope x₁ x₂ y₁ y₂) := by
  rw [equation_add_iff, addPolynomial_slope h₁ h₂ hxy hxx]
  eval_simp
  rw [neg_eq_zero, sub_self, mul_zero]

lemma equation_add [Nontrivial R] {x₁ x₂ y₁ y₂ : R} (h₁ : W'.Equation x₁ y₁)
    (h₂ : W'.Equation x₂ y₂) (hxy : x₁ = x₂ → IsUnit (y₁ - W'.negY x₂ y₂))
    (hxx : x₁ ≠ x₂ → IsUnit (x₁ - x₂)) : W'.Equation
      (W'.addX x₁ x₂ <| W'.slope x₁ x₂ y₁ y₂) (W'.addY x₁ x₂ y₁ <| W'.slope x₁ x₂ y₁ y₂) :=
  (equation_neg ..).mpr <| equation_negAdd h₁ h₂ hxy hxx

lemma nonsingular_negAdd_of_isUnit_eval_derivative {x₁ x₂ y₁ ℓ : R}
    (hx' : W'.Equation (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ))
    (hx : IsUnit <| (W'.addPolynomial x₁ y₁ ℓ).derivative.eval <| W'.addX x₁ x₂ ℓ) :
    W'.Nonsingular (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ) := by
  revert hx
  rw [addPolynomial, linePolynomial, polynomial, Nonsingular, and_iff_right hx', negAddY,
    polynomialX, polynomialY]
  eval_simp
  derivative_simp
  eval_simp
  exact Ideal.eq_top_of_isUnit_mem _ <| Ideal.mem_span_pair.mpr ⟨1, ℓ, by ring1⟩

@[deprecated (since := "2025-05-26")] alias nonsingular_negAdd_of_eval_derivative_ne_zero :=
  nonsingular_negAdd_of_isUnit_eval_derivative

lemma nonsingular_negAdd {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) : W.Nonsingular
      (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.negAddY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  by_cases hx₁ : x₁ = W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
  · rwa [negAddY, ← hx₁, sub_self, mul_zero, zero_add]
  · by_cases hx₂ : x₂ = W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
    · rwa [negAddY, ← hx₂, ← neg_sub, mul_neg, slope_of_X_ne (sub_ne_zero.mpr <| hx₂ ▸ hx₁).isUnit,
        mul_assoc, IsUnit.val_inv_mul, mul_one, neg_sub, sub_add_cancel]
    · replace hxy := fun hx => (sub_ne_zero.mpr <| hxy hx).isUnit
      have hxx : x₁ ≠ x₂ → IsUnit (x₁ - x₂) := fun hx => (sub_ne_zero.mpr hx).isUnit
      apply nonsingular_negAdd_of_isUnit_eval_derivative <| equation_negAdd h₁.left h₂.left hxy hxx
      rw [derivative_addPolynomial_slope h₁.left h₂.left hxy hxx]
      eval_simp
      simp_rw [sub_self, mul_zero, add_zero, IsUnit.neg_iff, IsUnit.mul_iff, IsUnit.sub_iff]
      exact ⟨(sub_ne_zero.mpr hx₁).isUnit, (sub_ne_zero.mpr hx₂).isUnit⟩

lemma nonsingular_add {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) : W.Nonsingular
      (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) :=
  (nonsingular_neg ..).mpr <| nonsingular_negAdd h₁ h₂ hxy

/-- The formula `x(P₁ + P₂) = x(P₁ - P₂) - ψ(P₁)ψ(P₂) / (x(P₂) - x(P₁))²`,
where `ψ(x,y) = 2y + a₁x + a₃`. -/
lemma addX_eq_addX_negY_sub {x₁ x₂ y₁ y₂ : R} (hx : IsUnit <| x₁ - x₂) :
    W'.addX x₁ x₂ (W'.slope x₁ x₂ y₁ y₂) = W'.addX x₁ x₂ (W'.slope x₁ x₂ y₁ <| W'.negY x₂ y₂) -
      (y₁ - W'.negY x₁ y₁) * (y₂ - W'.negY x₂ y₂) * hx.unit⁻¹ ^ 2 := by
  linear_combination (norm := (simp_rw [slope_of_X_ne hx, addX, negY]; ring1))
    W'.a₁ * (y₂ - W'.negY x₂ y₂) * ↑hx.unit⁻¹ * hx.mul_val_inv

/-- The formula `y(P₁)(x(P₂) - x(P₃)) + y(P₂)(x(P₃) - x(P₁)) + y(P₃)(x(P₁) - x(P₂)) = 0`,
assuming that `P₁ + P₂ + P₃ = O`. -/
lemma cyclic_sum_Y_mul_X_sub_X {x₁ x₂ y₁ y₂ : R} (hx : IsUnit <| x₁ - x₂) :
    y₁ * (x₂ - W'.addX x₁ x₂ (W'.slope x₁ x₂ y₁ y₂))
      + y₂ * (W'.addX x₁ x₂ (W'.slope x₁ x₂ y₁ y₂) - x₁)
      + W'.negAddY x₁ x₂ y₁ (W'.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) = 0 := by
  linear_combination (norm := (rw [slope_of_X_ne hx, negAddY, addX]; ring1))
    (y₁ - y₂) * (W'.addX x₁ x₂ (W'.slope x₁ x₂ y₁ y₂) - x₁) * hx.mul_val_inv

/-- The formula `ψ(P₁ + P₂) = (ψ(P₁)(x(P₂) - x(P₃)) - ψ(P₂)(x(P₁) - x(P₃))) / (x(P₁) - x(P₂))`,
where `ψ(x,y) = 2y + a₁x + a₃`. -/
lemma addY_sub_negY_addY {x₁ x₂ y₁ y₂ : R} (hx : IsUnit <| x₁ - x₂) :
    W'.addY x₁ x₂ y₁ (W'.slope x₁ x₂ y₁ y₂) -
        W'.negY (W'.addX x₁ x₂ <| W'.slope x₁ x₂ y₁ y₂) (W'.addY x₁ x₂ y₁ <| W'.slope x₁ x₂ y₁ y₂) =
      ((y₁ - W'.negY x₁ y₁) * (x₂ - W'.addX x₁ x₂ (W'.slope x₁ x₂ y₁ y₂)) -
          (y₂ - W'.negY x₂ y₂) * (x₁ - W'.addX x₁ x₂ (W'.slope x₁ x₂ y₁ y₂))) * hx.unit⁻¹ := by
  linear_combination (norm := (simp_rw [slope_of_X_ne hx, addY, negAddY, addX, negY]; ring1))
    (y₁ - W'.negY (W'.addX x₁ x₂ <| W'.slope x₁ x₂ y₁ y₂) y₁) * hx.mul_val_inv

/-! ## Maps and base changes -/

variable (f : R →+* S) (x y x₁ y₁ x₂ y₂ ℓ : R)

lemma map_negPolynomial :
    (W'.map f).toAffine.negPolynomial = W'.negPolynomial.map (mapRingHom f) := by
  simp_rw [negPolynomial]
  map_simp

lemma map_negY : (W'.map f).toAffine.negY (f x) (f y) = f (W'.negY x y) := by
  simp_rw [negY]
  map_simp

lemma map_linePolynomial : linePolynomial (f x) (f y) (f ℓ) = (linePolynomial x y ℓ).map f := by
  simp_rw [linePolynomial]
  map_simp

lemma map_addPolynomial :
    (W'.map f).toAffine.addPolynomial (f x) (f y) (f ℓ) = (W'.addPolynomial x y ℓ).map f := by
  simp_rw [addPolynomial, map_polynomial, eval_map, linePolynomial, ← coe_mapRingHom, ← eval₂_hom]
  map_simp

lemma map_addX : (W'.map f).toAffine.addX (f x₁) (f x₂) (f ℓ) = f (W'.addX x₁ x₂ ℓ) := by
  simp_rw [addX]
  map_simp

lemma map_negAddY :
    (W'.map f).toAffine.negAddY (f x₁) (f x₂) (f y₁) (f ℓ) = f (W'.negAddY x₁ x₂ y₁ ℓ) := by
  simp_rw [negAddY, map_addX]
  map_simp

lemma map_addY :
    (W'.map f).toAffine.addY (f x₁) (f x₂) (f y₁) (f ℓ) = f (W'.toAffine.addY x₁ x₂ y₁ ℓ) := by
  simp_rw [addY, map_negAddY, map_addX, map_negY]

lemma map_slope [IsLocalHom f] :
    (W'.map f).toAffine.slope (f x₁) (f x₂) (f y₁) (f y₂) = f (W'.slope x₁ x₂ y₁ y₂) := by
  have isUnit_f {x y : R} : IsUnit (f x - f y) ↔ IsUnit (x - y) := map_sub f .. ▸ isUnit_map_iff ..
  by_cases hx : IsUnit <| x₁ - x₂
  · simp_rw [slope_of_X_ne <| isUnit_f.mpr hx, ← map_sub, hx.unit_inv_map, slope_of_X_ne hx]
    map_simp
  · rw [slope, dif_neg <| hx ∘ isUnit_f.mp, map_negY, slope, dif_neg hx]
    by_cases hy : IsUnit <| y₁ - W'.negY x₂ y₂
    · simp_rw [dif_pos <| isUnit_f.mpr hy, dif_pos hy, ← map_sub, hy.unit_inv_map]
      map_simp
    · rw [dif_neg <| hy ∘ isUnit_f.mp, dif_neg hy, map_zero]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A →ₐ[S] B) (x y x₁ y₁ x₂ y₂ ℓ : A)

lemma baseChange_negPolynomial : (W'.baseChange B).toAffine.negPolynomial =
    (W'.baseChange A).toAffine.negPolynomial.map (mapRingHom f) := by
  rw [← map_negPolynomial, map_baseChange]

lemma baseChange_negY :
    (W'.baseChange B).toAffine.negY (f x) (f y) = f ((W'.baseChange A).toAffine.negY x y) := by
  rw [← RingHom.coe_coe, ← map_negY, map_baseChange]

lemma baseChange_addPolynomial : (W'.baseChange B).toAffine.addPolynomial (f x) (f y) (f ℓ) =
    ((W'.baseChange A).toAffine.addPolynomial x y ℓ).map f := by
  rw [← RingHom.coe_coe, ← map_addPolynomial, map_baseChange]

lemma baseChange_addX : (W'.baseChange B).toAffine.addX (f x₁) (f x₂) (f ℓ) =
    f ((W'.baseChange A).toAffine.addX x₁ x₂ ℓ) := by
  rw [← RingHom.coe_coe, ← map_addX, map_baseChange]

lemma baseChange_negAddY : (W'.baseChange B).toAffine.negAddY (f x₁) (f x₂) (f y₁) (f ℓ) =
    f ((W'.baseChange A).toAffine.negAddY x₁ x₂ y₁ ℓ) := by
  rw [← RingHom.coe_coe, ← map_negAddY, map_baseChange]

lemma baseChange_addY : (W'.baseChange B).toAffine.addY (f x₁) (f x₂) (f y₁) (f ℓ) =
    f ((W'.baseChange A).toAffine.addY x₁ x₂ y₁ ℓ) := by
  rw [← RingHom.coe_coe, ← map_addY, map_baseChange]

lemma baseChange_slope [hf : IsLocalHom f] :
    (W'.baseChange B).toAffine.slope (f x₁) (f x₂) (f y₁) (f y₂) =
      f ((W'.baseChange A).toAffine.slope x₁ x₂ y₁ y₂) := by
  have : IsLocalHom (f : A →+* B) := ⟨hf.map_nonunit⟩
  rw [← RingHom.coe_coe, ← map_slope, map_baseChange]

end Affine

end WeierstrassCurve
