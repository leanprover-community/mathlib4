/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# Affine coordinates for Weierstrass curves

This file defines the type of points on a Weierstrass curve as an inductive, consisting of the point
at infinity and affine points satisfying a Weierstrass equation with a nonsingular condition. This
file also defines the negation and addition operations of the group law for this type, and proves
that they respect the Weierstrass equation and the nonsingular condition. The fact that they form an
abelian group is proven in `Mathlib.AlgebraicGeometry.EllipticCurve.Group`.

## Mathematical background

Let `W` be a Weierstrass curve over a field `F`. A rational point on `W` is simply a point
$[X:Y:Z]$ defined over `F` in the projective plane satisfying the homogeneous cubic equation
$Y^2Z + a_1XYZ + a_3YZ^2 = X^3 + a_2X^2Z + a_4XZ^2 + a_6Z^3$. Any such point either lies in the
affine chart $Z \ne 0$ and satisfies the Weierstrass equation obtained by replacing $X/Z$ with $X$
and $Y/Z$ with $Y$, or is the unique point at infinity $0 := [0:1:0]$ when $Z = 0$. With this new
description, a nonsingular rational point on `W` is either $0$ or an affine point $(x, y)$ where
the partial derivatives $W_X(X, Y)$ and $W_Y(X, Y)$ do not vanish simultaneously. For a field
extension `K` of `F`, a `K`-rational point is simply a rational point on `W` base changed to `K`.

The set of nonsingular rational points forms an abelian group under a secant-and-tangent process.
 * The identity rational point is `0`.
 * Given a nonsingular rational point `P`, its negation `-P` is defined to be the unique third
    point of intersection between `W` and the line through `0` and `P`.
    Explicitly, if `P` is $(x, y)$, then `-P` is $(x, -y - a_1x - a_3)$.
 * Given two points `P` and `Q`, their addition `P + Q` is defined to be the negation of the unique
    third point of intersection between `W` and the line `L` through `P` and `Q`.
    Explicitly, let `P` be $(x_1, y_1)$ and let `Q` be $(x_2, y_2)$.
      * If $x_1 = x_2$ and $y_1 = -y_2 - a_1x_2 - a_3$, then `L` is vertical and `P + Q` is `0`.
      * If $x_1 = x_2$ and $y_1 \ne -y_2 - a_1x_2 - a_3$, then `L` is the tangent of `W` at `P = Q`,
        and has slope $\ell := (3x_1^2 + 2a_2x_1 + a_4 - a_1y_1) / (2y_1 + a_1x_1 + a_3)$.
      * Otherwise $x_1 \ne x_2$, then `L` is the secant of `W` through `P` and `Q`, and has slope
        $\ell := (y_1 - y_2) / (x_1 - x_2)$.

    In the latter two cases, the $X$-coordinate of `P + Q` is then the unique third solution of the
    equation obtained by substituting the line $Y = \ell(X - x_1) + y_1$ into the Weierstrass
    equation, and can be written down explicitly as $x := \ell^2 + a_1\ell - a_2 - x_1 - x_2$ by
    inspecting the $X^2$ terms. The $Y$-coordinate of `P + Q`, after applying the final negation
    that maps $Y$ to $-Y - a_1X - a_3$, is precisely $y := -(\ell(x - x_1) + y_1) - a_1x - a_3$.

The group law on this set is then uniquely determined by these constructions.

## Main definitions

 * `WeierstrassCurve.Affine.Equation`: the Weierstrass equation of an affine Weierstrass curve.
 * `WeierstrassCurve.Affine.Nonsingular`: the nonsingular condition on an affine Weierstrass curve.
 * `WeierstrassCurve.Affine.Point`: a nonsingular rational point on an affine Weierstrass curve.
 * `WeierstrassCurve.Affine.Point.neg`: the negation operation on an affine Weierstrass curve.
 * `WeierstrassCurve.Affine.Point.add`: the addition operation on an affine Weierstrass curve.

## Main statements

 * `WeierstrassCurve.Affine.equation_neg`: negation preserves the Weierstrass equation.
 * `WeierstrassCurve.Affine.equation_add`: addition preserves the Weierstrass equation.
 * `WeierstrassCurve.Affine.nonsingular_neg`: negation preserves the nonsingular condition.
 * `WeierstrassCurve.Affine.nonsingular_add`: addition preserves the nonsingular condition.
 * `WeierstrassCurve.Affine.nonsingular_of_Δ_ne_zero`: an affine Weierstrass curve is nonsingular at
    every point if its discriminant is non-zero.
 * `EllipticCurve.Affine.nonsingular`: an affine elliptic curve is nonsingular at every point.

## Notations

 * `W⟮K⟯`: the group of nonsingular rational points on `W` base changed to `K`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, affine coordinates
-/

open Polynomial

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

local macro "derivative_simp" : tactic =>
  `(tactic| simp only [derivative_C, derivative_X, derivative_X_pow, derivative_neg, derivative_add,
    derivative_sub, derivative_mul, derivative_sq])

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow, evalEval])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀,
    Polynomial.map_ofNat, map_C, map_X, Polynomial.map_neg, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_div, coe_mapRingHom,
    WeierstrassCurve.map])

universe r s u v w

/-! ## Weierstrass curves -/

/-- An abbreviation for a Weierstrass curve in affine coordinates. -/
abbrev WeierstrassCurve.Affine (R : Type u) : Type u :=
  WeierstrassCurve R

/-- The coercion to a Weierstrass curve in affine coordinates. -/
abbrev WeierstrassCurve.toAffine {R : Type u} (W : WeierstrassCurve R) : Affine R :=
  W

namespace WeierstrassCurve.Affine

variable {R : Type u} [CommRing R] (W : Affine R)

section Equation

/-! ### Weierstrass equations -/

/-- The polynomial $W(X, Y) := Y^2 + a_1XY + a_3Y - (X^3 + a_2X^2 + a_4X + a_6)$ associated to a
Weierstrass curve `W` over `R`. For ease of polynomial manipulation, this is represented as a term
of type `R[X][X]`, where the inner variable represents $X$ and the outer variable represents $Y$.
For clarity, the alternative notations `Y` and `R[X][Y]` are provided in the `Polynomial`
scope to represent the outer variable and the bivariate polynomial ring `R[X][X]` respectively. -/
noncomputable def polynomial : R[X][Y] :=
  Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y - C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)

lemma polynomial_eq : W.polynomial =
    Cubic.toPoly
      ⟨0, 1, Cubic.toPoly ⟨0, 0, W.a₁, W.a₃⟩, Cubic.toPoly ⟨-1, -W.a₂, -W.a₄, -W.a₆⟩⟩ := by
  simp only [polynomial, Cubic.toPoly]
  C_simp
  ring1

lemma polynomial_ne_zero [Nontrivial R] : W.polynomial ≠ 0 := by
  rw [polynomial_eq]
  exact Cubic.ne_zero_of_b_ne_zero one_ne_zero

@[simp]
lemma degree_polynomial [Nontrivial R] : W.polynomial.degree = 2 := by
  rw [polynomial_eq]
  exact Cubic.degree_of_b_ne_zero' one_ne_zero

@[simp]
lemma natDegree_polynomial [Nontrivial R] : W.polynomial.natDegree = 2 := by
  rw [polynomial_eq]
  exact Cubic.natDegree_of_b_ne_zero' one_ne_zero

lemma monic_polynomial : W.polynomial.Monic := by
  nontriviality R
  simpa only [polynomial_eq] using Cubic.monic_of_b_eq_one'

lemma irreducible_polynomial [IsDomain R] : Irreducible W.polynomial := by
  by_contra h
  rcases (W.monic_polynomial.not_irreducible_iff_exists_add_mul_eq_coeff W.natDegree_polynomial).mp
    h with ⟨f, g, h0, h1⟩
  simp only [polynomial_eq, Cubic.coeff_eq_c, Cubic.coeff_eq_d] at h0 h1
  apply_fun degree at h0 h1
  rw [Cubic.degree_of_a_ne_zero' <| neg_ne_zero.mpr <| one_ne_zero' R, degree_mul] at h0
  apply (h1.symm.le.trans Cubic.degree_of_b_eq_zero').not_lt
  rcases Nat.WithBot.add_eq_three_iff.mp h0.symm with h | h | h | h
  -- Porting note: replaced two `any_goals` proofs with two `iterate 2` proofs
  iterate 2 rw [degree_add_eq_right_of_degree_lt] <;> simp only [h] <;> decide
  iterate 2 rw [degree_add_eq_left_of_degree_lt] <;> simp only [h] <;> decide

lemma evalEval_polynomial (x y : R) : W.polynomial.evalEval x y =
    y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
  simp only [polynomial]
  eval_simp
  rw [add_mul, ← add_assoc]

@[simp]
lemma evalEval_polynomial_zero : W.polynomial.evalEval 0 0 = -W.a₆ := by
  simp only [evalEval_polynomial, zero_add, zero_sub, mul_zero, zero_pow <| Nat.succ_ne_zero _]

/-- The proposition that an affine point $(x, y)$ lies in `W`. In other words, $W(x, y) = 0$. -/
def Equation (x y : R) : Prop :=
  W.polynomial.evalEval x y = 0

lemma equation_iff' (x y : R) : W.Equation x y ↔
    y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
  rw [Equation, evalEval_polynomial]

lemma equation_iff (x y : R) :
    W.Equation x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  rw [equation_iff', sub_eq_zero]

@[simp]
lemma equation_zero : W.Equation 0 0 ↔ W.a₆ = 0 := by
  rw [Equation, evalEval_polynomial_zero, neg_eq_zero]

lemma equation_iff_variableChange (x y : R) :
    W.Equation x y ↔ (W.variableChange ⟨1, x, 0, y⟩).toAffine.Equation 0 0 := by
  rw [equation_iff', ← neg_eq_zero, equation_zero, variableChange_a₆, inv_one, Units.val_one]
  congr! 1
  ring1

end Equation

section Nonsingular

/-! ### Nonsingular Weierstrass equations -/

/-- The partial derivative $W_X(X, Y)$ of $W(X, Y)$ with respect to $X$.

TODO: define this in terms of `Polynomial.derivative`. -/
noncomputable def polynomialX : R[X][Y] :=
  C (C W.a₁) * Y - C (C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄)

lemma evalEval_polynomialX (x y : R) :
    W.polynomialX.evalEval x y = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) := by
  simp only [polynomialX]
  eval_simp

@[simp]
lemma evalEval_polynomialX_zero : W.polynomialX.evalEval 0 0 = -W.a₄ := by
  simp only [evalEval_polynomialX, zero_add, zero_sub, mul_zero, zero_pow <| Nat.succ_ne_zero _]

/-- The partial derivative $W_Y(X, Y)$ of $W(X, Y)$ with respect to $Y$.

TODO: define this in terms of `Polynomial.derivative`. -/
noncomputable def polynomialY : R[X][Y] :=
  C (C 2) * Y + C (C W.a₁ * X + C W.a₃)

lemma evalEval_polynomialY (x y : R) :
    W.polynomialY.evalEval x y = 2 * y + W.a₁ * x + W.a₃ := by
  simp only [polynomialY]
  eval_simp
  rw [← add_assoc]

@[simp]
lemma evalEval_polynomialY_zero : W.polynomialY.evalEval 0 0 = W.a₃ := by
  simp only [evalEval_polynomialY, zero_add, mul_zero]

@[deprecated (since := "2024-06-19")] alias eval_polynomial := evalEval_polynomial
@[deprecated (since := "2024-06-19")] alias eval_polynomial_zero := evalEval_polynomial_zero
@[deprecated (since := "2024-06-19")] alias eval_polynomialX := evalEval_polynomialX
@[deprecated (since := "2024-06-19")] alias eval_polynomialX_zero := evalEval_polynomialX_zero
@[deprecated (since := "2024-06-19")] alias eval_polynomialY := evalEval_polynomialY
@[deprecated (since := "2024-06-19")] alias eval_polynomialY_zero := evalEval_polynomialY_zero

/-- The proposition that an affine point $(x, y)$ in `W` is nonsingular.
In other words, either $W_X(x, y) \ne 0$ or $W_Y(x, y) \ne 0$.

Note that this definition is only mathematically accurate for fields.
TODO: generalise this definition to be mathematically accurate for a larger class of rings. -/
def Nonsingular (x y : R) : Prop :=
  W.Equation x y ∧ (W.polynomialX.evalEval x y ≠ 0 ∨ W.polynomialY.evalEval x y ≠ 0)

lemma nonsingular_iff' (x y : R) : W.Nonsingular x y ↔ W.Equation x y ∧
    (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 ∨ 2 * y + W.a₁ * x + W.a₃ ≠ 0) := by
  rw [Nonsingular, equation_iff', evalEval_polynomialX, evalEval_polynomialY]

lemma nonsingular_iff (x y : R) : W.Nonsingular x y ↔
    W.Equation x y ∧ (W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∨ y ≠ -y - W.a₁ * x - W.a₃) := by
  rw [nonsingular_iff', sub_ne_zero, ← sub_ne_zero (a := y)]
  congr! 3
  ring1

@[simp]
lemma nonsingular_zero : W.Nonsingular 0 0 ↔ W.a₆ = 0 ∧ (W.a₃ ≠ 0 ∨ W.a₄ ≠ 0) := by
  rw [Nonsingular, equation_zero, evalEval_polynomialX_zero, neg_ne_zero, evalEval_polynomialY_zero,
    or_comm]

lemma nonsingular_iff_variableChange (x y : R) :
    W.Nonsingular x y ↔ (W.variableChange ⟨1, x, 0, y⟩).toAffine.Nonsingular 0 0 := by
  rw [nonsingular_iff', equation_iff_variableChange, equation_zero, ← neg_ne_zero, or_comm,
    nonsingular_zero, variableChange_a₃, variableChange_a₄, inv_one, Units.val_one]
  simp only [variableChange]
  congr! 3 <;> ring1

lemma nonsingular_zero_of_Δ_ne_zero (h : W.Equation 0 0) (hΔ : W.Δ ≠ 0) : W.Nonsingular 0 0 := by
  simp only [equation_zero, nonsingular_zero] at *
  contrapose! hΔ
  simp only [b₂, b₄, b₆, b₈, Δ, h, hΔ]
  ring1

/-- A Weierstrass curve is nonsingular at every point if its discriminant is non-zero. -/
lemma nonsingular_of_Δ_ne_zero {x y : R} (h : W.Equation x y) (hΔ : W.Δ ≠ 0) : W.Nonsingular x y :=
  (W.nonsingular_iff_variableChange x y).mpr <|
    nonsingular_zero_of_Δ_ne_zero _ ((W.equation_iff_variableChange x y).mp h) <| by
      rwa [variableChange_Δ, inv_one, Units.val_one, one_pow, one_mul]

end Nonsingular

section Ring

/-! ### Group operation polynomials over a ring -/

/-- The polynomial $-Y - a_1X - a_3$ associated to negation. -/
noncomputable def negPolynomial : R[X][Y] :=
  -(Y : R[X][Y]) - C (C W.a₁ * X + C W.a₃)

lemma Y_sub_polynomialY : Y - W.polynomialY = W.negPolynomial := by
  rw [polynomialY, negPolynomial]; C_simp; ring

lemma Y_sub_negPolynomial : Y - W.negPolynomial = W.polynomialY := by
  rw [← Y_sub_polynomialY, sub_sub_cancel]

/-- The $Y$-coordinate of the negation of an affine point in `W`.

This depends on `W`, and has argument order: $x$, $y$. -/
@[simp]
def negY (x y : R) : R :=
  -y - W.a₁ * x - W.a₃

lemma negY_negY (x y : R) : W.negY x (W.negY x y) = y := by
  simp only [negY]
  ring1

lemma eval_negPolynomial (x y : R) : W.negPolynomial.evalEval x y = W.negY x y := by
  rw [negY, sub_sub, negPolynomial]
  eval_simp

/-- The polynomial $L(X - x) + y$ associated to the line $Y = L(X - x) + y$,
with a slope of $L$ that passes through an affine point $(x, y)$.

This does not depend on `W`, and has argument order: $x$, $y$, $L$. -/
noncomputable def linePolynomial (x y L : R) : R[X] :=
  C L * (X - C x) + C y

/-- The polynomial obtained by substituting the line $Y = L*(X - x) + y$, with a slope of $L$
that passes through an affine point $(x, y)$, into the polynomial $W(X, Y)$ associated to `W`.
If such a line intersects `W` at another point $(x', y')$, then the roots of this polynomial are
precisely $x$, $x'$, and the $X$-coordinate of the addition of $(x, y)$ and $(x', y')$.

This depends on `W`, and has argument order: $x$, $y$, $L$. -/
noncomputable def addPolynomial (x y L : R) : R[X] :=
  W.polynomial.eval <| linePolynomial x y L

lemma C_addPolynomial (x y L : R) : C (W.addPolynomial x y L) =
    (Y - C (linePolynomial x y L)) * (W.negPolynomial - C (linePolynomial x y L)) +
      W.polynomial := by
  rw [addPolynomial, linePolynomial, polynomial, negPolynomial]
  eval_simp
  C_simp
  ring1

lemma addPolynomial_eq (x y L : R) : W.addPolynomial x y L = -Cubic.toPoly
    ⟨1, -L ^ 2 - W.a₁ * L + W.a₂,
      2 * x * L ^ 2 + (W.a₁ * x - 2 * y - W.a₃) * L + (-W.a₁ * y + W.a₄),
      -x ^ 2 * L ^ 2 + (2 * x * y + W.a₃ * x) * L - (y ^ 2 + W.a₃ * y - W.a₆)⟩ := by
  rw [addPolynomial, linePolynomial, polynomial, Cubic.toPoly]
  eval_simp
  C_simp
  ring1

/-- The $X$-coordinate of the addition of two affine points $(x_1, y_1)$ and $(x_2, y_2)$ in `W`,
where the line through them is not vertical and has a slope of $L$.

This depends on `W`, and has argument order: $x_1$, $x_2$, $L$. -/
@[simp]
def addX (x₁ x₂ L : R) : R :=
  L ^ 2 + W.a₁ * L - W.a₂ - x₁ - x₂

/-- The $Y$-coordinate of the negated addition of two affine points $(x_1, y_1)$ and $(x_2, y_2)$,
where the line through them is not vertical and has a slope of $L$.

This depends on `W`, and has argument order: $x_1$, $x_2$, $y_1$, $L$. -/
@[simp]
def negAddY (x₁ x₂ y₁ L : R) : R :=
  L * (W.addX x₁ x₂ L - x₁) + y₁

/-- The $Y$-coordinate of the addition of two affine points $(x_1, y_1)$ and $(x_2, y_2)$ in `W`,
where the line through them is not vertical and has a slope of $L$.

This depends on `W`, and has argument order: $x_1$, $x_2$, $y_1$, $L$. -/
@[simp]
def addY (x₁ x₂ y₁ L : R) : R :=
  W.negY (W.addX x₁ x₂ L) (W.negAddY x₁ x₂ y₁ L)

lemma equation_neg_iff (x y : R) : W.Equation x (W.negY x y) ↔ W.Equation x y := by
  rw [equation_iff, equation_iff, negY]
  congr! 1
  ring1

lemma nonsingular_neg_iff (x y : R) : W.Nonsingular x (W.negY x y) ↔ W.Nonsingular x y := by
  rw [nonsingular_iff, equation_neg_iff, ← negY, negY_negY, ← @ne_comm _ y, nonsingular_iff]
  exact and_congr_right' <| (iff_congr not_and_or.symm not_and_or.symm).mpr <|
    not_congr <| and_congr_left fun h => by rw [← h]

lemma equation_add_iff (x₁ x₂ y₁ L : R) :
    W.Equation (W.addX x₁ x₂ L) (W.negAddY x₁ x₂ y₁ L) ↔
      (W.addPolynomial x₁ y₁ L).eval (W.addX x₁ x₂ L) = 0 := by
  rw [Equation, negAddY, addPolynomial, linePolynomial, polynomial]
  eval_simp

variable {W}

lemma equation_neg_of {x y : R} (h : W.Equation x <| W.negY x y) : W.Equation x y :=
  (W.equation_neg_iff ..).mp h

/-- The negation of an affine point in `W` lies in `W`. -/
lemma equation_neg {x y : R} (h : W.Equation x y) : W.Equation x <| W.negY x y :=
  (W.equation_neg_iff ..).mpr h

lemma nonsingular_neg_of {x y : R} (h : W.Nonsingular x <| W.negY x y) : W.Nonsingular x y :=
  (W.nonsingular_neg_iff ..).mp h

/-- The negation of a nonsingular affine point in `W` is nonsingular. -/
lemma nonsingular_neg {x y : R} (h : W.Nonsingular x y) : W.Nonsingular x <| W.negY x y :=
  (W.nonsingular_neg_iff ..).mpr h

lemma nonsingular_negAdd_of_eval_derivative_ne_zero {x₁ x₂ y₁ L : R}
    (hx' : W.Equation (W.addX x₁ x₂ L) (W.negAddY x₁ x₂ y₁ L))
    (hx : (W.addPolynomial x₁ y₁ L).derivative.eval (W.addX x₁ x₂ L) ≠ 0) :
    W.Nonsingular (W.addX x₁ x₂ L) (W.negAddY x₁ x₂ y₁ L) := by
  rw [Nonsingular, and_iff_right hx', negAddY, polynomialX, polynomialY]
  eval_simp
  contrapose! hx
  rw [addPolynomial, linePolynomial, polynomial]
  eval_simp
  derivative_simp
  simp only [zero_add, add_zero, sub_zero, zero_mul, mul_one]
  eval_simp
  linear_combination (norm := (norm_num1; ring1)) hx.left + L * hx.right

end Ring

section Field

/-! ### Group operation polynomials over a field -/

open Classical in
/-- The slope of the line through two affine points $(x_1, y_1)$ and $(x_2, y_2)$ in `W`.
If $x_1 \ne x_2$, then this line is the secant of `W` through $(x_1, y_1)$ and $(x_2, y_2)$,
and has slope $(y_1 - y_2) / (x_1 - x_2)$. Otherwise, if $y_1 \ne -y_1 - a_1x_1 - a_3$,
then this line is the tangent of `W` at $(x_1, y_1) = (x_2, y_2)$, and has slope
$(3x_1^2 + 2a_2x_1 + a_4 - a_1y_1) / (2y_1 + a_1x_1 + a_3)$. Otherwise, this line is vertical,
and has undefined slope, in which case this function returns the value 0.

This depends on `W`, and has argument order: $x_1$, $x_2$, $y_1$, $y_2$. -/
noncomputable def slope {F : Type u} [Field F] (W : Affine F) (x₁ x₂ y₁ y₂ : F) : F :=
  if x₁ = x₂ then if y₁ = W.negY x₂ y₂ then 0
    else (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.negY x₁ y₁)
  else (y₁ - y₂) / (x₁ - x₂)

variable {F : Type u} [Field F] {W : Affine F}

@[simp]
lemma slope_of_Y_eq {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂) :
    W.slope x₁ x₂ y₁ y₂ = 0 := by
  rw [slope, if_pos hx, if_pos hy]

@[simp]
lemma slope_of_Y_ne {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) :
    W.slope x₁ x₂ y₁ y₂ =
      (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.negY x₁ y₁) := by
  rw [slope, if_pos hx, if_neg hy]

@[simp]
lemma slope_of_X_ne {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
    W.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) := by
  rw [slope, if_neg hx]

lemma slope_of_Y_ne_eq_eval {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) :
    W.slope x₁ x₂ y₁ y₂ = -W.polynomialX.evalEval x₁ y₁ / W.polynomialY.evalEval x₁ y₁ := by
  rw [slope_of_Y_ne hx hy, evalEval_polynomialX, neg_sub]
  congr 1
  rw [negY, evalEval_polynomialY]
  ring1

lemma Y_eq_of_X_eq {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hx : x₁ = x₂) : y₁ = y₂ ∨ y₁ = W.negY x₂ y₂ := by
  rw [equation_iff] at h₁ h₂
  rw [← sub_eq_zero, ← sub_eq_zero (a := y₁), ← mul_eq_zero, negY]
  linear_combination (norm := (rw [hx]; ring1)) h₁ - h₂

lemma Y_eq_of_Y_ne {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hx : x₁ = x₂)
    (hy : y₁ ≠ W.negY x₂ y₂) : y₁ = y₂ :=
  (Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy

lemma addPolynomial_slope {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) : W.addPolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂) =
      -((X - C x₁) * (X - C x₂) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂))) := by
  rw [addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective]
  by_cases hx : x₁ = x₂
  · rcases hx, Y_eq_of_Y_ne h₁ h₂ hx (hxy hx) with ⟨rfl, rfl⟩
    rw [equation_iff] at h₁ h₂
    rw [slope_of_Y_ne rfl <| hxy rfl]
    rw [negY, ← sub_ne_zero] at hxy
    ext
    · rfl
    · simp only [addX]
      ring1
    · field_simp [hxy rfl]
      ring1
    · linear_combination (norm := (field_simp [hxy rfl]; ring1)) -h₁
  · rw [equation_iff] at h₁ h₂
    rw [slope_of_X_ne hx]
    rw [← sub_eq_zero] at hx
    ext
    · rfl
    · simp only [addX]
      ring1
    · apply mul_right_injective₀ hx
      linear_combination (norm := (field_simp [hx]; ring1)) h₂ - h₁
    · apply mul_right_injective₀ hx
      linear_combination (norm := (field_simp [hx]; ring1)) x₂ * h₁ - x₁ * h₂

/-- The negated addition of two affine points in `W` on a sloped line lies in `W`. -/
lemma equation_negAdd {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) : W.Equation
      (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.negAddY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  rw [equation_add_iff, addPolynomial_slope h₁ h₂ hxy]
  eval_simp
  rw [neg_eq_zero, sub_self, mul_zero]

/-- The addition of two affine points in `W` on a sloped line lies in `W`. -/
lemma equation_add {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    W.Equation (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) :=
  equation_neg <| equation_negAdd h₁ h₂ hxy

lemma derivative_addPolynomial_slope {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h₂ : W.Equation x₂ y₂) (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    derivative (W.addPolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) =
      -((X - C x₁) * (X - C x₂) + (X - C x₁) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)) +
          (X - C x₂) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂))) := by
  rw [addPolynomial_slope h₁ h₂ hxy]
  derivative_simp
  ring1

/-- The negated addition of two nonsingular affine points in `W` on a sloped line is nonsingular. -/
lemma nonsingular_negAdd {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) : W.Nonsingular
      (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.negAddY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  by_cases hx₁ : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₁
  · rwa [negAddY, hx₁, sub_self, mul_zero, zero_add]
  · by_cases hx₂ : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₂
    · by_cases hx : x₁ = x₂
      · subst hx
        contradiction
      · rwa [negAddY, ← neg_sub, mul_neg, hx₂, slope_of_X_ne hx,
          div_mul_cancel₀ _ <| sub_ne_zero_of_ne hx, neg_sub, sub_add_cancel]
    · apply nonsingular_negAdd_of_eval_derivative_ne_zero <| equation_negAdd h₁.1 h₂.1 hxy
      rw [derivative_addPolynomial_slope h₁.left h₂.left hxy]
      eval_simp
      simpa only [neg_ne_zero, sub_self, mul_zero, add_zero] using
        mul_ne_zero (sub_ne_zero_of_ne hx₁) (sub_ne_zero_of_ne hx₂)

/-- The addition of two nonsingular affine points in `W` on a sloped line is nonsingular. -/
lemma nonsingular_add {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    W.Nonsingular (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) :=
  nonsingular_neg <| nonsingular_negAdd h₁ h₂ hxy

variable {x₁ x₂ : F} (y₁ y₂ : F)

/-- The formula x(P₁ + P₂) = x(P₁ - P₂) - ψ(P₁)ψ(P₂) / (x(P₂) - x(P₁))²,
where ψ(x,y) = 2y + a₁x + a₃. -/
lemma addX_eq_addX_negY_sub (hx : x₁ ≠ x₂) :
    W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂))
      - (y₁ - W.negY x₁ y₁) * (y₂ - W.negY x₂ y₂) / (x₂ - x₁) ^ 2 := by
  simp_rw [slope_of_X_ne hx, addX, negY, ← neg_sub x₁, neg_sq]
  field_simp [sub_ne_zero.mpr hx]
  ring1

/-- The formula y(P₁)(x(P₂) - x(P₃)) + y(P₂)(x(P₃) - x(P₁)) + y(P₃)(x(P₁) - x(P₂)) = 0,
assuming that P₁ + P₂ + P₃ = O. -/
lemma cyclic_sum_Y_mul_X_sub_X (hx : x₁ ≠ x₂) :
    letI x₃ := W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
    y₁ * (x₂ - x₃) + y₂ * (x₃ - x₁) + W.negAddY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) = 0 := by
  simp_rw [slope_of_X_ne hx, negAddY, addX]
  field_simp [sub_ne_zero.mpr hx]
  ring1

/-- The formula
ψ(P₁ + P₂) = (ψ(P₂)(x(P₁) - x(P₃)) - ψ(P₁)(x(P₂) - x(P₃))) / (x(P₂) - x(P₁)),
where ψ(x,y) = 2y + a₁x + a₃. -/
lemma addY_sub_negY_addY (hx : x₁ ≠ x₂) :
    letI x₃ := W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
    letI y₃ := W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)
    y₃ - W.negY x₃ y₃ =
      ((y₂ - W.negY x₂ y₂) * (x₁ - x₃) - (y₁ - W.negY x₁ y₁) * (x₂ - x₃)) / (x₂ - x₁) := by
  simp_rw [addY, negY, eq_div_iff (sub_ne_zero.mpr hx.symm)]
  linear_combination 2 * cyclic_sum_Y_mul_X_sub_X y₁ y₂ hx

end Field

section Group

/-! ### Group operations -/

/-- A nonsingular rational point on a Weierstrass curve `W` in affine coordinates. This is either
the unique point at infinity `WeierstrassCurve.Affine.Point.zero` or the nonsingular affine points
`WeierstrassCurve.Affine.Point.some` $(x, y)$ satisfying the Weierstrass equation of `W`. -/
inductive Point
  | zero
  | some {x y : R} (h : W.Nonsingular x y)

/-- For an algebraic extension `S` of `R`, the type of nonsingular `S`-rational points on `W`. -/
scoped notation3:max W "⟮" S "⟯" => Affine.Point <| baseChange W S

namespace Point

variable {W}

instance : Inhabited W.Point :=
  ⟨zero⟩

instance : Zero W.Point :=
  ⟨zero⟩

lemma zero_def : (zero : W.Point) = 0 :=
  rfl

lemma some_ne_zero {x y : R} (h : W.Nonsingular x y) : some h ≠ 0 := by rintro (_|_)

/-- The negation of a nonsingular rational point on `W`.

Given a nonsingular rational point `P` on `W`, use `-P` instead of `neg P`. -/
def neg : W.Point → W.Point
  | 0 => 0
  | some h => some <| nonsingular_neg h

instance : Neg W.Point :=
  ⟨neg⟩

lemma neg_def (P : W.Point) : P.neg = -P :=
  rfl

@[simp]
lemma neg_zero : (-0 : W.Point) = 0 :=
  rfl

@[simp]
lemma neg_some {x y : R} (h : W.Nonsingular x y) : -some h = some (nonsingular_neg h) :=
  rfl

instance : InvolutiveNeg W.Point :=
  ⟨by rintro (_ | _) <;> simp [zero_def]; ring1⟩

variable {F : Type u} [Field F] {W : Affine F}

open Classical in
/-- The addition of two nonsingular rational points on `W`.

Given two nonsingular rational points `P` and `Q` on `W`, use `P + Q` instead of `add P Q`. -/
noncomputable def add : W.Point → W.Point → W.Point
  | 0, P => P
  | P, 0 => P
  | @some _ _ _ x₁ y₁ h₁, @some _ _ _ x₂ y₂ h₂ =>
    if h : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂ then 0
    else some (nonsingular_add h₁ h₂ fun hx hy ↦ h ⟨hx, hy⟩)

noncomputable instance instAddPoint : Add W.Point :=
  ⟨add⟩

lemma add_def (P Q : W.Point) : P.add Q = P + Q :=
  rfl

noncomputable instance instAddZeroClassPoint : AddZeroClass W.Point :=
  ⟨by rintro (_ | _) <;> rfl, by rintro (_ | _) <;> rfl⟩

@[simp]
lemma add_of_Y_eq {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂) : some h₁ + some h₂ = 0 := by
  simp_rw [← add_def, add]; exact dif_pos ⟨hx, hy⟩

@[simp]
lemma add_self_of_Y_eq {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ = W.negY x₁ y₁) :
    some h₁ + some h₁ = 0 :=
  add_of_Y_eq rfl hy

@[simp]
lemma add_of_imp {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) : some h₁ + some h₂ = some (nonsingular_add h₁ h₂ hxy) :=
  dif_neg fun hn ↦ hxy hn.1 hn.2

@[simp]
lemma add_of_Y_ne {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hy : y₁ ≠ W.negY x₂ y₂) :
    some h₁ + some h₂ = some (nonsingular_add h₁ h₂ fun _ ↦ hy) :=
  add_of_imp fun _ ↦ hy

lemma add_of_Y_ne' {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hy : y₁ ≠ W.negY x₂ y₂) :
    some h₁ + some h₂ = -some (nonsingular_negAdd h₁ h₂ fun _ ↦ hy) :=
  add_of_Y_ne hy

@[simp]
lemma add_self_of_Y_ne {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ ≠ W.negY x₁ y₁) :
    some h₁ + some h₁ = some (nonsingular_add h₁ h₁ fun _ => hy) :=
  add_of_Y_ne hy

lemma add_self_of_Y_ne' {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ ≠ W.negY x₁ y₁) :
    some h₁ + some h₁ = -some (nonsingular_negAdd h₁ h₁ fun _ => hy) :=
  add_of_Y_ne hy

@[simp]
lemma add_of_X_ne {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) : some h₁ + some h₂ = some (nonsingular_add h₁ h₂ fun h => (hx h).elim) :=
  add_of_imp fun h ↦ (hx h).elim

lemma add_of_X_ne' {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) : some h₁ + some h₂ = -some (nonsingular_negAdd h₁ h₂ fun h => (hx h).elim) :=
  add_of_X_ne hx

@[deprecated (since := "2024-06-03")] alias some_add_some_of_Yeq := add_of_Y_eq
@[deprecated (since := "2024-06-03")] alias some_add_self_of_Yeq := add_self_of_Y_eq
@[deprecated (since := "2024-06-03")] alias some_add_some_of_Yne := add_of_Y_ne
@[deprecated (since := "2024-06-03")] alias some_add_some_of_Yne' := add_of_Y_ne'
@[deprecated (since := "2024-06-03")] alias some_add_self_of_Yne := add_self_of_Y_ne
@[deprecated (since := "2024-06-03")] alias some_add_self_of_Yne' := add_self_of_Y_ne'
@[deprecated (since := "2024-06-03")] alias some_add_some_of_Xne := add_of_X_ne
@[deprecated (since := "2024-06-03")] alias some_add_some_of_Xne' := add_of_X_ne'

end Point

end Group

section Map

/-! ### Maps across ring homomorphisms -/

variable {S : Type v} [CommRing S] (f : R →+* S)

lemma map_polynomial : (W.map f).toAffine.polynomial = W.polynomial.map (mapRingHom f) := by
  simp only [polynomial]
  map_simp

lemma evalEval_baseChange_polynomial_X_Y :
    (W.baseChange R[X][Y]).toAffine.polynomial.evalEval (C X) Y = W.polynomial := by
  rw [baseChange, toAffine, map_polynomial, evalEval, eval_map, eval_C_X_eval₂_map_C_X]

variable {W} in
lemma Equation.map {x y : R} (h : W.Equation x y) : Equation (W.map f) (f x) (f y) := by
  rw [Equation, map_polynomial, map_mapRingHom_evalEval, ← f.map_zero]; exact congr_arg f h

variable {f} in
lemma map_equation (hf : Function.Injective f) (x y : R) :
    (W.map f).toAffine.Equation (f x) (f y) ↔ W.Equation x y := by
  simp only [Equation, map_polynomial, map_mapRingHom_evalEval, map_eq_zero_iff f hf]

lemma map_polynomialX : (W.map f).toAffine.polynomialX = W.polynomialX.map (mapRingHom f) := by
  simp only [polynomialX]
  map_simp

lemma map_polynomialY : (W.map f).toAffine.polynomialY = W.polynomialY.map (mapRingHom f) := by
  simp only [polynomialY]
  map_simp

variable {f} in
lemma map_nonsingular (hf : Function.Injective f) (x y : R) :
    (W.map f).toAffine.Nonsingular (f x) (f y) ↔ W.Nonsingular x y := by
  simp only [Nonsingular, evalEval, W.map_equation hf, map_polynomialX,
    map_polynomialY, map_mapRingHom_evalEval, map_ne_zero_iff f hf]

lemma map_negPolynomial :
    (W.map f).toAffine.negPolynomial = W.negPolynomial.map (mapRingHom f) := by
  simp only [negPolynomial]
  map_simp

lemma map_negY (x y : R) : (W.map f).toAffine.negY (f x) (f y) = f (W.negY x y) := by
  simp only [negY]
  map_simp

lemma map_linePolynomial (x y L : R) :
    linePolynomial (f x) (f y) (f L) = (linePolynomial x y L).map f := by
  simp only [linePolynomial]
  map_simp

lemma map_addPolynomial (x y L : R) :
    (W.map f).toAffine.addPolynomial (f x) (f y) (f L) = (W.addPolynomial x y L).map f := by
  rw [addPolynomial, map_polynomial, eval_map, linePolynomial, addPolynomial, ← coe_mapRingHom,
    ← eval₂_hom, linePolynomial]
  map_simp

lemma map_addX (x₁ x₂ L : R) :
    (W.map f).toAffine.addX (f x₁) (f x₂) (f L) = f (W.addX x₁ x₂ L) := by
  simp only [addX]
  map_simp

lemma map_negAddY (x₁ x₂ y₁ L : R) :
    (W.map f).toAffine.negAddY (f x₁) (f x₂) (f y₁) (f L) = f (W.negAddY x₁ x₂ y₁ L) := by
  simp only [negAddY, map_addX]
  map_simp

lemma map_addY (x₁ x₂ y₁ L : R) :
    (W.map f).toAffine.addY (f x₁) (f x₂) (f y₁) (f L) = f (W.toAffine.addY x₁ x₂ y₁ L) := by
  simp only [addY, map_negAddY, map_addX, map_negY]

lemma map_slope {F : Type u} [Field F] (W : Affine F) {K : Type v} [Field K] (f : F →+* K)
    (x₁ x₂ y₁ y₂ : F) : (W.map f).toAffine.slope (f x₁) (f x₂) (f y₁) (f y₂) =
      f (W.slope x₁ x₂ y₁ y₂) := by
  by_cases hx : x₁ = x₂
  · by_cases hy : y₁ = W.negY x₂ y₂
    · rw [slope_of_Y_eq (congr_arg f hx) <| by rw [hy, map_negY], slope_of_Y_eq hx hy, map_zero]
    · rw [slope_of_Y_ne (congr_arg f hx) <| W.map_negY f x₂ y₂ ▸ fun h => hy <| f.injective h,
        map_negY, slope_of_Y_ne hx hy]
      map_simp
  · rw [slope_of_X_ne fun h => hx <| f.injective h, slope_of_X_ne hx]
    map_simp

end Map

section BaseChange

/-! ### Base changes across algebra homomorphisms -/

variable {R : Type r} [CommRing R] (W : Affine R) {S : Type s} [CommRing S] [Algebra R S]
  {A : Type u} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  {B : Type v} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[S] B)

lemma baseChange_polynomial : (W.baseChange B).toAffine.polynomial =
    (W.baseChange A).toAffine.polynomial.map (mapRingHom f) := by
  rw [← map_polynomial, map_baseChange]

lemma baseChange_equation (hf : Function.Injective f) (x y : A) :
    (W.baseChange B).toAffine.Equation (f x) (f y) ↔ (W.baseChange A).toAffine.Equation x y := by
  erw [← map_equation _ hf, map_baseChange]
  rfl

lemma baseChange_polynomialX : (W.baseChange B).toAffine.polynomialX =
    (W.baseChange A).toAffine.polynomialX.map (mapRingHom f) := by
  rw [← map_polynomialX, map_baseChange]

lemma baseChange_polynomialY : (W.baseChange B).toAffine.polynomialY =
    (W.baseChange A).toAffine.polynomialY.map (mapRingHom f) := by
  rw [← map_polynomialY, map_baseChange]

variable {f} in
lemma baseChange_nonsingular (hf : Function.Injective f) (x y : A) :
    (W.baseChange B).toAffine.Nonsingular (f x) (f y) ↔
      (W.baseChange A).toAffine.Nonsingular x y := by
  erw [← map_nonsingular _ hf, map_baseChange]
  rfl

lemma baseChange_negPolynomial :
    (W.baseChange B).toAffine.negPolynomial =
      (W.baseChange A).toAffine.negPolynomial.map (mapRingHom f) := by
  rw [← map_negPolynomial, map_baseChange]

lemma baseChange_negY (x y : A) :
    (W.baseChange B).toAffine.negY (f x) (f y) = f ((W.baseChange A).toAffine.negY x y) := by
  erw [← map_negY, map_baseChange]
  rfl

lemma baseChange_addPolynomial (x y L : A) :
    (W.baseChange B).toAffine.addPolynomial (f x) (f y) (f L) =
      ((W.baseChange A).toAffine.addPolynomial x y L).map f := by
  rw [← map_addPolynomial, map_baseChange]
  rfl

lemma baseChange_addX (x₁ x₂ L : A) :
    (W.baseChange B).toAffine.addX (f x₁) (f x₂) (f L) =
      f ((W.baseChange A).toAffine.addX x₁ x₂ L) := by
  erw [← map_addX, map_baseChange]
  rfl

lemma baseChange_negAddY (x₁ x₂ y₁ L : A) :
    (W.baseChange B).toAffine.negAddY (f x₁) (f x₂) (f y₁) (f L) =
      f ((W.baseChange A).toAffine.negAddY x₁ x₂ y₁ L) := by
  erw [← map_negAddY, map_baseChange]
  rfl

lemma baseChange_addY (x₁ x₂ y₁ L : A) :
    (W.baseChange B).toAffine.addY (f x₁) (f x₂) (f y₁) (f L) =
      f ((W.baseChange A).toAffine.addY x₁ x₂ y₁ L) := by
  erw [← map_addY, map_baseChange]
  rfl

variable {F : Type u} [Field F] [Algebra R F] [Algebra S F] [IsScalarTower R S F]
  {K : Type v} [Field K] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (f : F →ₐ[S] K)
  {L : Type w} [Field L] [Algebra R L] [Algebra S L] [IsScalarTower R S L] (g : K →ₐ[S] L)

lemma baseChange_slope (x₁ x₂ y₁ y₂ : F) :
    (W.baseChange K).toAffine.slope (f x₁) (f x₂) (f y₁) (f y₂) =
      f ((W.baseChange F).toAffine.slope x₁ x₂ y₁ y₂) := by
  erw [← map_slope, map_baseChange]
  rfl

namespace Point

/-- The function from `W⟮F⟯` to `W⟮K⟯` induced by an algebra homomorphism `f : F →ₐ[S] K`,
where `W` is defined over a subring of a ring `S`, and `F` and `K` are field extensions of `S`. -/
def mapFun : W⟮F⟯ → W⟮K⟯
  | 0 => 0
  | some h => some <| (W.baseChange_nonsingular f.injective ..).mpr h

/-- The group homomorphism from `W⟮F⟯` to `W⟮K⟯` induced by an algebra homomorphism `f : F →ₐ[S] K`,
where `W` is defined over a subring of a ring `S`, and `F` and `K` are field extensions of `S`. -/
def map : W⟮F⟯ →+ W⟮K⟯ where
  toFun := mapFun W f
  map_zero' := rfl
  map_add' := by
    rintro (_ | @⟨x₁, y₁, _⟩) (_ | @⟨x₂, y₂, _⟩)
    any_goals rfl
    have inj : Function.Injective f := f.injective
    by_cases h : x₁ = x₂ ∧ y₁ = negY (W.baseChange F) x₂ y₂
    · simp only [add_of_Y_eq h.1 h.2, mapFun]
      rw [add_of_Y_eq congr(f $(h.1))]
      rw [baseChange_negY, inj.eq_iff]
      exact h.2
    · simp only [add_of_imp fun hx hy ↦ h ⟨hx, hy⟩, mapFun]
      rw [add_of_imp]
      · simp only [some.injEq, ← baseChange_addX, ← baseChange_addY, ← baseChange_slope]
      · push_neg at h; rwa [baseChange_negY, inj.eq_iff, inj.ne_iff]

lemma map_zero : map W f (0 : W⟮F⟯) = 0 :=
  rfl

lemma map_some {x y : F} (h : (W.baseChange F).toAffine.Nonsingular x y) :
    map W f (some h) = some ((W.baseChange_nonsingular f.injective ..).mpr h) :=
  rfl

lemma map_id (P : W⟮F⟯) : map W (Algebra.ofId F F) P = P := by
  cases P <;> rfl

lemma map_map (P : W⟮F⟯) : map W g (map W f P) = map W (g.comp f) P := by
  cases P <;> rfl

lemma map_injective : Function.Injective <| map W f := by
  rintro (_ | _) (_ | _) h
  any_goals contradiction
  · rfl
  · simpa only [some.injEq] using ⟨f.injective (some.inj h).left, f.injective (some.inj h).right⟩

variable (F K) in
/-- The group homomorphism from `W⟮F⟯` to `W⟮K⟯` induced by the base change from `F` to `K`,
where `W` is defined over a subring of a ring `S`, and `F` and `K` are field extensions of `S`. -/
abbrev baseChange [Algebra F K] [IsScalarTower R F K] : W⟮F⟯ →+ W⟮K⟯ :=
  map W <| Algebra.ofId F K

lemma map_baseChange [Algebra F K] [IsScalarTower R F K] [Algebra F L] [IsScalarTower R F L]
    (f : K →ₐ[F] L) (P : W⟮F⟯) : map W f (baseChange W F K P) = baseChange W F L P := by
  have : Subsingleton (F →ₐ[F] L) := inferInstance
  convert map_map W (Algebra.ofId F K) f P

end Point

end BaseChange

@[deprecated (since := "2024-06-03")] alias addY' := negAddY
@[deprecated (since := "2024-06-03")] alias
  nonsingular_add_of_eval_derivative_ne_zero := nonsingular_negAdd_of_eval_derivative_ne_zero
@[deprecated (since := "2024-06-03")] alias slope_of_Yeq := slope_of_Y_eq
@[deprecated (since := "2024-06-03")] alias slope_of_Yne := slope_of_Y_ne
@[deprecated (since := "2024-06-03")] alias slope_of_Xne := slope_of_X_ne
@[deprecated (since := "2024-06-03")] alias slope_of_Yne_eq_eval := slope_of_Y_ne_eq_eval
@[deprecated (since := "2024-06-03")] alias Yeq_of_Xeq := Y_eq_of_X_eq
@[deprecated (since := "2024-06-03")] alias Yeq_of_Yne := Y_eq_of_Y_ne
@[deprecated (since := "2024-06-03")] alias equation_add' := equation_negAdd
@[deprecated (since := "2024-06-03")] alias nonsingular_add' := nonsingular_negAdd
@[deprecated (since := "2024-06-03")] alias baseChange_addY' := baseChange_negAddY
@[deprecated (since := "2024-06-03")] alias map_addY' := map_negAddY

end WeierstrassCurve.Affine

/-! ## Elliptic curves -/

/-- The coercion from an elliptic curve to a Weierstrass curve in affine coordinates. -/
abbrev EllipticCurve.toAffine {R : Type u} [CommRing R] (E : EllipticCurve R) :
    WeierstrassCurve.Affine R :=
  E.toWeierstrassCurve.toAffine

namespace EllipticCurve.Affine

variable {R : Type u} [CommRing R] (E : EllipticCurve R)

lemma nonsingular [Nontrivial R] {x y : R} (h : E.toAffine.Equation x y) :
    E.toAffine.Nonsingular x y :=
  E.toAffine.nonsingular_of_Δ_ne_zero h <| E.coe_Δ' ▸ E.Δ'.ne_zero

end EllipticCurve.Affine
