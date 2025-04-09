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
abelian group is proven in `Mathlib/AlgebraicGeometry/EllipticCurve/Group.lean`.

## Mathematical background

Let `W` be a Weierstrass curve over a field `F` with coefficients `aᵢ`. An *affine point*
on `W` is a tuple `(x, y)` of elements in `R` satisfying the *Weierstrass equation* `W(X, Y) = 0` in
*affine coordinates*, where `W(X, Y) := Y² + a₁XY + a₃Y - (X³ + a₂X² + a₄X + a₆)`. It is
*nonsingular* if its partial derivatives `W_X(x, y)` and `W_Y(x, y)` do not vanish simultaneously.

The nonsingular affine points on `W` can be given negation and addition operations defined by a
secant-and-tangent process.
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

The type of nonsingular points `W⟮F⟯` in affine coordinates is an inductive, consisting of the
unique point at infinity `𝓞` and nonsingular affine points `(x, y)`. Then `W⟮F⟯` can be endowed with
a group law, with `𝓞` as the identity nonsingular point, which is uniquely determined by these
formulae.

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
 * `WeierstrassCurve.Affine.nonsingular`: an affine elliptic curve is nonsingular at every point.

## Notations

 * `W⟮K⟯`: the group of nonsingular rational points on `W` base changed to `K`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, affine coordinates
-/

open Polynomial

open scoped Polynomial.Bivariate

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

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} {L : Type w}

variable (R) in
/-- An abbreviation for a Weierstrass curve in affine coordinates. -/
abbrev Affine : Type r :=
  WeierstrassCurve R

/-- The conversion from a Weierstrass curve to affine coordinates. -/
abbrev toAffine (W : WeierstrassCurve R) : Affine R :=
  W

namespace Affine

variable [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Field F] [Field K] [Field L]
  {W' : Affine R} {W : Affine F}

section Equation

/-! ### Weierstrass equations -/

variable (W') in
/-- The polynomial `W(X, Y) := Y² + a₁XY + a₃Y - (X³ + a₂X² + a₄X + a₆)` associated to a Weierstrass
curve `W` over a ring `R` in affine coordinates.

For ease of polynomial manipulation, this is represented as a term of type `R[X][X]`, where the
inner variable represents `X` and the outer variable represents `Y`. For clarity, the alternative
notations `Y` and `R[X][Y]` are provided in the `Polynomial.Bivariate` scope to represent the outer
variable and the bivariate polynomial ring `R[X][X]` respectively. -/
noncomputable def polynomial : R[X][Y] :=
  Y ^ 2 + C (C W'.a₁ * X + C W'.a₃) * Y - C (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆)

lemma polynomial_eq : W'.polynomial = Cubic.toPoly
    ⟨0, 1, Cubic.toPoly ⟨0, 0, W'.a₁, W'.a₃⟩, Cubic.toPoly ⟨-1, -W'.a₂, -W'.a₄, -W'.a₆⟩⟩ := by
  simp only [polynomial, Cubic.toPoly]
  C_simp
  ring1

lemma polynomial_ne_zero [Nontrivial R] : W'.polynomial ≠ 0 := by
  rw [polynomial_eq]
  exact Cubic.ne_zero_of_b_ne_zero one_ne_zero

@[simp]
lemma degree_polynomial [Nontrivial R] : W'.polynomial.degree = 2 := by
  rw [polynomial_eq]
  exact Cubic.degree_of_b_ne_zero' one_ne_zero

@[simp]
lemma natDegree_polynomial [Nontrivial R] : W'.polynomial.natDegree = 2 := by
  rw [polynomial_eq]
  exact Cubic.natDegree_of_b_ne_zero' one_ne_zero

lemma monic_polynomial : W'.polynomial.Monic := by
  nontriviality R
  simpa only [polynomial_eq] using Cubic.monic_of_b_eq_one'

lemma irreducible_polynomial [IsDomain R] : Irreducible W'.polynomial := by
  by_contra h
  rcases (monic_polynomial.not_irreducible_iff_exists_add_mul_eq_coeff natDegree_polynomial).mp h
    with ⟨f, g, h0, h1⟩
  simp only [polynomial_eq, Cubic.coeff_eq_c, Cubic.coeff_eq_d] at h0 h1
  apply_fun degree at h0 h1
  rw [Cubic.degree_of_a_ne_zero' <| neg_ne_zero.mpr <| one_ne_zero' R, degree_mul] at h0
  apply (h1.symm.le.trans Cubic.degree_of_b_eq_zero').not_lt
  rcases Nat.WithBot.add_eq_three_iff.mp h0.symm with h | h | h | h
  iterate 2 rw [degree_add_eq_right_of_degree_lt] <;> simp only [h] <;> decide
  iterate 2 rw [degree_add_eq_left_of_degree_lt] <;> simp only [h] <;> decide

lemma evalEval_polynomial (x y : R) : W'.polynomial.evalEval x y =
    y ^ 2 + W'.a₁ * x * y + W'.a₃ * y - (x ^ 3 + W'.a₂ * x ^ 2 + W'.a₄ * x + W'.a₆) := by
  simp only [polynomial]
  eval_simp
  rw [add_mul, ← add_assoc]

@[simp]
lemma evalEval_polynomial_zero : W'.polynomial.evalEval 0 0 = -W'.a₆ := by
  simp only [evalEval_polynomial, zero_add, zero_sub, mul_zero, zero_pow <| Nat.succ_ne_zero _]

variable (W') in
/-- The proposition that an affine point `(x, y)` lies in a Weierstrass curve `W`.

In other words, it satisfies the Weierstrass equation `W(X, Y) = 0`. -/
def Equation (x y : R) : Prop :=
  W'.polynomial.evalEval x y = 0

lemma equation_iff' (x y : R) : W'.Equation x y ↔
    y ^ 2 + W'.a₁ * x * y + W'.a₃ * y - (x ^ 3 + W'.a₂ * x ^ 2 + W'.a₄ * x + W'.a₆) = 0 := by
  rw [Equation, evalEval_polynomial]

lemma equation_iff (x y : R) : W'.Equation x y ↔
    y ^ 2 + W'.a₁ * x * y + W'.a₃ * y = x ^ 3 + W'.a₂ * x ^ 2 + W'.a₄ * x + W'.a₆ := by
  rw [equation_iff', sub_eq_zero]

@[simp]
lemma equation_zero : W'.Equation 0 0 ↔ W'.a₆ = 0 := by
  rw [Equation, evalEval_polynomial_zero, neg_eq_zero]

lemma equation_iff_variableChange (x y : R) :
    W'.Equation x y ↔ (W'.variableChange ⟨1, x, 0, y⟩).toAffine.Equation 0 0 := by
  rw [equation_iff', ← neg_eq_zero, equation_zero, variableChange_a₆, inv_one, Units.val_one]
  congr! 1
  ring1

end Equation

section Nonsingular

/-! ### Nonsingular Weierstrass equations -/

variable (W') in
/-- The partial derivative `W_X(X, Y)` with respect to `X` of the polynomial `W(X, Y)` associated to
a Weierstrass curve `W` in affine coordinates. -/
-- TODO: define this in terms of `Polynomial.derivative`.
noncomputable def polynomialX : R[X][Y] :=
  C (C W'.a₁) * Y - C (C 3 * X ^ 2 + C (2 * W'.a₂) * X + C W'.a₄)

lemma evalEval_polynomialX (x y : R) :
    W'.polynomialX.evalEval x y = W'.a₁ * y - (3 * x ^ 2 + 2 * W'.a₂ * x + W'.a₄) := by
  simp only [polynomialX]
  eval_simp

@[simp]
lemma evalEval_polynomialX_zero : W'.polynomialX.evalEval 0 0 = -W'.a₄ := by
  simp only [evalEval_polynomialX, zero_add, zero_sub, mul_zero, zero_pow <| Nat.succ_ne_zero _]

variable (W') in
/-- The partial derivative `W_Y(X, Y)` with respect to `Y` of the polynomial `W(X, Y)` associated to
a Weierstrass curve `W` in affine coordinates. -/
-- TODO: define this in terms of `Polynomial.derivative`.
noncomputable def polynomialY : R[X][Y] :=
  C (C 2) * Y + C (C W'.a₁ * X + C W'.a₃)

lemma evalEval_polynomialY (x y : R) : W'.polynomialY.evalEval x y = 2 * y + W'.a₁ * x + W'.a₃ := by
  simp only [polynomialY]
  eval_simp
  rw [← add_assoc]

@[simp]
lemma evalEval_polynomialY_zero : W'.polynomialY.evalEval 0 0 = W'.a₃ := by
  simp only [evalEval_polynomialY, zero_add, mul_zero]

variable (W') in
/-- The proposition that an affine point `(x, y)` on a Weierstrass curve `W` is nonsingular.

In other words, either `W_X(x, y) ≠ 0` or `W_Y(x, y) ≠ 0`.

Note that this definition is only mathematically accurate for fields. -/
-- TODO: generalise this definition to be mathematically accurate for a larger class of rings.
def Nonsingular (x y : R) : Prop :=
  W'.Equation x y ∧ (W'.polynomialX.evalEval x y ≠ 0 ∨ W'.polynomialY.evalEval x y ≠ 0)

lemma nonsingular_iff' (x y : R) : W'.Nonsingular x y ↔ W'.Equation x y ∧
    (W'.a₁ * y - (3 * x ^ 2 + 2 * W'.a₂ * x + W'.a₄) ≠ 0 ∨ 2 * y + W'.a₁ * x + W'.a₃ ≠ 0) := by
  rw [Nonsingular, equation_iff', evalEval_polynomialX, evalEval_polynomialY]

lemma nonsingular_iff (x y : R) : W'.Nonsingular x y ↔ W'.Equation x y ∧
    (W'.a₁ * y ≠ 3 * x ^ 2 + 2 * W'.a₂ * x + W'.a₄ ∨ y ≠ -y - W'.a₁ * x - W'.a₃) := by
  rw [nonsingular_iff', sub_ne_zero, ← sub_ne_zero (a := y)]
  congr! 3
  ring1

@[simp]
lemma nonsingular_zero : W'.Nonsingular 0 0 ↔ W'.a₆ = 0 ∧ (W'.a₃ ≠ 0 ∨ W'.a₄ ≠ 0) := by
  rw [Nonsingular, equation_zero, evalEval_polynomialX_zero, neg_ne_zero, evalEval_polynomialY_zero,
    or_comm]

lemma nonsingular_iff_variableChange (x y : R) :
    W'.Nonsingular x y ↔ (W'.variableChange ⟨1, x, 0, y⟩).toAffine.Nonsingular 0 0 := by
  rw [nonsingular_iff', equation_iff_variableChange, equation_zero, ← neg_ne_zero, or_comm,
    nonsingular_zero, variableChange_a₃, variableChange_a₄, inv_one, Units.val_one]
  simp only [variableChange]
  congr! 3 <;> ring1

private lemma equation_zero_iff_nonsingular_zero_of_Δ_ne_zero (hΔ : W'.Δ ≠ 0) :
    W'.Equation 0 0 ↔ W'.Nonsingular 0 0 := by
  simp only [equation_zero, nonsingular_zero, iff_self_and]
  contrapose! hΔ
  simp only [b₂, b₄, b₆, b₈, Δ, hΔ]
  ring1

/-- A Weierstrass curve is nonsingular at every point if its discriminant is non-zero. -/
lemma equation_iff_nonsingular_of_Δ_ne_zero {x y : R} (hΔ : W'.Δ ≠ 0) :
    W'.Equation x y ↔ W'.Nonsingular x y := by
  rw [equation_iff_variableChange, nonsingular_iff_variableChange,
    equation_zero_iff_nonsingular_zero_of_Δ_ne_zero <| by
      rwa [variableChange_Δ, inv_one, Units.val_one, one_pow, one_mul]]

/-- An elliptic curve is nonsingular at every point. -/
lemma equation_iff_nonsingular [Nontrivial R] [W'.IsElliptic] {x y : R} :
    W'.toAffine.Equation x y ↔ W'.toAffine.Nonsingular x y :=
  W'.toAffine.equation_iff_nonsingular_of_Δ_ne_zero <| W'.coe_Δ' ▸ W'.Δ'.ne_zero

@[deprecated (since := "2025-03-01")] alias nonsingular_zero_of_Δ_ne_zero :=
  equation_iff_nonsingular_of_Δ_ne_zero
@[deprecated (since := "2025-03-01")] alias nonsingular_of_Δ_ne_zero :=
  equation_iff_nonsingular_of_Δ_ne_zero
@[deprecated (since := "2025-03-01")] alias nonsingular := equation_iff_nonsingular

end Nonsingular

section Ring

/-! ### Group operation polynomials over a ring -/

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
  simp only [negY]
  ring1

lemma evalEval_negPolynomial (x y : R) : W'.negPolynomial.evalEval x y = W'.negY x y := by
  rw [negY, sub_sub, negPolynomial]
  eval_simp

@[deprecated (since := "2025-03-05")] alias eval_negPolynomial := evalEval_negPolynomial

/-- The line polynomial `ℓ(X - x) + y` associated to the line `Y = ℓ(X - x) + y` that passes through
a nonsingular affine point `(x, y)` on a Weierstrass curve `W` with a slope of `ℓ`.

This does not depend on `W`, and has argument order: `x`, `y`, `ℓ`. -/
noncomputable def linePolynomial (x y ℓ : R) : R[X] :=
  C ℓ * (X - C x) + C y

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

lemma equation_neg (x y : R) : W'.Equation x (W'.negY x y) ↔ W'.Equation x y := by
  rw [equation_iff, equation_iff, negY]
  congr! 1
  ring1

@[deprecated (since := "2025-02-01")] alias equation_neg_of := equation_neg
@[deprecated (since := "2025-02-01")] alias equation_neg_iff := equation_neg

lemma nonsingular_neg (x y : R) : W'.Nonsingular x (W'.negY x y) ↔ W'.Nonsingular x y := by
  rw [nonsingular_iff, equation_neg, ← negY, negY_negY, ← @ne_comm _ y, nonsingular_iff]
  exact and_congr_right' <| (iff_congr not_and_or.symm not_and_or.symm).mpr <|
    not_congr <| and_congr_left fun h => by rw [← h]

@[deprecated (since := "2025-02-01")] alias nonsingular_neg_of := nonsingular_neg
@[deprecated (since := "2025-02-01")] alias nonsingular_neg_iff := nonsingular_neg

lemma equation_add_iff (x₁ x₂ y₁ ℓ : R) : W'.Equation (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ) ↔
    (W'.addPolynomial x₁ y₁ ℓ).eval (W'.addX x₁ x₂ ℓ) = 0 := by
  rw [Equation, negAddY, addPolynomial, linePolynomial, polynomial]
  eval_simp

lemma nonsingular_negAdd_of_eval_derivative_ne_zero {x₁ x₂ y₁ ℓ : R}
    (hx' : W'.Equation (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ))
    (hx : (W'.addPolynomial x₁ y₁ ℓ).derivative.eval (W'.addX x₁ x₂ ℓ) ≠ 0) :
    W'.Nonsingular (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ) := by
  rw [Nonsingular, and_iff_right hx', negAddY, polynomialX, polynomialY]
  eval_simp
  contrapose! hx
  rw [addPolynomial, linePolynomial, polynomial]
  eval_simp
  derivative_simp
  simp only [zero_add, add_zero, sub_zero, zero_mul, mul_one]
  eval_simp
  linear_combination (norm := (norm_num1; ring1)) hx.left + ℓ * hx.right

end Ring

section Field

/-! ### Group operation polynomials over a field -/

open Classical in
variable (W) in
/-- The slope of the line through two nonsingular affine points `(x₁, y₁)` and `(x₂, y₂)` on a
Weierstrass curve `W`.

If `x₁ ≠ x₂`, then this line is the secant of `W` through `(x₁, y₁)` and `(x₂, y₂)`, and has slope
`(y₁ - y₂) / (x₁ - x₂)`. Otherwise, if `y₁ ≠ -y₁ - a₁x₁ - a₃`, then this line is the tangent of `W`
at `(x₁, y₁) = (x₂, y₂)`, and has slope `(3x₁² + 2a₂x₁ + a₄ - a₁y₁) / (2y₁ + a₁x₁ + a₃)`. Otherwise,
this line is vertical, in which case this returns the value `0`.

This depends on `W`, and has argument order: `x₁`, `x₂`, `y₁`, `y₂`. -/
noncomputable def slope (x₁ x₂ y₁ y₂ : F) : F :=
  if x₁ = x₂ then if y₁ = W.negY x₂ y₂ then 0
    else (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.negY x₁ y₁)
  else (y₁ - y₂) / (x₁ - x₂)

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

lemma slope_of_Y_ne_eq_evalEval {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) :
    W.slope x₁ x₂ y₁ y₂ = -W.polynomialX.evalEval x₁ y₁ / W.polynomialY.evalEval x₁ y₁ := by
  rw [slope_of_Y_ne hx hy, evalEval_polynomialX, neg_sub]
  congr 1
  rw [negY, evalEval_polynomialY]
  ring1

@[deprecated (since := "2025-03-05")] alias slope_of_Y_ne_eq_eval := slope_of_Y_ne_eq_evalEval

lemma Y_eq_of_X_eq {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hx : x₁ = x₂) : y₁ = y₂ ∨ y₁ = W.negY x₂ y₂ := by
  rw [equation_iff] at h₁ h₂
  rw [← sub_eq_zero, ← sub_eq_zero (a := y₁), ← mul_eq_zero, negY]
  linear_combination (norm := (rw [hx]; ring1)) h₁ - h₂

lemma Y_eq_of_Y_ne {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hx : x₁ = x₂)
    (hy : y₁ ≠ W.negY x₂ y₂) : y₁ = y₂ :=
  (Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy

lemma addPolynomial_slope {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) : W.addPolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂) =
      -((X - C x₁) * (X - C x₂) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂))) := by
  rw [addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective]
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    rcases hx, Y_eq_of_Y_ne h₁ h₂ hx hy with ⟨rfl, rfl⟩
    rw [equation_iff] at h₁ h₂
    rw [slope_of_Y_ne rfl hy]
    rw [negY, ← sub_ne_zero] at hy
    ext
    · rfl
    · simp only [addX]
      ring1
    · field_simp [hy]
      ring1
    · linear_combination (norm := (field_simp [hy]; ring1)) -h₁
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
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) : W.Equation
      (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.negAddY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  rw [equation_add_iff, addPolynomial_slope h₁ h₂ hxy]
  eval_simp
  rw [neg_eq_zero, sub_self, mul_zero]

/-- The addition of two affine points in `W` on a sloped line lies in `W`. -/
lemma equation_add {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    W.Equation (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) :=
  (equation_neg ..).mpr <| equation_negAdd h₁ h₂ hxy

lemma C_addPolynomial_slope {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) : C (W.addPolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) =
      -(C (X - C x₁) * C (X - C x₂) * C (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂))) := by
  rw [addPolynomial_slope h₁ h₂ hxy]
  map_simp

lemma derivative_addPolynomial_slope {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h₂ : W.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    derivative (W.addPolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) =
      -((X - C x₁) * (X - C x₂) + (X - C x₁) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)) +
          (X - C x₂) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂))) := by
  rw [addPolynomial_slope h₁ h₂ hxy]
  derivative_simp
  ring1

/-- The negated addition of two nonsingular affine points in `W` on a sloped line is nonsingular. -/
lemma nonsingular_negAdd {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) : W.Nonsingular
      (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.negAddY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  by_cases hx₁ : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₁
  · rwa [negAddY, hx₁, sub_self, mul_zero, zero_add]
  · by_cases hx₂ : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₂
    · by_cases hx : x₁ = x₂
      · subst hx
        contradiction
      · rwa [negAddY, ← neg_sub, mul_neg, hx₂, slope_of_X_ne hx,
          div_mul_cancel₀ _ <| sub_ne_zero_of_ne hx, neg_sub, sub_add_cancel]
    · apply nonsingular_negAdd_of_eval_derivative_ne_zero <| equation_negAdd h₁.left h₂.left hxy
      rw [derivative_addPolynomial_slope h₁.left h₂.left hxy]
      eval_simp
      simp only [neg_ne_zero, sub_self, mul_zero, add_zero]
      exact mul_ne_zero (sub_ne_zero_of_ne hx₁) (sub_ne_zero_of_ne hx₂)

/-- The addition of two nonsingular affine points in `W` on a sloped line is nonsingular. -/
lemma nonsingular_add {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    W.Nonsingular (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) :=
  (nonsingular_neg ..).mpr <| nonsingular_negAdd h₁ h₂ hxy

/-- The formula `x(P₁ + P₂) = x(P₁ - P₂) - ψ(P₁)ψ(P₂) / (x(P₂) - x(P₁))²`,
where `ψ(x,y) = 2y + a₁x + a₃`. -/
lemma addX_eq_addX_negY_sub {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ ≠ x₂) :
    W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = W.addX x₁ x₂ (W.slope x₁ x₂ y₁ <| W.negY x₂ y₂) -
      (y₁ - W.negY x₁ y₁) * (y₂ - W.negY x₂ y₂) / (x₂ - x₁) ^ 2 := by
  simp_rw [slope_of_X_ne hx, addX, negY, ← neg_sub x₁, neg_sq]
  field_simp [sub_ne_zero.mpr hx]
  ring1

/-- The formula `y(P₁)(x(P₂) - x(P₃)) + y(P₂)(x(P₃) - x(P₁)) + y(P₃)(x(P₁) - x(P₂)) = 0`,
assuming that `P₁ + P₂ + P₃ = O`. -/
lemma cyclic_sum_Y_mul_X_sub_X {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ ≠ x₂) :
    let x₃ := W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
    y₁ * (x₂ - x₃) + y₂ * (x₃ - x₁) + W.negAddY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) = 0 := by
  simp_rw [slope_of_X_ne hx, negAddY, addX]
  field_simp [sub_ne_zero.mpr hx]
  ring1

/-- The formula `ψ(P₁ + P₂) = (ψ(P₂)(x(P₁) - x(P₃)) - ψ(P₁)(x(P₂) - x(P₃))) / (x(P₂) - x(P₁))`,
where `ψ(x,y) = 2y + a₁x + a₃`. -/
lemma addY_sub_negY_addY {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ ≠ x₂) :
    let x₃ := W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
    let y₃ := W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)
    y₃ - W.negY x₃ y₃ =
      ((y₂ - W.negY x₂ y₂) * (x₁ - x₃) - (y₁ - W.negY x₁ y₁) * (x₂ - x₃)) / (x₂ - x₁) := by
  simp_rw [addY, negY, eq_div_iff (sub_ne_zero.mpr hx.symm)]
  linear_combination (norm := ring1) 2 * cyclic_sum_Y_mul_X_sub_X y₁ y₂ hx

end Field

section Group

/-! ### Nonsingular points -/

variable (W') in
/-- A nonsingular point on a Weierstrass curve `W` in affine coordinates. This is either the unique
point at infinity `WeierstrassCurve.Affine.Point.zero` or a nonsingular affine point
`WeierstrassCurve.Affine.Point.some (x, y)` satisfying the Weierstrass equation of `W`. -/
inductive Point
  | zero
  | some {x y : R} (h : W'.Nonsingular x y)

/-- For an algebraic extension `S` of a ring `R`, the type of nonsingular `S`-points on a
Weierstrass curve `W` over `R` in affine coordinates. -/
scoped notation3:max W' "⟮" S "⟯" => Affine.Point <| baseChange W' S

namespace Point

/-! ### Group operations -/

instance : Inhabited W'.Point :=
  ⟨.zero⟩

instance : Zero W'.Point :=
  ⟨.zero⟩

lemma zero_def : 0 = (.zero : W'.Point) :=
  rfl

lemma some_ne_zero {x y : R} (h : W'.Nonsingular x y) : Point.some h ≠ 0 := by
  rintro (_ | _)

/-- The negation of a nonsingular point on a Weierstrass curve in affine coordinates.

Given a nonsingular point `P` in affine coordinates, use `-P` instead of `neg P`. -/
def neg : W'.Point → W'.Point
  | 0 => 0
  | some h => some <| (nonsingular_neg ..).mpr h

instance : Neg W'.Point :=
  ⟨neg⟩

lemma neg_def (P : W'.Point) : -P = P.neg :=
  rfl

@[simp]
lemma neg_zero : (-0 : W'.Point) = 0 :=
  rfl

@[simp]
lemma neg_some {x y : R} (h : W'.Nonsingular x y) : -some h = some ((nonsingular_neg ..).mpr h) :=
  rfl

instance : InvolutiveNeg W'.Point where
  neg_neg := by
    rintro (_ | _)
    · rfl
    · simp only [neg_some, negY_negY]

open Classical in
/-- The addition of two nonsingular points on a Weierstrass curve in affine coordinates.

Given two nonsingular points `P` and `Q` in affine coordinates, use `P + Q` instead of `add P Q`. -/
noncomputable def add : W.Point → W.Point → W.Point
  | 0, P => P
  | P, 0 => P
  | @some _ _ _ x₁ y₁ h₁, @some _ _ _ x₂ y₂ h₂ =>
    if hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂ then 0 else some <| nonsingular_add h₁ h₂ hxy

noncomputable instance : Add W.Point :=
  ⟨add⟩

noncomputable instance : AddZeroClass W.Point :=
  ⟨by rintro (_ | _) <;> rfl, by rintro (_ | _) <;> rfl⟩

lemma add_def (P Q : W.Point) : P + Q = P.add Q :=
  rfl

lemma add_some {x₁ x₂ y₁ y₂ : F} (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) {h₁ : W.Nonsingular x₁ y₁}
    {h₂ : W.Nonsingular x₂ y₂} : some h₁ + some h₂ = some (nonsingular_add h₁ h₂ hxy) := by
  simp only [add_def, add, dif_neg hxy]

@[deprecated (since := "2025-02-28")] alias add_of_imp := add_some

@[simp]
lemma add_of_Y_eq {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂) : some h₁ + some h₂ = 0 := by
  simpa only [add_def, add] using dif_pos ⟨hx, hy⟩

@[simp]
lemma add_self_of_Y_eq {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ = W.negY x₁ y₁) :
    some h₁ + some h₁ = 0 :=
  add_of_Y_eq rfl hy

@[simp]
lemma add_of_Y_ne {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hy : y₁ ≠ W.negY x₂ y₂) :
    some h₁ + some h₂ = some (nonsingular_add h₁ h₂ fun hxy => hy hxy.right) :=
  add_some fun hxy => hy hxy.right

lemma add_of_Y_ne' {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hy : y₁ ≠ W.negY x₂ y₂) :
    some h₁ + some h₂ = -some (nonsingular_negAdd h₁ h₂ fun hxy => hy hxy.right) :=
  add_of_Y_ne hy

@[simp]
lemma add_self_of_Y_ne {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ ≠ W.negY x₁ y₁) :
    some h₁ + some h₁ = some (nonsingular_add h₁ h₁ fun hxy => hy hxy.right) :=
  add_of_Y_ne hy

lemma add_self_of_Y_ne' {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ ≠ W.negY x₁ y₁) :
    some h₁ + some h₁ = -some (nonsingular_negAdd h₁ h₁ fun hxy => hy hxy.right) :=
  add_of_Y_ne hy

@[simp]
lemma add_of_X_ne {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) : some h₁ + some h₂ = some (nonsingular_add h₁ h₂ fun hxy => hx hxy.left) :=
  add_some fun hxy => hx hxy.left

lemma add_of_X_ne' {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) : some h₁ + some h₂ = -some (nonsingular_negAdd h₁ h₂ fun hxy => hx hxy.left) :=
  add_of_X_ne hx

end Point

end Group

section Map

/-! ### Maps across ring homomorphisms -/

variable (f : R →+* S) (x y x₁ y₁ x₂ y₂ ℓ : R)

lemma map_polynomial : (W'.map f).toAffine.polynomial = W'.polynomial.map (mapRingHom f) := by
  simp only [polynomial]
  map_simp

lemma evalEval_baseChange_polynomial :
    (W'.baseChange R[X][Y]).toAffine.polynomial.evalEval (C X) Y = W'.polynomial := by
  rw [map_polynomial, evalEval, eval_map, eval_C_X_eval₂_map_C_X]

@[deprecated (since := "2025-03-05")] alias evalEval_baseChange_polynomial_X_Y :=
  evalEval_baseChange_polynomial

variable {x y} in
lemma Equation.map {x y : R} (h : W'.Equation x y) : (W'.map f).toAffine.Equation (f x) (f y) := by
  rw [Equation, map_polynomial, map_mapRingHom_evalEval, h, map_zero]

variable {f} in
lemma map_equation (hf : Function.Injective f) :
    (W'.map f).toAffine.Equation (f x) (f y) ↔ W'.Equation x y := by
  simp only [Equation, map_polynomial, map_mapRingHom_evalEval, map_eq_zero_iff f hf]

lemma map_polynomialX : (W'.map f).toAffine.polynomialX = W'.polynomialX.map (mapRingHom f) := by
  simp only [polynomialX]
  map_simp

lemma map_polynomialY : (W'.map f).toAffine.polynomialY = W'.polynomialY.map (mapRingHom f) := by
  simp only [polynomialY]
  map_simp

variable {f} in
lemma map_nonsingular (hf : Function.Injective f) :
    (W'.map f).toAffine.Nonsingular (f x) (f y) ↔ W'.Nonsingular x y := by
  simp only [Nonsingular, evalEval, map_equation _ _ hf, map_polynomialX, map_polynomialY,
    map_mapRingHom_evalEval, map_ne_zero_iff f hf]

lemma map_negPolynomial :
    (W'.map f).toAffine.negPolynomial = W'.negPolynomial.map (mapRingHom f) := by
  simp only [negPolynomial]
  map_simp

lemma map_negY : (W'.map f).toAffine.negY (f x) (f y) = f (W'.negY x y) := by
  simp only [negY]
  map_simp

lemma map_linePolynomial : linePolynomial (f x) (f y) (f ℓ) = (linePolynomial x y ℓ).map f := by
  simp only [linePolynomial]
  map_simp

lemma map_addPolynomial :
    (W'.map f).toAffine.addPolynomial (f x) (f y) (f ℓ) = (W'.addPolynomial x y ℓ).map f := by
  rw [addPolynomial, map_polynomial, eval_map, linePolynomial, addPolynomial, ← coe_mapRingHom,
    ← eval₂_hom, linePolynomial]
  map_simp

lemma map_addX : (W'.map f).toAffine.addX (f x₁) (f x₂) (f ℓ) = f (W'.addX x₁ x₂ ℓ) := by
  simp only [addX]
  map_simp

lemma map_negAddY :
    (W'.map f).toAffine.negAddY (f x₁) (f x₂) (f y₁) (f ℓ) = f (W'.negAddY x₁ x₂ y₁ ℓ) := by
  simp only [negAddY, map_addX]
  map_simp

lemma map_addY :
    (W'.map f).toAffine.addY (f x₁) (f x₂) (f y₁) (f ℓ) = f (W'.toAffine.addY x₁ x₂ y₁ ℓ) := by
  simp only [addY, map_negAddY, map_addX, map_negY]

lemma map_slope (f : F →+* K) (x₁ x₂ y₁ y₂ : F) :
    (W.map f).toAffine.slope (f x₁) (f x₂) (f y₁) (f y₂) = f (W.slope x₁ x₂ y₁ y₂) := by
  by_cases hx : x₁ = x₂
  · by_cases hy : y₁ = W.negY x₂ y₂
    · rw [slope_of_Y_eq (congr_arg f hx) <| by rw [hy, map_negY], slope_of_Y_eq hx hy, map_zero]
    · rw [slope_of_Y_ne (congr_arg f hx) <| map_negY f x₂ y₂ ▸ fun h => hy <| f.injective h,
        map_negY, slope_of_Y_ne hx hy]
      map_simp
  · rw [slope_of_X_ne fun h => hx <| f.injective h, slope_of_X_ne hx]
    map_simp

end Map

section BaseChange

/-! ### Base changes across algebra homomorphisms -/

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A →ₐ[S] B) (x y x₁ y₁ x₂ y₂ ℓ : A)

lemma baseChange_polynomial : (W'.baseChange B).toAffine.polynomial =
    (W'.baseChange A).toAffine.polynomial.map (mapRingHom f) := by
  rw [← map_polynomial, map_baseChange]

variable {x y} in
lemma Equation.baseChange (h : (W'.baseChange A).toAffine.Equation x y) :
    (W'.baseChange B).toAffine.Equation (f x) (f y) := by
  convert Equation.map f.toRingHom h using 1
  rw [AlgHom.toRingHom_eq_coe, map_baseChange]

variable {f} in
lemma baseChange_equation (hf : Function.Injective f) :
    (W'.baseChange B).toAffine.Equation (f x) (f y) ↔ (W'.baseChange A).toAffine.Equation x y := by
  rw [← map_equation _ _ hf, AlgHom.toRingHom_eq_coe, map_baseChange, RingHom.coe_coe]

lemma baseChange_polynomialX : (W'.baseChange B).toAffine.polynomialX =
    (W'.baseChange A).toAffine.polynomialX.map (mapRingHom f) := by
  rw [← map_polynomialX, map_baseChange]

lemma baseChange_polynomialY : (W'.baseChange B).toAffine.polynomialY =
    (W'.baseChange A).toAffine.polynomialY.map (mapRingHom f) := by
  rw [← map_polynomialY, map_baseChange]

variable {f} in
lemma baseChange_nonsingular (hf : Function.Injective f) :
    (W'.baseChange B).toAffine.Nonsingular (f x) (f y) ↔
      (W'.baseChange A).toAffine.Nonsingular x y := by
  rw [← map_nonsingular _ _ hf, AlgHom.toRingHom_eq_coe, map_baseChange, RingHom.coe_coe]

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

lemma baseChange_slope [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] (f : F →ₐ[S] K) (x₁ x₂ y₁ y₂ : F) :
  (W'.baseChange K).toAffine.slope (f x₁) (f x₂) (f y₁) (f y₂) =
    f ((W'.baseChange F).toAffine.slope x₁ x₂ y₁ y₂) := by
  rw [← RingHom.coe_coe, ← map_slope, map_baseChange]

end BaseChange

namespace Point

variable [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] [Algebra R L] [Algebra S L] [IsScalarTower R S L] (f : F →ₐ[S] K)
  (g : K →ₐ[S] L)

/-- The group homomorphism from `W⟮F⟯` to `W⟮K⟯` induced by an algebra homomorphism `f : F →ₐ[S] K`,
where `W` is defined over a subring of a ring `S`, and `F` and `K` are field extensions of `S`. -/
noncomputable def map : W'⟮F⟯ →+ W'⟮K⟯ where
  toFun P := match P with
    | 0 => 0
    | some h => some <| (baseChange_nonsingular _ _ f.injective).mpr h
  map_zero' := rfl
  map_add' := by
    rintro (_ | @⟨x₁, y₁, _⟩) (_ | @⟨x₂, y₂, _⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = (W'.baseChange F).toAffine.negY x₂ y₂
    · simp only [add_of_Y_eq hxy.left hxy.right]
      rw [add_of_Y_eq (congr_arg _ hxy.left) <| by rw [hxy.right, baseChange_negY]]
    · simp only [add_some hxy, ← baseChange_addX, ← baseChange_addY, ← baseChange_slope]
      rw [add_some fun h => hxy ⟨f.injective h.1, f.injective (W'.baseChange_negY f .. ▸ h).2⟩]

@[deprecated (since := "2025-03-01")] alias mapFun := map

lemma map_zero : map f (0 : W'⟮F⟯) = 0 :=
  rfl

lemma map_some {x y : F} (h : (W'.baseChange F).toAffine.Nonsingular x y) :
    map f (some h) = some ((W'.baseChange_nonsingular _ _ f.injective).mpr h) :=
  rfl

lemma map_id (P : W'⟮F⟯) : map (Algebra.ofId F F) P = P := by
  cases P <;> rfl

lemma map_map (P : W'⟮F⟯) : map g (map f P) = map (g.comp f) P := by
  cases P <;> rfl

lemma map_injective : Function.Injective <| map (W' := W') f := by
  rintro (_ | _) (_ | _) h
  any_goals contradiction
  · rfl
  · simpa only [some.injEq] using ⟨f.injective (some.inj h).left, f.injective (some.inj h).right⟩

variable (F K) in
/-- The group homomorphism from `W⟮F⟯` to `W⟮K⟯` induced by the base change from `F` to `K`, where
`W` is defined over a subring of a ring `S`, and `F` and `K` are field extensions of `S`. -/
noncomputable abbrev baseChange [Algebra F K] [IsScalarTower R F K] : W'⟮F⟯ →+ W'⟮K⟯ :=
  map <| Algebra.ofId F K

lemma map_baseChange [Algebra F K] [IsScalarTower R F K] [Algebra F L] [IsScalarTower R F L]
    (f : K →ₐ[F] L) (P : W'⟮F⟯) : map f (baseChange F K P) = baseChange F L P := by
  have : Subsingleton (F →ₐ[F] L) := inferInstance
  convert map_map (Algebra.ofId F K) f P

end Point

end Affine

end WeierstrassCurve
