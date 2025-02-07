/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Formulae for group operations of Weierstrass curves in affine coordinates

This file defines the type of points on a Weierstrass curve as an inductive, consisting of the point
at infinity and affine points satisfying a Weierstrass equation with a nonsingular condition. This
file also defines the negation and addition operations of the group law for this type, and proves
that they respect the Weierstrass equation and the nonsingular condition. The fact that they form an
abelian group is proven in `Mathlib/AlgebraicGeometry/EllipticCurve/Group.lean`.

## Mathematical background

Let `W` be a Weierstrass curve over a field `F`. A rational point on `W` is simply a point
`[X:Y:Z]` defined over `F` in the projective plane satisfying the homogeneous cubic equation
`Y²Z + a₁XYZ + a₃YZ² = X³ + a₂X²Z + a₄XZ² + a₆Z³`. Any such point either lies in the affine chart
`Z ≠ 0` and satisfies the Weierstrass equation obtained by replacing `X / Z` with `X` and `Y / Z`
with `Y`, or is the unique point at infinity `𝓞 := [0:1:0]` when `Z = 0`. With this new description,
a nonsingular rational point on `W` is either `𝓞` or an affine point `(x, y)` where the partial
derivatives `W_X(X, Y)` and `W_Y(X, Y)` do not vanish simultaneously. For a field extension `K` of
`F`, a `K`-rational point is simply a rational point on `W` base changed to `K`.

The set of nonsingular rational points forms an abelian group under a secant-and-tangent process.
 * The identity rational point is `0`.
 * Given a nonsingular rational point `P`, its negation `-P` is defined to be the unique third
    point of intersection between `W` and the line through `0` and `P`.
    Explicitly, if `P` is `(x, y)`, then `-P` is `(x, -y - a₁x - a₃)`.
 * Given two points `P` and `Q`, their addition `P + Q` is defined to be the negation of the unique
    third point of intersection between `W` and the line `L` through `P` and `Q`.
    Explicitly, let `P` be `(x₁, y₁)` and let `Q` be `(x₂, y₂)`.
      * If `x₁ = x₂` and `y₁ = -y₂ - a₁x₂ - a₃`, then `L` is vertical and `P + Q` is `𝓞`.
      * If `x₁ = x₂` and `y₁ ≠ -y₂ - a₁x₂ - a₃`, then `L` is the tangent of `W` at `P = Q`,
        and has slope `ℓ := (3x₁² + 2a₂x₁ + a₄ - a₁y₁) / (2y₁ + a₁x₁ + a₃)`.
      * Otherwise `x₁ ≠ x₂`, then `L` is the secant of `W` through `P` and `Q`, and has slope
        `ℓ := (y₁ - y₂) / (x₁ - x₂)`.

    In the latter two cases, the `X`-coordinate of `P + Q` is then the unique third solution of the
    equation obtained by substituting the line `Y = ℓ(X - x₁) + y₁` into the Weierstrass equation,
    and can be written down explicitly as `x := ℓ² + a₁ℓ - a₂ - x₁ - x₂` by inspecting the `X²`
    terms. The `Y`-coordinate of `P + Q`, after applying the final negation that maps `Y` to
    `-Y - a₁X - a₃`, is precisely `y := -(ℓ(x - x₁) + y₁) - a₁x - a₃`.

The group law on this set is then uniquely determined by these constructions.

## Main definitions

 * `WeierstrassCurve.Affine.negPolynomial`: the polynomial associated to `-P`.
 * `WeierstrassCurve.Affine.negY`: the `Y`-coordinate of `-P`.
 * `WeierstrassCurve.Affine.linePolynomial`: the polynomial defined by a line through `P` and `Q`.
 * `WeierstrassCurve.Affine.slope`: the slope of the line through `P` and `Q`.
 * `WeierstrassCurve.Affine.addPolynomial`: the polynomial associated to `P + Q`.
 * `WeierstrassCurve.Affine.addX`: the `X`-coordinate of `P + Q`.
 * `WeierstrassCurve.Affine.negAddY`: the `Y`-coordinate of `-(P + Q)`.
 * `WeierstrassCurve.Affine.addY`: the `Y`-coordinate of `P + Q`.

## Main statements

 * `WeierstrassCurve.Affine.equation_neg`: negation preserves the Weierstrass equation.
 * `WeierstrassCurve.Affine.nonsingular_neg`: negation preserves the nonsingular condition.
 * `WeierstrassCurve.Affine.equation_add`: addition preserves the Weierstrass equation.
 * `WeierstrassCurve.Affine.nonsingular_add`: addition preserves the nonsingular condition.

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

namespace WeierstrassCurve.Affine

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Field F] [Field K] {W' : Affine R} {W : Affine F}

section Negation

/-! ### Negation formulae -/

variable (W') in
/-- The polynomial `-Y - a₁X - a₃` associated to negation. -/
noncomputable def negPolynomial : R[X][Y] :=
  -(Y : R[X][Y]) - C (C W'.a₁ * X + C W'.a₃)

lemma Y_sub_polynomialY : Y - W'.polynomialY = W'.negPolynomial := by
  rw [polynomialY, negPolynomial]
  C_simp
  ring1

lemma Y_sub_negPolynomial : Y - W'.negPolynomial = W'.polynomialY := by
  rw [← Y_sub_polynomialY, sub_sub_cancel]

variable (W') in
/-- The `Y`-coordinate of the negation of an affine point in `W`.

This depends on `W`, and has argument order: `x`, `y`. -/
@[simp]
def negY (x y : R) : R :=
  -y - W'.a₁ * x - W'.a₃

lemma negY_negY (x y : R) : W'.negY x (W'.negY x y) = y := by
  simp only [negY]
  ring1

lemma eval_negPolynomial (x y : R) : W'.negPolynomial.evalEval x y = W'.negY x y := by
  rw [negY, sub_sub, negPolynomial]
  eval_simp

lemma Y_eq_of_X_eq {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hx : x₁ = x₂) : y₁ = y₂ ∨ y₁ = W.negY x₂ y₂ := by
  rw [equation_iff] at h₁ h₂
  rw [← sub_eq_zero, ← sub_eq_zero (a := y₁), ← mul_eq_zero, negY]
  linear_combination (norm := (rw [hx]; ring1)) h₁ - h₂

lemma Y_eq_of_Y_ne {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hx : x₁ = x₂)
    (hy : y₁ ≠ W.negY x₂ y₂) : y₁ = y₂ :=
  (Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy

/-- The negation of an affine point in `W` lies in `W`. -/
lemma equation_neg (x y : R) : W'.Equation x (W'.negY x y) ↔ W'.Equation x y := by
  rw [equation_iff, equation_iff, negY]
  congr! 1
  ring1

@[deprecated (since := "2025-02-01")] alias equation_neg_of := equation_neg
@[deprecated (since := "2025-02-01")] alias equation_neg_iff := equation_neg

/-- The negation of a nonsingular affine point in `W` is nonsingular. -/
lemma nonsingular_neg (x y : R) : W'.Nonsingular x (W'.negY x y) ↔ W'.Nonsingular x y := by
  rw [nonsingular_iff, equation_neg, ← negY, negY_negY, ← @ne_comm _ y, nonsingular_iff]
  exact and_congr_right' <| (iff_congr not_and_or.symm not_and_or.symm).mpr <|
    not_congr <| and_congr_left fun h => by rw [← h]

@[deprecated (since := "2025-02-01")] alias nonsingular_neg_of := nonsingular_neg
@[deprecated (since := "2025-02-01")] alias nonsingular_neg_iff := nonsingular_neg

end Negation

section Slope

/-! ### Slope formulae -/

variable (W') in
/-- The polynomial `ℓ(X - x) + y` associated to the line `Y = ℓ(X - x) + y`, with a slope of `ℓ`
that passes through an affine point `(x, y)`.

This does not depend on `W`, and has argument order: `x`, `y`, `ℓ`. -/
noncomputable def linePolynomial (x y ℓ : R) : R[X] :=
  C ℓ * (X - C x) + C y

open scoped Classical in
variable (W) in
/-- The slope of the line through two affine points `(x₁, y₁)` and `(x₂, y₂)` in `W`. If `x₁ ≠ x₂`,
then this line is the secant of `W` through `(x₁, y₁)` and `(x₂, y₂)`, and has slope
`(y₁ - y₂) / (x₁ - x₂)`. Otherwise, if `y₁ ≠ -y₁ - a₁x₁ - a₃`, then this line is the tangent of `W`
at `(x₁, y₁) = (x₂, y₂)`, and has slope `(3x₁² + 2a₂x₁ + a₄ - a₁y₁) / (2y₁ + a₁x₁ + a₃)`.
Otherwise, this line is vertical, in which case this function returns the value `0`.

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

lemma slope_of_Y_ne_eq_eval {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) :
    W.slope x₁ x₂ y₁ y₂ = -W.polynomialX.evalEval x₁ y₁ / W.polynomialY.evalEval x₁ y₁ := by
  rw [slope_of_Y_ne hx hy, evalEval_polynomialX, neg_sub]
  congr 1
  rw [negY, evalEval_polynomialY]
  ring1

end Slope

section Addition

/-! ### Addition formulae -/

variable (W') in
/-- The polynomial obtained by substituting the line `Y = ℓ*(X - x) + y`, with a slope of `ℓ` that
passes through an affine point `(x, y)`, into the polynomial `W(X, Y)` associated to `W`. If such a
line intersects `W` at another point `(x', y')`, then the roots of this polynomial are precisely
`x`, `x'`, and the `X`-coordinate of the addition of `(x, y)` and `(x', y')`.

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
/-- The `X`-coordinate of the addition of two affine points `(x₁, y₁)` and `(x₂, y₂)` in `W`, where
the line through them is not vertical and has a slope of `ℓ`.

This depends on `W`, and has argument order: `x₁`, `x₂`, `ℓ`. -/
@[simp]
def addX (x₁ x₂ ℓ : R) : R :=
  ℓ ^ 2 + W'.a₁ * ℓ - W'.a₂ - x₁ - x₂

variable (W') in
/-- The `Y`-coordinate of the negated addition of two affine points `(x₁, y₁)` and `(x₂, y₂)`, where
the line through them is not vertical and has a slope of `ℓ`.

This depends on `W`, and has argument order: `x₁`, `x₂`, `y₁`, `ℓ`. -/
@[simp]
def negAddY (x₁ x₂ y₁ ℓ : R) : R :=
  ℓ * (W'.addX x₁ x₂ ℓ - x₁) + y₁

variable (W') in
/-- The `Y`-coordinate of the addition of two affine points `(x₁, y₁)` and `(x₂, y₂)` in `W`, where
the line through them is not vertical and has a slope of `ℓ`.

This depends on `W`, and has argument order: `x₁`, `x₂`, `y₁`, `ℓ`. -/
@[simp]
def addY (x₁ x₂ y₁ ℓ : R) : R :=
  W'.negY (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ)

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

lemma equation_add_iff (x₁ x₂ y₁ ℓ : R) : W'.Equation (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ) ↔
    (W'.addPolynomial x₁ y₁ ℓ).eval (W'.addX x₁ x₂ ℓ) = 0 := by
  rw [Equation, negAddY, addPolynomial, linePolynomial, polynomial]
  eval_simp

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

end Addition

section Map

/-! ### Maps and base changes -/

variable (f : R →+* S) (x y x₁ y₁ x₂ y₂ ℓ : R)

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

lemma baseChange_slope [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] (f : F →ₐ[S] K) (x₁ x₂ y₁ y₂ : F) :
  (W'.baseChange K).toAffine.slope (f x₁) (f x₂) (f y₁) (f y₂) =
    f ((W'.baseChange F).toAffine.slope x₁ x₂ y₁ y₂) := by
  rw [← RingHom.coe_coe, ← map_slope, map_baseChange]

end Map

end WeierstrassCurve.Affine
