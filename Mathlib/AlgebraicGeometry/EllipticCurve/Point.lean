/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.RingTheory.ClassGroup

#align_import algebraic_geometry.elliptic_curve.point from "leanprover-community/mathlib"@"e2e7f2ac359e7514e4d40061d7c08bb69487ba4e"

/-!
# Nonsingular rational points on Weierstrass curves

This file defines the type of nonsingular rational points on a Weierstrass curve over a field and
proves that it forms an abelian group under a geometric secant-and-tangent process.

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

 * `WeierstrassCurve.Point`: the type of nonsingular rational points on a Weierstrass curve `W`.
 * `WeierstrassCurve.Point.add`: the addition of two nonsingular rational points on `W`.

## Main statements

 * `WeierstrassCurve.Point.instAddCommGroupPoint`: the type of nonsingular rational points on `W`
    forms an abelian group under addition.

## Notations

 * `W⟮K⟯`: the group of nonsingular rational points on `W` base changed to `K`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, group law
-/

-- porting note: replaced `map_one`, `map_bit0`, and `map_bit1` with `map_ofNat`
local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀])

universe u v w

namespace WeierstrassCurve

open CoordinateRing Ideal Polynomial

-- porting note: relocated into `Polynomial` section
local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow])

-- porting note: relocated into `Polynomial` section
local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

-- porting note: relocated into `Polynomial` section
local macro "derivative_simp" : tactic =>
  `(tactic| simp only [derivative_C, derivative_X, derivative_X_pow, derivative_neg, derivative_add,
              derivative_sub, derivative_mul, derivative_sq])

open scoped nonZeroDivisors Polynomial PolynomialPolynomial

section Basic

/-! ### Polynomials associated to nonsingular rational points on a Weierstrass curve -/

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (A : Type v) [CommRing A] [Algebra R A]
  (B : Type w) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] (x₁ x₂ y₁ y₂ L : R)

/-- The polynomial $-Y - a_1X - a_3$ associated to negation. -/
noncomputable def negPolynomial : R[X][Y] :=
  -Y - C (C W.a₁ * X + C W.a₃)
#align weierstrass_curve.neg_polynomial WeierstrassCurve.negPolynomial

/-- The $Y$-coordinate of the negation of an affine point in `W`.

This depends on `W`, and has argument order: $x_1$, $y_1$. -/
@[simp]
def negY : R :=
  -y₁ - W.a₁ * x₁ - W.a₃
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.neg_Y WeierstrassCurve.negY

lemma negY_negY : W.negY x₁ (W.negY x₁ y₁) = y₁ := by
  simp only [negY]
  ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.neg_Y_neg_Y WeierstrassCurve.negY_negY

lemma baseChange_negY :
    (W.baseChange A).negY (algebraMap R A x₁) (algebraMap R A y₁) =
      algebraMap R A (W.negY x₁ y₁) := by
  simp only [negY]
  map_simp
  rfl
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.base_change_neg_Y WeierstrassCurve.baseChange_negY

lemma baseChange_negY_of_baseChange (x₁ y₁ : A) :
    (W.baseChange B).negY (algebraMap A B x₁) (algebraMap A B y₁) =
      algebraMap A B ((W.baseChange A).negY x₁ y₁) := by
  rw [← baseChange_negY, baseChange_baseChange]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.base_change_neg_Y_of_base_change WeierstrassCurve.baseChange_negY_of_baseChange

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
lemma eval_negPolynomial : (W.negPolynomial.eval <| C y₁).eval x₁ = W.negY x₁ y₁ := by
  rw [negY, sub_sub, negPolynomial]
  eval_simp
#align weierstrass_curve.eval_neg_polynomial WeierstrassCurve.eval_negPolynomial

/-- The polynomial $L(X - x_1) + y_1$ associated to the line $Y = L(X - x_1) + y_1$,
with a slope of $L$ that passes through an affine point $(x_1, y_1)$.

This does not depend on `W`, and has argument order: $x_1$, $y_1$, $L$. -/
noncomputable def linePolynomial : R[X] :=
  C L * (X - C x₁) + C y₁
#align weierstrass_curve.line_polynomial WeierstrassCurve.linePolynomial

lemma XYIdeal_eq₁ : XYIdeal W x₁ (C y₁) = XYIdeal W x₁ (linePolynomial x₁ y₁ L) := by
  simp only [XYIdeal, XClass, YClass, linePolynomial]
  rw [← span_pair_add_mul_right <| CoordinateRing.mk W <| C <| C <| -L, ← _root_.map_mul, ← map_add]
  apply congr_arg (_ ∘ _ ∘ _ ∘ _)
  C_simp
  ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal_eq₁ WeierstrassCurve.XYIdeal_eq₁

/-- The polynomial obtained by substituting the line $Y = L*(X - x_1) + y_1$, with a slope of $L$
that passes through an affine point $(x_1, y_1)$, into the polynomial $W(X, Y)$ associated to `W`.
If such a line intersects `W` at another point $(x_2, y_2)$, then the roots of this polynomial are
precisely $x_1$, $x_2$, and the $X$-coordinate of the addition of $(x_1, y_1)$ and $(x_2, y_2)$.

This depends on `W`, and has argument order: $x_1$, $y_1$, $L$. -/
noncomputable def addPolynomial : R[X] :=
  W.polynomial.eval <| linePolynomial x₁ y₁ L
#align weierstrass_curve.add_polynomial WeierstrassCurve.addPolynomial

lemma C_addPolynomial :
    C (W.addPolynomial x₁ y₁ L) =
      (Y - C (linePolynomial x₁ y₁ L)) * (W.negPolynomial - C (linePolynomial x₁ y₁ L)) +
        W.polynomial := by
  rw [addPolynomial, linePolynomial, WeierstrassCurve.polynomial, negPolynomial]
  eval_simp
  C_simp
  ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.C_add_polynomial WeierstrassCurve.C_addPolynomial

lemma CoordinateRing.C_addPolynomial :
    CoordinateRing.mk W (C (W.addPolynomial x₁ y₁ L)) =
      CoordinateRing.mk W
        ((Y - C (linePolynomial x₁ y₁ L)) * (W.negPolynomial - C (linePolynomial x₁ y₁ L))) :=
  AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [W.C_addPolynomial, add_sub_cancel', mul_one]⟩
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.C_add_polynomial WeierstrassCurve.CoordinateRing.C_addPolynomial

lemma addPolynomial_eq :
    W.addPolynomial x₁ y₁ L =
      -Cubic.toPoly
        ⟨1, -L ^ 2 - W.a₁ * L + W.a₂,
          2 * x₁ * L ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * L + (-W.a₁ * y₁ + W.a₄),
          -x₁ ^ 2 * L ^ 2 + (2 * x₁ * y₁ + W.a₃ * x₁) * L - (y₁ ^ 2 + W.a₃ * y₁ - W.a₆)⟩ := by
  rw [addPolynomial, linePolynomial, WeierstrassCurve.polynomial, Cubic.toPoly]
  eval_simp
  C_simp
  ring1
#align weierstrass_curve.add_polynomial_eq WeierstrassCurve.addPolynomial_eq

/-- The $X$-coordinate of the addition of two affine points $(x_1, y_1)$ and $(x_2, y_2)$ in `W`,
where the line through them is not vertical and has a slope of $L$.

This depends on `W`, and has argument order: $x_1$, $x_2$, $L$. -/
@[simp]
def addX : R :=
  L ^ 2 + W.a₁ * L - W.a₂ - x₁ - x₂
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.add_X WeierstrassCurve.addX

lemma baseChange_addX :
    (W.baseChange A).addX (algebraMap R A x₁) (algebraMap R A x₂) (algebraMap R A L) =
      algebraMap R A (W.addX x₁ x₂ L) := by
  simp only [addX]
  map_simp
  rfl
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.base_change_add_X WeierstrassCurve.baseChange_addX

lemma baseChange_addX_of_baseChange (x₁ x₂ L : A) :
    (W.baseChange B).addX (algebraMap A B x₁) (algebraMap A B x₂) (algebraMap A B L) =
      algebraMap A B ((W.baseChange A).addX x₁ x₂ L) := by
  rw [← baseChange_addX, baseChange_baseChange]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.base_change_add_X_of_base_change WeierstrassCurve.baseChange_addX_of_baseChange

/-- The $Y$-coordinate, before applying the final negation, of the addition of two affine points
$(x_1, y_1)$ and $(x_2, y_2)$, where the line through them is not vertical and has a slope of $L$.

This depends on `W`, and has argument order: $x_1$, $x_2$, $y_1$, $L$. -/
@[simp]
def addY' : R :=
  L * (W.addX x₁ x₂ L - x₁) + y₁
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.add_Y' WeierstrassCurve.addY'

lemma baseChange_addY' :
    (W.baseChange A).addY' (algebraMap R A x₁) (algebraMap R A x₂) (algebraMap R A y₁)
        (algebraMap R A L) =
      algebraMap R A (W.addY' x₁ x₂ y₁ L) := by
  simp only [addY', baseChange_addX]
  map_simp
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.base_change_add_Y' WeierstrassCurve.baseChange_addY'

lemma baseChange_addY'_of_baseChange (x₁ x₂ y₁ L : A) :
    (W.baseChange B).addY' (algebraMap A B x₁) (algebraMap A B x₂) (algebraMap A B y₁)
        (algebraMap A B L) =
      algebraMap A B ((W.baseChange A).addY' x₁ x₂ y₁ L) := by
  rw [← baseChange_addY', baseChange_baseChange]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.base_change_add_Y'_of_base_change WeierstrassCurve.baseChange_addY'_of_baseChange

/-- The $Y$-coordinate of the addition of two affine points $(x_1, y_1)$ and $(x_2, y_2)$ in `W`,
where the line through them is not vertical and has a slope of $L$.

This depends on `W`, and has argument order: $x_1$, $x_2$, $y_1$, $L$. -/
@[simp]
def addY : R :=
  W.negY (W.addX x₁ x₂ L) (W.addY' x₁ x₂ y₁ L)
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.add_Y WeierstrassCurve.addY

lemma baseChange_addY :
    (W.baseChange A).addY (algebraMap R A x₁) (algebraMap R A x₂) (algebraMap R A y₁)
        (algebraMap R A L) =
      algebraMap R A (W.addY x₁ x₂ y₁ L) := by
  simp only [addY, baseChange_addY', baseChange_addX, baseChange_negY]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.base_change_add_Y WeierstrassCurve.baseChange_addY

lemma baseChange_addY_of_baseChange (x₁ x₂ y₁ L : A) :
    (W.baseChange B).addY (algebraMap A B x₁) (algebraMap A B x₂) (algebraMap A B y₁)
        (algebraMap A B L) =
      algebraMap A B ((W.baseChange A).addY x₁ x₂ y₁ L) := by
  rw [← baseChange_addY, baseChange_baseChange]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.base_change_add_Y_of_base_change WeierstrassCurve.baseChange_addY_of_baseChange

lemma XYIdeal_add_eq :
    XYIdeal W (W.addX x₁ x₂ L) (C (W.addY x₁ x₂ y₁ L)) =
      span {CoordinateRing.mk W <| W.negPolynomial - C (linePolynomial x₁ y₁ L)} ⊔
        XIdeal W (W.addX x₁ x₂ L) := by
  simp only [XYIdeal, XIdeal, XClass, YClass, addY, addY', negY, negPolynomial, linePolynomial]
  rw [sub_sub <| -Y, neg_sub_left Y, map_neg, span_singleton_neg, sup_comm, ← span_insert,
    ← span_pair_add_mul_right <| CoordinateRing.mk W <| C <| C <| W.a₁ + L, ← _root_.map_mul,
    ← map_add]
  apply congr_arg (_ ∘ _ ∘ _ ∘ _)
  C_simp
  ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal_add_eq WeierstrassCurve.XYIdeal_add_eq

lemma equation_add_iff :
    W.equation (W.addX x₁ x₂ L) (W.addY' x₁ x₂ y₁ L) ↔
      (W.addPolynomial x₁ y₁ L).eval (W.addX x₁ x₂ L) = 0 := by
  rw [WeierstrassCurve.equation, addY', addPolynomial, linePolynomial, WeierstrassCurve.polynomial]
  eval_simp
#align weierstrass_curve.equation_add_iff WeierstrassCurve.equation_add_iff

lemma nonsingular_add_of_eval_derivative_ne_zero
    (hx' : W.equation (W.addX x₁ x₂ L) (W.addY' x₁ x₂ y₁ L))
    (hx : (derivative <| W.addPolynomial x₁ y₁ L).eval (W.addX x₁ x₂ L) ≠ 0) :
    W.nonsingular (W.addX x₁ x₂ L) (W.addY' x₁ x₂ y₁ L) := by
  rw [WeierstrassCurve.nonsingular, and_iff_right hx', addY', WeierstrassCurve.polynomialX,
    WeierstrassCurve.polynomialY]
  eval_simp
  contrapose! hx
  rw [addPolynomial, linePolynomial, WeierstrassCurve.polynomial]
  eval_simp
  derivative_simp
  simp only [zero_add, add_zero, sub_zero, zero_mul, mul_one]
  eval_simp
  linear_combination (norm := (norm_num1; ring1)) hx.left + L * hx.right
#align weierstrass_curve.nonsingular_add_of_eval_derivative_ne_zero WeierstrassCurve.nonsingular_add_of_eval_derivative_ne_zero

/-! ### The type of nonsingular rational points on a Weierstrass curve -/

/-- A nonsingular rational point on a Weierstrass curve `W` over `R`. This is either the point at
infinity `WeierstrassCurve.Point.zero` or an affine point `WeierstrassCurve.Point.some` $(x, y)$
satisfying the equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$ of `W`. -/
inductive Point
  | zero
  | some {x y : R} (h : W.nonsingular x y)
#align weierstrass_curve.point WeierstrassCurve.Point

/-- For an algebraic extension `S` of `R`, The type of nonsingular `S`-rational points on `W`. -/
scoped[WeierstrassCurve] notation W "⟮" S "⟯" => Point (baseChange W S)

namespace Point

instance : Inhabited W.Point :=
  ⟨zero⟩

instance : Zero W.Point :=
  ⟨zero⟩

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
lemma zero_def : (zero : W.Point) = 0 :=
  rfl
#align weierstrass_curve.point.zero_def WeierstrassCurve.Point.zero_def

end Point

variable {W x₁ y₁}

lemma equation_neg_iff : W.equation x₁ (W.negY x₁ y₁) ↔ W.equation x₁ y₁ := by
  rw [equation_iff, equation_iff, negY]
  congr! 1
  ring1
#align weierstrass_curve.equation_neg_iff WeierstrassCurve.equation_neg_iff

lemma equation_neg_of (h : W.equation x₁ <| W.negY x₁ y₁) : W.equation x₁ y₁ :=
  equation_neg_iff.mp h
#align weierstrass_curve.equation_neg_of WeierstrassCurve.equation_neg_of

/-- The negation of an affine point in `W` lies in `W`. -/
lemma equation_neg (h : W.equation x₁ y₁) : W.equation x₁ <| W.negY x₁ y₁ :=
  equation_neg_iff.mpr h
#align weierstrass_curve.equation_neg WeierstrassCurve.equation_neg

lemma nonsingular_neg_iff : W.nonsingular x₁ (W.negY x₁ y₁) ↔ W.nonsingular x₁ y₁ := by
  rw [nonsingular_iff, equation_neg_iff, ← negY, negY_negY, ← @ne_comm _ y₁, nonsingular_iff]
  exact and_congr_right' <| (iff_congr not_and_or.symm not_and_or.symm).mpr <|
    not_congr <| and_congr_left fun h => by rw [← h]
#align weierstrass_curve.nonsingular_neg_iff WeierstrassCurve.nonsingular_neg_iff

lemma nonsingular_neg_of (h : W.nonsingular x₁ <| W.negY x₁ y₁) : W.nonsingular x₁ y₁ :=
  nonsingular_neg_iff.mp h
#align weierstrass_curve.nonsingular_neg_of WeierstrassCurve.nonsingular_neg_of

/-- The negation of a nonsingular affine point in `W` is nonsingular. -/
lemma nonsingular_neg (h : W.nonsingular x₁ y₁) : W.nonsingular x₁ <| W.negY x₁ y₁ :=
  nonsingular_neg_iff.mpr h
#align weierstrass_curve.nonsingular_neg WeierstrassCurve.nonsingular_neg

namespace Point

/-- The negation of a nonsingular rational point.

Given a nonsingular rational point `P`, use `-P` instead of `neg P`. -/
def neg : W.Point → W.Point
  | 0 => 0
  | some h => some <| nonsingular_neg h
#align weierstrass_curve.point.neg WeierstrassCurve.Point.neg

instance : Neg W.Point :=
  ⟨neg⟩

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
lemma neg_def (P : W.Point) : P.neg = -P :=
  rfl
#align weierstrass_curve.point.neg_def WeierstrassCurve.Point.neg_def

@[simp]
lemma neg_zero : (-0 : W.Point) = 0 :=
  rfl
#align weierstrass_curve.point.neg_zero WeierstrassCurve.Point.neg_zero

@[simp]
lemma neg_some (h : W.nonsingular x₁ y₁) : -some h = some (nonsingular_neg h) :=
  rfl
#align weierstrass_curve.point.neg_some WeierstrassCurve.Point.neg_some

instance : InvolutiveNeg W.Point :=
  ⟨by rintro (_ | _) <;> simp [zero_def]; ring1⟩

end Point

end Basic

section Addition

/-! ### Slopes of lines through nonsingular rational points on a Weierstrass curve -/

open scoped Classical

variable {F : Type u} [Field F] (W : WeierstrassCurve F) (K : Type v) [Field K] [Algebra F K]
  (x₁ x₂ y₁ y₂ : F)

/-- The slope of the line through two affine points $(x_1, y_1)$ and $(x_2, y_2)$ in `W`.
If $x_1 \ne x_2$, then this line is the secant of `W` through $(x_1, y_1)$ and $(x_2, y_2)$,
and has slope $(y_1 - y_2) / (x_1 - x_2)$. Otherwise, if $y_1 \ne -y_1 - a_1x_1 - a_3$,
then this line is the tangent of `W` at $(x_1, y_1) = (x_2, y_2)$, and has slope
$(3x_1^2 + 2a_2x_1 + a_4 - a_1y_1) / (2y_1 + a_1x_1 + a_3)$. Otherwise, this line is vertical,
and has undefined slope, in which case this function returns the value 0.

This depends on `W`, and has argument order: $x_1$, $x_2$, $y_1$, $y_2$. -/
noncomputable def slope : F :=
  if x₁ = x₂ then
    if y₁ = W.negY x₂ y₂ then 0
    else (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.negY x₁ y₁)
  else (y₁ - y₂) / (x₁ - x₂)
#align weierstrass_curve.slope WeierstrassCurve.slope

variable {W x₁ x₂ y₁ y₂} (h₁ : W.nonsingular x₁ y₁) (h₂ : W.nonsingular x₂ y₂)
  (h₁' : W.equation x₁ y₁) (h₂' : W.equation x₂ y₂)

@[simp]
lemma slope_of_Y_eq (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂) : W.slope x₁ x₂ y₁ y₂ = 0 := by
  rw [slope, if_pos hx, if_pos hy]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.slope_of_Y_eq WeierstrassCurve.slope_of_Y_eq

@[simp]
lemma slope_of_Y_ne (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) :
    W.slope x₁ x₂ y₁ y₂ =
      (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.negY x₁ y₁) := by
  rw [slope, if_pos hx, if_neg hy]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.slope_of_Y_ne WeierstrassCurve.slope_of_Y_ne

@[simp]
lemma slope_of_X_ne (hx : x₁ ≠ x₂) : W.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) := by
  rw [slope, if_neg hx]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.slope_of_X_ne WeierstrassCurve.slope_of_X_ne

lemma slope_of_Y_ne_eq_eval (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) :
    W.slope x₁ x₂ y₁ y₂ =
      -(W.polynomialX.eval <| C y₁).eval x₁ / (W.polynomialY.eval <| C y₁).eval x₁ := by
  rw [slope_of_Y_ne hx hy, eval_polynomialX, neg_sub]
  congr 1
  rw [negY, eval_polynomialY]
  ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.slope_of_Y_ne_eq_eval WeierstrassCurve.slope_of_Y_ne_eq_eval

lemma baseChange_slope :
    (W.baseChange K).slope (algebraMap F K x₁) (algebraMap F K x₂) (algebraMap F K y₁)
        (algebraMap F K y₂) =
      algebraMap F K (W.slope x₁ x₂ y₁ y₂) := by
  by_cases hx : x₁ = x₂
  · by_cases hy : y₁ = W.negY x₂ y₂
    · rw [slope_of_Y_eq hx hy, slope_of_Y_eq <| congr_arg _ hx, map_zero]
      · rw [hy, baseChange_negY]
    · rw [slope_of_Y_ne hx hy, slope_of_Y_ne <| congr_arg _ hx]
      · map_simp
        simp only [baseChange_negY]
        rfl
      · rw [baseChange_negY]
        contrapose! hy
        exact NoZeroSMulDivisors.algebraMap_injective F K hy
  · rw [slope_of_X_ne hx, slope_of_X_ne]
    · map_simp
    · contrapose! hx
      exact NoZeroSMulDivisors.algebraMap_injective F K hx
#align weierstrass_curve.base_change_slope WeierstrassCurve.baseChange_slope

lemma baseChange_slope_of_baseChange {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type v) [Field F] [Algebra R F] (K : Type w) [Field K] [Algebra R K] [Algebra F K]
    [IsScalarTower R F K] (x₁ x₂ y₁ y₂ : F) :
    (W.baseChange K).slope (algebraMap F K x₁) (algebraMap F K x₂) (algebraMap F K y₁)
        (algebraMap F K y₂) =
      algebraMap F K ((W.baseChange F).slope x₁ x₂ y₁ y₂) := by
  rw [← baseChange_slope, baseChange_baseChange]
#align weierstrass_curve.base_change_slope_of_base_change WeierstrassCurve.baseChange_slope_of_baseChange

lemma Y_eq_of_X_eq (hx : x₁ = x₂) : y₁ = y₂ ∨ y₁ = W.negY x₂ y₂ := by
  rw [equation_iff] at h₁' h₂'
  rw [← sub_eq_zero, ← @sub_eq_zero _ _ y₁, ← mul_eq_zero, negY]
  linear_combination (norm := (rw [hx]; ring1)) h₁' - h₂'
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.Y_eq_of_X_eq WeierstrassCurve.Y_eq_of_X_eq

lemma Y_eq_of_Y_ne (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) : y₁ = y₂ :=
  Or.resolve_right (Y_eq_of_X_eq h₁' h₂' hx) hy
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.Y_eq_of_Y_ne WeierstrassCurve.Y_eq_of_Y_ne

-- porting note: increased `maxHeartbeats` for `ring1`
set_option synthInstance.maxHeartbeats 30000 in
lemma XYIdeal_eq₂ (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    XYIdeal W x₂ (C y₂) = XYIdeal W x₂ (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  -- porting note: removed assumption `h₂` explicitly
  clear h₂
  have hy₂ : y₂ = (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂).eval x₂ := by
    by_cases hx : x₁ = x₂
    · rcases hx, Y_eq_of_Y_ne h₁' h₂' hx <| hxy hx with ⟨rfl, rfl⟩
      field_simp [linePolynomial, sub_ne_zero_of_ne (hxy rfl)]
    · field_simp [linePolynomial, slope_of_X_ne hx, sub_ne_zero_of_ne hx]
      ring1
  nth_rw 1 [hy₂]
  simp only [XYIdeal, XClass, YClass, linePolynomial]
  rw [← span_pair_add_mul_right <| CoordinateRing.mk W <| C <| C <| -W.slope x₁ x₂ y₁ y₂,
    ← _root_.map_mul, ← map_add]
  apply congr_arg (_ ∘ _ ∘ _ ∘ _)
  eval_simp
  C_simp
  ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal_eq₂ WeierstrassCurve.XYIdeal_eq₂

lemma addPolynomial_slope (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    W.addPolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂) =
      -((X - C x₁) * (X - C x₂) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂))) := by
  -- porting note: removed assumption `h₂` explicitly
  clear h₂
  rw [addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective]
  by_cases hx : x₁ = x₂
  · rcases hx, Y_eq_of_Y_ne h₁' h₂' hx (hxy hx) with ⟨rfl, rfl⟩
    rw [equation_iff] at h₁' h₂'
    rw [slope_of_Y_ne rfl <| hxy rfl]
    rw [negY, ← sub_ne_zero] at hxy
    ext
    · rfl
    · simp only [addX]
      ring1
    · field_simp [hxy rfl]
      ring1
    · linear_combination (norm := (field_simp [hxy rfl]; ring1)) -h₁'
  · rw [equation_iff] at h₁' h₂'
    rw [slope_of_X_ne hx]
    rw [← sub_eq_zero] at hx
    ext
    · rfl
    · simp only [addX]
      ring1
    · apply mul_right_injective₀ hx
      linear_combination (norm := (field_simp [hx]; ring1)) h₂' - h₁'
    · apply mul_right_injective₀ hx
      linear_combination (norm := (field_simp [hx]; ring1)) x₂ * h₁' - x₁ * h₂'
#align weierstrass_curve.add_polynomial_slope WeierstrassCurve.addPolynomial_slope

lemma CoordinateRing.C_addPolynomial_slope (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    CoordinateRing.mk W (C <| W.addPolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) =
      -(XClass W x₁ * XClass W x₂ * XClass W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)) := by
  simp only [addPolynomial_slope h₁' h₂' hxy, C_neg, mk, map_neg, neg_inj, _root_.map_mul]
  rfl
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.C_add_polynomial_slope WeierstrassCurve.CoordinateRing.C_addPolynomial_slope

lemma derivative_addPolynomial_slope (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    derivative (W.addPolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) =
      -((X - C x₁) * (X - C x₂) + (X - C x₁) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)) +
          (X - C x₂) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂))) := by
  rw [addPolynomial_slope h₁' h₂' hxy]
  derivative_simp
  ring1
#align weierstrass_curve.derivative_add_polynomial_slope WeierstrassCurve.derivative_addPolynomial_slope

/-! ### The addition law on nonsingular rational points on a Weierstrass curve -/

/-- The addition of two affine points in `W` on a sloped line,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$, lies in `W`. -/
lemma equation_add' (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    W.equation (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.addY' x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  rw [equation_add_iff, addPolynomial_slope h₁' h₂' hxy]
  eval_simp
  rw [neg_eq_zero, sub_self, mul_zero]
#align weierstrass_curve.equation_add' WeierstrassCurve.equation_add'

/-- The addition of two affine points in `W` on a sloped line lies in `W`. -/
lemma equation_add (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    W.equation (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) :=
  equation_neg <| equation_add' h₁' h₂' hxy
#align weierstrass_curve.equation_add WeierstrassCurve.equation_add

/-- The addition of two nonsingular affine points in `W` on a sloped line,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$, is nonsingular. -/
lemma nonsingular_add' (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    W.nonsingular (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)
      (W.addY' x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  -- porting note: removed assumption `h₂'` explicitly
  clear h₂'
  by_cases hx₁ : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₁
  · rwa [addY', hx₁, sub_self, mul_zero, zero_add]
  · by_cases hx₂ : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₂
    · by_cases hx : x₁ = x₂
      · subst hx
        contradiction
      · rwa [addY', ← neg_sub, mul_neg, hx₂, slope_of_X_ne hx,
          div_mul_cancel _ <| sub_ne_zero_of_ne hx, neg_sub, sub_add_cancel]
    · apply W.nonsingular_add_of_eval_derivative_ne_zero _ _ _ _ (equation_add' h₁.1 h₂.1 hxy)
      rw [derivative_addPolynomial_slope h₁.left h₂.left hxy]
      eval_simp
      simpa only [neg_ne_zero, sub_self, mul_zero, add_zero] using
        mul_ne_zero (sub_ne_zero_of_ne hx₁) (sub_ne_zero_of_ne hx₂)
#align weierstrass_curve.nonsingular_add' WeierstrassCurve.nonsingular_add'

/-- The addition of two nonsingular affine points in `W` on a sloped line is nonsingular. -/
lemma nonsingular_add (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    W.nonsingular (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) :=
  nonsingular_neg <| nonsingular_add' h₁ h₂ hxy
#align weierstrass_curve.nonsingular_add WeierstrassCurve.nonsingular_add

namespace Point

variable {h₁ h₂}

/-- The addition of two nonsingular rational points.

Given two nonsingular rational points `P` and `Q`, use `P + Q` instead of `add P Q`. -/
noncomputable def add : W.Point → W.Point → W.Point
  | 0, P => P
  | P, 0 => P
  | @some _ _ _ x₁ y₁ h₁, @some _ _ _ x₂ y₂ h₂ =>
    if hx : x₁ = x₂ then
      if hy : y₁ = W.negY x₂ y₂ then 0 else some <| nonsingular_add h₁ h₂ fun _ => hy
    else some <| nonsingular_add h₁ h₂ fun h => (hx h).elim
#align weierstrass_curve.point.add WeierstrassCurve.Point.add

noncomputable instance instAddPoint : Add W.Point :=
  ⟨add⟩

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
lemma add_def (P Q : W.Point) : P.add Q = P + Q :=
  rfl
#align weierstrass_curve.point.add_def WeierstrassCurve.Point.add_def

noncomputable instance instAddZeroClassPoint : AddZeroClass W.Point :=
  ⟨by rintro (_ | _) <;> rfl, by rintro (_ | _) <;> rfl⟩

@[simp]
lemma some_add_some_of_Y_eq (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂) : some h₁ + some h₂ = 0 := by
  simp only [← add_def, add, dif_pos hx, dif_pos hy]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.point.some_add_some_of_Y_eq WeierstrassCurve.Point.some_add_some_of_Y_eq

@[simp]
lemma some_add_self_of_Y_eq (hy : y₁ = W.negY x₁ y₁) : some h₁ + some h₁ = 0 :=
  some_add_some_of_Y_eq rfl hy
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.point.some_add_self_of_Y_eq WeierstrassCurve.Point.some_add_self_of_Y_eq

@[simp]
lemma some_add_some_of_Y_ne (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) :
    some h₁ + some h₂ = some (nonsingular_add h₁ h₂ fun _ => hy) := by
  simp only [← add_def, add, dif_pos hx, dif_neg hy]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.point.some_add_some_of_Y_ne WeierstrassCurve.Point.some_add_some_of_Y_ne

lemma some_add_some_of_Y_ne' (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) :
    some h₁ + some h₂ = -some (nonsingular_add' h₁ h₂ fun _ => hy) :=
  some_add_some_of_Y_ne hx hy
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.point.some_add_some_of_Y_ne' WeierstrassCurve.Point.some_add_some_of_Y_ne'

@[simp]
lemma some_add_self_of_Y_ne (hy : y₁ ≠ W.negY x₁ y₁) :
    some h₁ + some h₁ = some (nonsingular_add h₁ h₁ fun _ => hy) :=
  some_add_some_of_Y_ne rfl hy
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.point.some_add_self_of_Y_ne WeierstrassCurve.Point.some_add_self_of_Y_ne

lemma some_add_self_of_Y_ne' (hy : y₁ ≠ W.negY x₁ y₁) :
    some h₁ + some h₁ = -some (nonsingular_add' h₁ h₁ fun _ => hy) :=
  some_add_some_of_Y_ne rfl hy
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.point.some_add_self_of_Y_ne' WeierstrassCurve.Point.some_add_self_of_Y_ne'

@[simp]
lemma some_add_some_of_X_ne (hx : x₁ ≠ x₂) :
    some h₁ + some h₂ = some (nonsingular_add h₁ h₂ fun h => (hx h).elim) := by
  simp only [← add_def, add, dif_neg hx]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.point.some_add_some_of_X_ne WeierstrassCurve.Point.some_add_some_of_X_ne

lemma some_add_some_of_X_ne' (hx : x₁ ≠ x₂) :
    some h₁ + some h₂ = -some (nonsingular_add' h₁ h₂ fun h => (hx h).elim) :=
  some_add_some_of_X_ne hx
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.point.some_add_some_of_X_ne' WeierstrassCurve.Point.some_add_some_of_X_ne'

end Point

end Addition

section Group

/-! ### The axioms for nonsingular rational points on a Weierstrass curve -/

variable {F : Type u} [Field F] {W : WeierstrassCurve F} {x₁ x₂ y₁ y₂ : F}
  (h₁ : W.nonsingular x₁ y₁) (h₂ : W.nonsingular x₂ y₂) (h₁' : W.equation x₁ y₁)
  (h₂' : W.equation x₂ y₂)

-- porting note: increased `maxHeartbeats` for `ring1`
set_option maxHeartbeats 800000 in
lemma XYIdeal_neg_mul : XYIdeal W x₁ (C <| W.negY x₁ y₁) * XYIdeal W x₁ (C y₁) = XIdeal W x₁ := by
  have Y_rw :
    (Y - C (C y₁)) * (Y - C (C (W.negY x₁ y₁))) -
        C (X - C x₁) *
          (C (X ^ 2 + C (x₁ + W.a₂) * X + C (x₁ ^ 2 + W.a₂ * x₁ + W.a₄)) - C (C W.a₁) * Y) =
      W.polynomial * 1 := by
    linear_combination (norm := (rw [negY, WeierstrassCurve.polynomial]; C_simp; ring1))
      congr_arg C (congr_arg C ((W.equation_iff _ _).mp h₁.left).symm)
  simp_rw [XYIdeal, XClass, YClass, span_pair_mul_span_pair, mul_comm, ← _root_.map_mul,
    AdjoinRoot.mk_eq_mk.mpr ⟨1, Y_rw⟩, _root_.map_mul, span_insert,
    ← span_singleton_mul_span_singleton, ← mul_sup, ← span_insert]
  convert mul_top (_ : Ideal W.CoordinateRing) using 2
  simp_rw [← @Set.image_singleton _ _ <| CoordinateRing.mk W, ← Set.image_insert_eq, ← map_span]
  convert map_top (R := F[X][Y]) (CoordinateRing.mk W) using 1
  apply congr_arg
  simp_rw [eq_top_iff_one, mem_span_insert', mem_span_singleton']
  rcases ((W.nonsingular_iff' _ _).mp h₁).right with hx | hy
  · let W_X := W.a₁ * y₁ - (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄)
    refine
      ⟨C (C W_X⁻¹ * -(X + C (2 * x₁ + W.a₂))), C (C <| W_X⁻¹ * W.a₁), 0, C (C <| W_X⁻¹ * -1), ?_⟩
    rw [← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hx]
    simp only [mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel hx]
    C_simp
    ring1
  · let W_Y := 2 * y₁ + W.a₁ * x₁ + W.a₃
    refine ⟨0, C (C W_Y⁻¹), C (C <| W_Y⁻¹ * -1), 0, ?_⟩
    rw [negY, ← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hy]
    simp only [mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel hy]
    C_simp
    ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal_neg_mul WeierstrassCurve.XYIdeal_neg_mul

private lemma XYIdeal'_mul_inv :
    XYIdeal W x₁ (C y₁) *
        (XYIdeal W x₁ (C <| W.negY x₁ y₁) *
          (XIdeal W x₁ : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)⁻¹) =
      1 := by
  rw [← mul_assoc, ← FractionalIdeal.coeIdeal_mul, mul_comm <| XYIdeal W _ _, XYIdeal_neg_mul h₁,
    XIdeal, FractionalIdeal.coe_ideal_span_singleton_mul_inv W.FunctionField <| XClass_ne_zero W x₁]

-- porting note: increased `maxHeartbeats` for `ring1`
set_option synthInstance.maxHeartbeats 60000 in
set_option maxHeartbeats 600000 in
lemma XYIdeal_mul_XYIdeal (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    XIdeal W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) * (XYIdeal W x₁ (C y₁) * XYIdeal W x₂ (C y₂)) =
      YIdeal W (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) *
        XYIdeal W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)
          (C <| W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  -- porting note: removed assumption `h₂` explicitly
  clear h₂
  have sup_rw : ∀ a b c d : Ideal W.CoordinateRing, a ⊔ (b ⊔ (c ⊔ d)) = a ⊔ d ⊔ b ⊔ c :=
    fun _ _ c _ => by rw [← sup_assoc, @sup_comm _ _ c, sup_sup_sup_comm, ← sup_assoc]
  rw [XYIdeal_add_eq, XIdeal, mul_comm, W.XYIdeal_eq₁ x₁ y₁ <| W.slope x₁ x₂ y₁ y₂, XYIdeal,
    XYIdeal_eq₂ h₁' h₂' hxy, XYIdeal, span_pair_mul_span_pair]
  simp_rw [span_insert, sup_rw, sup_mul, span_singleton_mul_span_singleton]
  rw [← neg_eq_iff_eq_neg.mpr <| CoordinateRing.C_addPolynomial_slope h₁' h₂' hxy,
    span_singleton_neg, CoordinateRing.C_addPolynomial, _root_.map_mul, YClass]
  simp_rw [mul_comm <| XClass W x₁, mul_assoc, ← span_singleton_mul_span_singleton, ← mul_sup]
  rw [span_singleton_mul_span_singleton, ← span_insert,
    ← span_pair_add_mul_right <| -(XClass W <| W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂), mul_neg,
    ← sub_eq_add_neg, ← sub_mul, ← map_sub <| CoordinateRing.mk W, sub_sub_sub_cancel_right,
    span_insert, ← span_singleton_mul_span_singleton, ← sup_rw, ← sup_mul, ← sup_mul]
  apply congr_arg (_ ∘ _)
  convert top_mul (_ : Ideal W.CoordinateRing)
  simp_rw [XClass, ← @Set.image_singleton _ _ <| CoordinateRing.mk W, ← map_span, ← Ideal.map_sup,
    eq_top_iff_one, mem_map_iff_of_surjective _ AdjoinRoot.mk_surjective, ← span_insert,
    mem_span_insert', mem_span_singleton']
  by_cases hx : x₁ = x₂
  · rcases hx, Y_eq_of_Y_ne h₁' h₂' hx (hxy hx) with ⟨rfl, rfl⟩
    let y := (y₁ - W.negY x₁ y₁) ^ 2
    replace hxy := pow_ne_zero 2 (sub_ne_zero_of_ne <| hxy rfl)
    refine
      ⟨1 + C (C <| y⁻¹ * 4) * W.polynomial,
        ⟨C <| C y⁻¹ * (C 4 * X ^ 2 + C (4 * x₁ + W.b₂) * X + C (4 * x₁ ^ 2 + W.b₂ * x₁ + 2 * W.b₄)),
          0, C (C y⁻¹) * (Y - W.negPolynomial), ?_⟩, by
        rw [map_add, map_one, _root_.map_mul <| CoordinateRing.mk W, AdjoinRoot.mk_self, mul_zero,
          add_zero]⟩
    rw [WeierstrassCurve.polynomial, negPolynomial,
      ← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hxy]
    simp only [mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel hxy]
    linear_combination (norm := (rw [b₂, b₄, negY]; C_simp; ring1))
      -4 * congr_arg C (congr_arg C <| (W.equation_iff _ _).mp h₁')
  · replace hx := sub_ne_zero_of_ne hx
    refine ⟨_, ⟨⟨C <| C (x₁ - x₂)⁻¹, C <| C <| (x₁ - x₂)⁻¹ * -1, 0, ?_⟩, map_one _⟩⟩
    rw [← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hx]
    simp only [← mul_assoc, mul_add, ← C_mul, mul_inv_cancel hx]
    C_simp
    ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal_mul_XY_ideal WeierstrassCurve.XYIdeal_mul_XYIdeal

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
/-- The non-zero fractional ideal $\langle X - x, Y - y \rangle$ of $F(W)$ for some $x, y \in F$. -/
noncomputable def XYIdeal' : (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ :=
  Units.mkOfMulEqOne _ _ <| XYIdeal'_mul_inv h₁
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal' WeierstrassCurve.XYIdeal'

lemma XYIdeal'_eq :
    (XYIdeal' h₁ : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = XYIdeal W x₁ (C y₁) :=
  rfl
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal'_eq WeierstrassCurve.XYIdeal'_eq

lemma mk_XYIdeal'_mul_mk_XYIdeal'_of_Y_eq :
    ClassGroup.mk (XYIdeal' <| nonsingular_neg h₁) * ClassGroup.mk (XYIdeal' h₁) = 1 := by
  rw [← _root_.map_mul]
  exact
    (ClassGroup.mk_eq_one_of_coe_ideal <| by exact (FractionalIdeal.coeIdeal_mul _ _).symm.trans <|
      FractionalIdeal.coeIdeal_inj.mpr <| XYIdeal_neg_mul h₁).mpr ⟨_, XClass_ne_zero W _, rfl⟩
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.mk_XY_ideal'_mul_mk_XY_ideal'_of_Y_eq WeierstrassCurve.mk_XYIdeal'_mul_mk_XYIdeal'_of_Y_eq

lemma mk_XYIdeal'_mul_mk_XYIdeal' (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    ClassGroup.mk (XYIdeal' h₁) * ClassGroup.mk (XYIdeal' h₂) =
      ClassGroup.mk (XYIdeal' <| nonsingular_add h₁ h₂ hxy) := by
  rw [← _root_.map_mul]
  exact
    (ClassGroup.mk_eq_mk_of_coe_ideal (by exact (FractionalIdeal.coeIdeal_mul _ _).symm) <|
        XYIdeal'_eq _).mpr
      ⟨_, _, XClass_ne_zero W _, YClass_ne_zero W _, XYIdeal_mul_XYIdeal h₁.left h₂.left hxy⟩
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.mk_XY_ideal'_mul_mk_XY_ideal' WeierstrassCurve.mk_XYIdeal'_mul_mk_XYIdeal'

namespace Point

/-- The set function mapping an affine point $(x, y)$ of `W` to the class of the non-zero fractional
ideal $\langle X - x, Y - y \rangle$ of $F(W)$ in the class group of $F[W]$. -/
@[simp]
noncomputable def toClassFun : W.Point → Additive (ClassGroup W.CoordinateRing)
  | 0 => 0
  | some h => Additive.ofMul <| ClassGroup.mk <| XYIdeal' h
#align weierstrass_curve.point.to_class_fun WeierstrassCurve.Point.toClassFun

/-- The group homomorphism mapping an affine point $(x, y)$ of `W` to the class of the non-zero
fractional ideal $\langle X - x, Y - y \rangle$ of $F(W)$ in the class group of $F[W]$. -/
@[simps]
noncomputable def toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing) where
  toFun := toClassFun
  map_zero' := rfl
  map_add' := by
    rintro (_ | @⟨x₁, y₁, h₁⟩) (_ | @⟨x₂, y₂, h₂⟩)
    any_goals simp only [zero_def, toClassFun, _root_.zero_add, _root_.add_zero]
    by_cases hx : x₁ = x₂
    · by_cases hy : y₁ = W.negY x₂ y₂
      · substs hx hy
        simpa only [some_add_some_of_Y_eq rfl rfl] using
          (mk_XYIdeal'_mul_mk_XYIdeal'_of_Y_eq h₂).symm
      · simpa only [some_add_some_of_Y_ne hx hy] using
          (mk_XYIdeal'_mul_mk_XYIdeal' h₁ h₂ fun _ => hy).symm
    · simpa only [some_add_some_of_X_ne hx] using
        (mk_XYIdeal'_mul_mk_XYIdeal' h₁ h₂ fun h => (hx h).elim).symm
#align weierstrass_curve.point.to_class WeierstrassCurve.Point.toClass

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
lemma toClass_zero : toClass (0 : W.Point) = 0 :=
  rfl
#align weierstrass_curve.point.to_class_zero WeierstrassCurve.Point.toClass_zero

lemma toClass_some : toClass (some h₁) = ClassGroup.mk (XYIdeal' h₁) :=
  rfl
#align weierstrass_curve.point.to_class_some WeierstrassCurve.Point.toClass_some

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
lemma add_eq_zero (P Q : W.Point) : P + Q = 0 ↔ P = -Q := by
  rcases P, Q with ⟨_ | @⟨x₁, y₁, _⟩, _ | @⟨x₂, y₂, _⟩⟩
  any_goals rfl
  · rw [zero_def, zero_add, ← neg_eq_iff_eq_neg, neg_zero, eq_comm]
  · rw [neg_some, some.injEq]
    constructor
    · intro h
      by_cases hx : x₁ = x₂
      · by_cases hy : y₁ = W.negY x₂ y₂
        · exact ⟨hx, hy⟩
        · rw [some_add_some_of_Y_ne hx hy] at h
          contradiction
      · rw [some_add_some_of_X_ne hx] at h
        contradiction
    · exact fun ⟨hx, hy⟩ => some_add_some_of_Y_eq hx hy
#align weierstrass_curve.point.add_eq_zero WeierstrassCurve.Point.add_eq_zero

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
lemma add_left_neg (P : W.Point) : -P + P = 0 := by
  rw [add_eq_zero]
#align weierstrass_curve.point.add_left_neg WeierstrassCurve.Point.add_left_neg

-- porting note: removed `@[simp]` to avoid a `simpNF` linter error
lemma neg_add_eq_zero (P Q : W.Point) : -P + Q = 0 ↔ P = Q := by
  rw [add_eq_zero, neg_inj]
#align weierstrass_curve.point.neg_add_eq_zero WeierstrassCurve.Point.neg_add_eq_zero

lemma toClass_eq_zero (P : W.Point) : toClass P = 0 ↔ P = 0 := by
  constructor
  · intro hP
    rcases P with (_ | @⟨_, _, ⟨h, _⟩⟩)
    · rfl
    · rcases (ClassGroup.mk_eq_one_of_coe_ideal <| by rfl).mp hP with ⟨p, h0, hp⟩
      apply (p.natDegree_norm_ne_one _).elim
      rw [← finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W) h0,
        ← (quotientEquivAlgOfEq F hp).toLinearEquiv.finrank_eq,
        (quotientXYIdealEquiv W h).toLinearEquiv.finrank_eq, FiniteDimensional.finrank_self]
  · exact congr_arg toClass
#align weierstrass_curve.point.to_class_eq_zero WeierstrassCurve.Point.toClass_eq_zero

lemma toClass_injective : Function.Injective <| @toClass _ _ W := by
  rintro (_ | h) _ hP
  all_goals rw [← neg_add_eq_zero, ← toClass_eq_zero, map_add, ← hP]
  · exact zero_add 0
  · exact mk_XYIdeal'_mul_mk_XYIdeal'_of_Y_eq h
#align weierstrass_curve.point.to_class_injective WeierstrassCurve.Point.toClass_injective

lemma add_comm (P Q : W.Point) : P + Q = Q + P :=
  toClass_injective <| by simp only [map_add, _root_.add_comm]
#align weierstrass_curve.point.add_comm WeierstrassCurve.Point.add_comm

lemma add_assoc (P Q R : W.Point) : P + Q + R = P + (Q + R) :=
  toClass_injective <| by simp only [map_add, _root_.add_assoc]
#align weierstrass_curve.point.add_assoc WeierstrassCurve.Point.add_assoc

noncomputable instance instAddCommGroupPoint : AddCommGroup W.Point where
  zero := zero
  neg := neg
  add := add
  zero_add := zero_add
  add_zero := add_zero
  add_left_neg := add_left_neg
  add_comm := add_comm
  add_assoc := add_assoc

end Point

end Group

section BaseChange

/-! ### Nonsingular rational points on a base changed Weierstrass curve -/

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (F : Type v) [Field F] [Algebra R F]
  (K : Type w) [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]

namespace Point

open scoped WeierstrassCurve

/-- The function from `W⟮F⟯` to `W⟮K⟯` induced by a base change from `F` to `K`. -/
def ofBaseChangeFun : W⟮F⟯ → W⟮K⟯
  | 0 => 0
  | some h => some <| (nonsingular_iff_baseChange_of_baseChange W F K _ _).mp h
#align weierstrass_curve.point.of_base_change_fun WeierstrassCurve.Point.ofBaseChangeFun

/-- The group homomorphism from `W⟮F⟯` to `W⟮K⟯` induced by a base change from `F` to `K`. -/
@[simps]
def ofBaseChange : W⟮F⟯ →+ W⟮K⟯ where
  toFun := ofBaseChangeFun W F K
  map_zero' := rfl
  map_add' := by
    rintro (_ | @⟨x₁, y₁, _⟩) (_ | @⟨x₂, y₂, _⟩)
    any_goals rfl
    by_cases hx : x₁ = x₂
    · by_cases hy : y₁ = (W.baseChange F).negY x₂ y₂
      · simp only [some_add_some_of_Y_eq hx hy, ofBaseChangeFun]
        rw [some_add_some_of_Y_eq <| congr_arg _ hx]
        · rw [hy, baseChange_negY_of_baseChange]
      · simp only [some_add_some_of_Y_ne hx hy, ofBaseChangeFun]
        rw [some_add_some_of_Y_ne <| congr_arg _ hx]
        · simp only [baseChange_addX_of_baseChange, baseChange_addY_of_baseChange,
            baseChange_slope_of_baseChange]
        · rw [baseChange_negY_of_baseChange]
          contrapose! hy
          exact NoZeroSMulDivisors.algebraMap_injective F K hy
    · simp only [some_add_some_of_X_ne hx, ofBaseChangeFun]
      rw [some_add_some_of_X_ne]
      · simp only [baseChange_addX_of_baseChange, baseChange_addY_of_baseChange,
          baseChange_slope_of_baseChange]
      · contrapose! hx
        exact NoZeroSMulDivisors.algebraMap_injective F K hx
#align weierstrass_curve.point.of_base_change WeierstrassCurve.Point.ofBaseChange

lemma ofBaseChange_injective : Function.Injective <| ofBaseChange W F K := by
  rintro (_ | _) (_ | _) h
  any_goals contradiction
  · rfl
  · rw [some.injEq]
    exact
      ⟨NoZeroSMulDivisors.algebraMap_injective F K (some.inj h).left,
        NoZeroSMulDivisors.algebraMap_injective F K (some.inj h).right⟩
#align weierstrass_curve.point.of_base_change_injective WeierstrassCurve.Point.ofBaseChange_injective

end Point

end BaseChange

end WeierstrassCurve

namespace EllipticCurve

/-! ### Rational points on an elliptic curve -/

namespace Point

variable {R : Type} [Nontrivial R] [CommRing R] (E : EllipticCurve R)

/-- An affine point on an elliptic curve `E` over `R`. -/
def mk {x y : R} (h : E.equation x y) : E.Point :=
  WeierstrassCurve.Point.some <| E.nonsingular h
#align elliptic_curve.point.mk EllipticCurve.Point.mk

end Point

end EllipticCurve
