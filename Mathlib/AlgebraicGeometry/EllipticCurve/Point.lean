/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata

! This file was ported from Lean 3 source module algebraic_geometry.elliptic_curve.point
! leanprover-community/mathlib commit e2e7f2ac359e7514e4d40061d7c08bb69487ba4e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.RingTheory.ClassGroup

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

 * `weierstrass_curve.point`: the type of nonsingular rational points on a Weierstrass curve `W`.
 * `weierstrass_curve.point.add`: the addition of two nonsingular rational points on `W`.

## Main statements

 * `weierstrass_curve.point.add_comm_group`: the type of nonsingular rational points on `W` forms an
    abelian group under addition.

## Notations

 * `W⟮K⟯`: the group of nonsingular rational points on `W` base changed to `K`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, group law
-/

-- Porting note: copied from `Weierstass`
local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow])


universe u v w

namespace WeierstrassCurve

open CoordinateRing Ideal Polynomial

-- Porting note: copied from `Weierstass` and added `eval_neg`
--  and moved here because it needs `open Polynomial`
local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow, eval_neg])

-- Porting note: copied from `Weierstass` and moved here because it needs `open Polynomial`
local macro "C_simp" : tactic =>
  `(tactic| simp only [C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

-- Porting note: moved here because it needs `open Polynomial`
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

theorem negY_negY : W.negY x₁ (W.negY x₁ y₁) = y₁ := by simp only [negY]; ring1
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.neg_Y_neg_Y WeierstrassCurve.negY_negY

theorem baseChange_negY :
    (W.baseChange A).negY (algebraMap R A x₁) (algebraMap R A y₁) =
      algebraMap R A (W.negY x₁ y₁) := by
  simp only [negY]
  map_simp
  rfl
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.base_change_neg_Y WeierstrassCurve.baseChange_negY

theorem baseChange_negY_of_baseChange (x₁ y₁ : A) :
    (W.baseChange B).negY (algebraMap A B x₁) (algebraMap A B y₁) =
      algebraMap A B ((W.baseChange A).negY x₁ y₁) :=
  by rw [← baseChange_negY, baseChange_baseChange]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.base_change_neg_Y_of_base_change WeierstrassCurve.baseChange_negY_of_baseChange

@[simp]
theorem eval_negPolynomial : (W.negPolynomial.eval <| C y₁).eval x₁ = W.negY x₁ y₁ := by
  rw [negY, sub_sub, negPolynomial]
  eval_simp
#align weierstrass_curve.eval_neg_polynomial WeierstrassCurve.eval_negPolynomial

/-- The polynomial $L(X - x_1) + y_1$ associated to the line $Y = L(X - x_1) + y_1$,
with a slope of $L$ that passes through an affine point $(x_1, y_1)$.

This does not depend on `W`, and has argument order: $x_1$, $y_1$, $L$. -/
noncomputable def linePolynomial : R[X] :=
  C L * (X - C x₁) + C y₁
#align weierstrass_curve.line_polynomial WeierstrassCurve.linePolynomial

theorem xYIdeal_eq₁ : XYIdeal W x₁ (C y₁) = XYIdeal W x₁ (linePolynomial x₁ y₁ L) := by
  simp only [XYIdeal, XClass, YClass, linePolynomial]
  rw [← span_pair_add_mul_right <| AdjoinRoot.mk _ <| C <| C <| -L, ← _root_.map_mul, ← map_add]
  apply congr_arg (_ ∘ _ ∘ _ ∘ _)
  C_simp
  ring
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal_eq₁ WeierstrassCurve.xYIdeal_eq₁

/-- The polynomial obtained by substituting the line $Y = L*(X - x_1) + y_1$, with a slope of $L$
that passes through an affine point $(x_1, y_1)$, into the polynomial $W(X, Y)$ associated to `W`.
If such a line intersects `W` at another point $(x_2, y_2)$, then the roots of this polynomial are
precisely $x_1$, $x_2$, and the $X$-coordinate of the addition of $(x_1, y_1)$ and $(x_2, y_2)$.

This depends on `W`, and has argument order: $x_1$, $y_1$, $L$. -/
noncomputable def addPolynomial : R[X] :=
  W.polynomial.eval <| linePolynomial x₁ y₁ L
#align weierstrass_curve.add_polynomial WeierstrassCurve.addPolynomial

-- Porting note: here and elsewhere used `C_addPolynomial` instead of `c_addPolynomial`
theorem C_addPolynomial :
    C (W.addPolynomial x₁ y₁ L) =
      (Y - C (linePolynomial x₁ y₁ L)) * (W.negPolynomial - C (linePolynomial x₁ y₁ L)) +
        W.polynomial := by
  rw [addPolynomial, linePolynomial, WeierstrassCurve.polynomial, negPolynomial]
  eval_simp
  C_simp
  ring
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.C_add_polynomial WeierstrassCurve.C_addPolynomial

theorem CoordinateRing.C_addPolynomial :
    AdjoinRoot.mk W.polynomial (C (W.addPolynomial x₁ y₁ L)) =
      AdjoinRoot.mk W.polynomial
        ((Y - C (linePolynomial x₁ y₁ L)) * (W.negPolynomial - C (linePolynomial x₁ y₁ L))) :=
  AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [WeierstrassCurve.C_addPolynomial, add_sub_cancel', mul_one]⟩
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.coordinate_ring.C_add_polynomial WeierstrassCurve.CoordinateRing.C_addPolynomial

theorem addPolynomial_eq :
    W.addPolynomial x₁ y₁ L =
      -Cubic.toPoly
          ⟨1, -L ^ 2 - W.a₁ * L + W.a₂,
            2 * x₁ * L ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * L + (-W.a₁ * y₁ + W.a₄),
            -x₁ ^ 2 * L ^ 2 + (2 * x₁ * y₁ + W.a₃ * x₁) * L - (y₁ ^ 2 + W.a₃ * y₁ - W.a₆)⟩ := by
  rw [addPolynomial, linePolynomial, WeierstrassCurve.polynomial, Cubic.toPoly]
  eval_simp
  C_simp
  -- Porting note: `ring` and `ring1` do not work
  ring_nf
  rfl
#align weierstrass_curve.add_polynomial_eq WeierstrassCurve.addPolynomial_eq

/-- The $X$-coordinate of the addition of two affine points $(x_1, y_1)$ and $(x_2, y_2)$ in `W`,
where the line through them is not vertical and has a slope of $L$.

This depends on `W`, and has argument order: $x_1$, $x_2$, $L$. -/
@[simp]
def addX : R :=
  L ^ 2 + W.a₁ * L - W.a₂ - x₁ - x₂
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.add_X WeierstrassCurve.addX

theorem baseChange_addX :
    (W.baseChange A).addX (algebraMap R A x₁) (algebraMap R A x₂) (algebraMap R A L) =
      algebraMap R A (W.addX x₁ x₂ L) := by
  simp only [addX]
  map_simp
  rfl
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.base_change_add_X WeierstrassCurve.baseChange_addX

theorem baseChange_addX_of_baseChange (x₁ x₂ L : A) :
    (W.baseChange B).addX (algebraMap A B x₁) (algebraMap A B x₂) (algebraMap A B L) =
      algebraMap A B ((W.baseChange A).addX x₁ x₂ L) :=
  by rw [← baseChange_addX, baseChange_baseChange]
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

theorem baseChange_addY' :
    (W.baseChange A).addY' (algebraMap R A x₁) (algebraMap R A x₂) (algebraMap R A y₁)
        (algebraMap R A L) = algebraMap R A (W.addY' x₁ x₂ y₁ L) := by
  simp only [addY', baseChange_addX]
  map_simp
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.base_change_add_Y' WeierstrassCurve.baseChange_addY'

theorem baseChange_addY'_of_baseChange (x₁ x₂ y₁ L : A) :
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

theorem baseChange_addY :
    (W.baseChange A).addY (algebraMap R A x₁) (algebraMap R A x₂) (algebraMap R A y₁)
        (algebraMap R A L) = algebraMap R A (W.addY x₁ x₂ y₁ L) := by
  simp only [addY, baseChange_addY', baseChange_addX, baseChange_negY]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.base_change_add_Y WeierstrassCurve.baseChange_addY

theorem baseChange_addY_of_baseChange (x₁ x₂ y₁ L : A) :
    (W.baseChange B).addY (algebraMap A B x₁) (algebraMap A B x₂) (algebraMap A B y₁)
        (algebraMap A B L) = algebraMap A B ((W.baseChange A).addY x₁ x₂ y₁ L) := by
  rw [← baseChange_addY, baseChange_baseChange]
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.base_change_add_Y_of_base_change WeierstrassCurve.baseChange_addY_of_baseChange

-- Porting note: change name to `XYIdeal_add_eq` instead of `xYIdeal_add_eq`
set_option maxHeartbeats 300000 in
theorem XYIdeal_add_eq :
    XYIdeal W (W.addX x₁ x₂ L) (C (W.addY x₁ x₂ y₁ L)) =
      span {AdjoinRoot.mk W.polynomial <| W.negPolynomial - C (linePolynomial x₁ y₁ L)} ⊔
        XIdeal W (W.addX x₁ x₂ L) := by
  simp only [XYIdeal, XIdeal, XClass, YClass, addY, addY', negY, negPolynomial, linePolynomial]
  -- Porting note: original proof
  --  conv_rhs => rw [sub_sub, ← neg_add', map_neg, span_singleton_neg, sup_comm, ← span_insert]
  -- but using a `conv` here times out the rest of the proof
  rw [show span {(AdjoinRoot.mk (W.polynomial))
      (-Y - (C (C W.a₁ * Y + C W.a₃ : R[X]) : R[X][Y])
      - (C (C L * (Y - C x₁) + C y₁ : R[X]) : R[X][Y]))} ⊔
      span {CoordinateRing.mk W (C (Y - (C (addX W x₁ x₂ L) : R[X])) : R[X][Y])} =
      span {CoordinateRing.mk W (C (Y - (C (addX W x₁ x₂ L) : R[X])) : R[X][Y]),
      (AdjoinRoot.mk (WeierstrassCurve.polynomial W))
      (Y + (C (C W.a₁ * Y + C W.a₃) + C (C L * (Y - C x₁) + C y₁)))} by
    rw [sub_sub, ← neg_add', map_neg, span_singleton_neg, sup_comm, ← span_insert]]
  rw [← span_pair_add_mul_right <| AdjoinRoot.mk _ <| C <| C <| W.a₁ + L, ← _root_.map_mul,
    ← map_add]
  apply congr_arg (_ ∘ _ ∘ _ ∘ _)
  C_simp
  ring
set_option linter.uppercaseLean3 false in
#align weierstrass_curve.XY_ideal_add_eq WeierstrassCurve.XYIdeal_add_eq

theorem equation_add_iff :
    W.equation (W.addX x₁ x₂ L) (W.addY' x₁ x₂ y₁ L) ↔
      (W.addPolynomial x₁ y₁ L).eval (W.addX x₁ x₂ L) = 0 := by
  rw [WeierstrassCurve.equation, addY', addPolynomial, linePolynomial, WeierstrassCurve.polynomial]
  eval_simp
#align weierstrass_curve.equation_add_iff WeierstrassCurve.equation_add_iff

theorem nonsingular_add_of_eval_derivative_ne_zero
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
  simp only [zero_add, add_zero, sub_zero, MulZeroClass.zero_mul, mul_one]
  eval_simp
  linear_combination (norm := (norm_num1; ring1)) hx.left + L * hx.right
#align weierstrass_curve.nonsingular_add_of_eval_derivative_ne_zero WeierstrassCurve.nonsingular_add_of_eval_derivative_ne_zero

/-! ### The type of nonsingular rational points on a Weierstrass curve -/


/-- A nonsingular rational point on a Weierstrass curve `W` over `R`. This is either the point at
infinity `weierstrass_curve.point.zero` or an affine point `weierstrass_curve.point.some` $(x, y)$
satisfying the equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$ of `W`. For an algebraic
extension `S` of `R`, the type of nonsingular `S`-rational points on `W` is denoted `W⟮S⟯`. -/
inductive Point
  | zero
  | some {x y : R} (h : W.nonsingular x y)
#align weierstrass_curve.point WeierstrassCurve.Point

scoped notation W "⟮" S "⟯" => (W.base_change S).Point

namespace Point

instance : Inhabited W.Point :=
  ⟨zero⟩

instance : Zero W.Point :=
  ⟨zero⟩

@[simp]
theorem zero_def : (zero : W.Point) = 0 :=
  rfl
#align weierstrass_curve.point.zero_def WeierstrassCurve.Point.zero_def

end Point

variable {W x₁ y₁}

theorem equation_neg_iff : W.equation x₁ (W.negY x₁ y₁) ↔ W.equation x₁ y₁ := by
  rw [equation_iff, equation_iff, neg_Y]; congr 2; ring1
#align weierstrass_curve.equation_neg_iff WeierstrassCurve.equation_neg_iff

theorem equation_neg_of (h : W.equation x₁ <| W.negY x₁ y₁) : W.equation x₁ y₁ :=
  equation_neg_iff.mp h
#align weierstrass_curve.equation_neg_of WeierstrassCurve.equation_neg_of

/-- The negation of an affine point in `W` lies in `W`. -/
theorem equation_neg (h : W.equation x₁ y₁) : W.equation x₁ <| W.negY x₁ y₁ :=
  equation_neg_iff.mpr h
#align weierstrass_curve.equation_neg WeierstrassCurve.equation_neg

theorem nonsingular_neg_iff : W.nonsingular x₁ (W.negY x₁ y₁) ↔ W.nonsingular x₁ y₁ := by
  rw [nonsingular_iff, equation_neg_iff, ← neg_Y, neg_Y_neg_Y, ← @ne_comm _ y₁, nonsingular_iff]
  exact
    and_congr_right'
      ((iff_congr not_and_distrib.symm not_and_distrib.symm).mpr <|
        not_congr <| and_congr_left fun h => by rw [← h])
#align weierstrass_curve.nonsingular_neg_iff WeierstrassCurve.nonsingular_neg_iff

theorem nonsingular_neg_of (h : W.nonsingular x₁ <| W.negY x₁ y₁) : W.nonsingular x₁ y₁ :=
  nonsingular_neg_iff.mp h
#align weierstrass_curve.nonsingular_neg_of WeierstrassCurve.nonsingular_neg_of

/-- The negation of a nonsingular affine point in `W` is nonsingular. -/
theorem nonsingular_neg (h : W.nonsingular x₁ y₁) : W.nonsingular x₁ <| W.negY x₁ y₁ :=
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

@[simp]
theorem neg_def (P : W.Point) : P.neg = -P :=
  rfl
#align weierstrass_curve.point.neg_def WeierstrassCurve.Point.neg_def

@[simp]
theorem neg_zero : (-0 : W.Point) = 0 :=
  rfl
#align weierstrass_curve.point.neg_zero WeierstrassCurve.Point.neg_zero

@[simp]
theorem neg_some (h : W.nonsingular x₁ y₁) : -some h = some (nonsingular_neg h) :=
  rfl
#align weierstrass_curve.point.neg_some WeierstrassCurve.Point.neg_some

instance : InvolutiveNeg W.Point :=
  ⟨neg, by rintro (_ | _); · rfl; · simp; ring1⟩

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
  if hx : x₁ = x₂ then
    if hy : y₁ = W.negY x₂ y₂ then 0
    else (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.negY x₁ y₁)
  else (y₁ - y₂) / (x₁ - x₂)
#align weierstrass_curve.slope WeierstrassCurve.slope

variable {W x₁ x₂ y₁ y₂} (h₁ : W.nonsingular x₁ y₁) (h₂ : W.nonsingular x₂ y₂)
  (h₁' : W.equation x₁ y₁) (h₂' : W.equation x₂ y₂)

@[simp]
theorem slope_of_Y_eq (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂) : W.slope x₁ x₂ y₁ y₂ = 0 := by
  rw [slope, dif_pos hx, dif_pos hy]
#align weierstrass_curve.slope_of_Y_eq WeierstrassCurve.slope_of_Y_eq

@[simp]
theorem slope_of_Y_ne (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) :
    W.slope x₁ x₂ y₁ y₂ = (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.negY x₁ y₁) :=
  by rw [slope, dif_pos hx, dif_neg hy]
#align weierstrass_curve.slope_of_Y_ne WeierstrassCurve.slope_of_Y_ne

@[simp]
theorem slope_of_X_ne (hx : x₁ ≠ x₂) : W.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) := by
  rw [slope, dif_neg hx]
#align weierstrass_curve.slope_of_X_ne WeierstrassCurve.slope_of_X_ne

theorem slope_of_Y_ne_eq_eval (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) :
    W.slope x₁ x₂ y₁ y₂ =
      -(W.polynomialX.eval <| C y₁).eval x₁ / (W.polynomialY.eval <| C y₁).eval x₁ := by
  rw [slope_of_Y_ne hx hy, eval_polynomial_X, neg_sub]; congr 1; rw [neg_Y, eval_polynomial_Y]
  ring1
#align weierstrass_curve.slope_of_Y_ne_eq_eval WeierstrassCurve.slope_of_Y_ne_eq_eval

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2652570801.map_simp -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2652570801.map_simp -/
theorem baseChange_slope :
    (W.base_change K).slope (algebraMap F K x₁) (algebraMap F K x₂) (algebraMap F K y₁)
        (algebraMap F K y₂) =
      algebraMap F K (W.slope x₁ x₂ y₁ y₂) := by
  by_cases hx : x₁ = x₂
  · by_cases hy : y₁ = W.neg_Y x₂ y₂
    · rw [slope_of_Y_eq hx hy, slope_of_Y_eq <| congr_arg _ hx, map_zero]
      · rw [hy, base_change_neg_Y]
    · rw [slope_of_Y_ne hx hy, slope_of_Y_ne <| congr_arg _ hx]
      · run_tac
          map_simp
        simpa only [base_change_neg_Y]
      · rw [base_change_neg_Y]
        contrapose! hy
        exact NoZeroSMulDivisors.algebraMap_injective F K hy
  · rw [slope_of_X_ne hx, slope_of_X_ne]
    ·
      run_tac
        map_simp
    · contrapose! hx
      exact NoZeroSMulDivisors.algebraMap_injective F K hx
#align weierstrass_curve.base_change_slope WeierstrassCurve.baseChange_slope

theorem baseChange_slope_of_baseChange {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type v) [Field F] [Algebra R F] (K : Type w) [Field K] [Algebra R K] [Algebra F K]
    [IsScalarTower R F K] (x₁ x₂ y₁ y₂ : F) :
    (W.base_change K).slope (algebraMap F K x₁) (algebraMap F K x₂) (algebraMap F K y₁)
        (algebraMap F K y₂) =
      algebraMap F K ((W.base_change F).slope x₁ x₂ y₁ y₂) :=
  by rw [← base_change_slope, base_change_base_change]
#align weierstrass_curve.base_change_slope_of_base_change WeierstrassCurve.baseChange_slope_of_baseChange

theorem Y_eq_of_X_eq (hx : x₁ = x₂) : y₁ = y₂ ∨ y₁ = W.negY x₂ y₂ := by
  rw [equation_iff] at h₁' h₂'
  rw [← sub_eq_zero, ← @sub_eq_zero _ _ y₁, ← mul_eq_zero, neg_Y]
  linear_combination (norm := (rw [hx]; ring1)) h₁' - h₂'
#align weierstrass_curve.Y_eq_of_X_eq WeierstrassCurve.Y_eq_of_X_eq

theorem Y_eq_of_Y_ne (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) : y₁ = y₂ :=
  Or.resolve_right (Y_eq_of_X_eq h₁' h₂' hx) hy
#align weierstrass_curve.Y_eq_of_Y_ne WeierstrassCurve.Y_eq_of_Y_ne

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2062814307.eval_simp -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1008755739.C_simp -/
theorem xYIdeal_eq₂ (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    XYIdeal W x₂ (C y₂) = XYIdeal W x₂ (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  have hy₂ : y₂ = (line_polynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂).eval x₂ := by
    by_cases hx : x₁ = x₂
    · rcases hx, Y_eq_of_Y_ne h₁' h₂' hx <| hxy hx with ⟨rfl, rfl⟩
      field_simp [line_polynomial, sub_ne_zero_of_ne (hxy rfl)]
    · field_simp [line_polynomial, slope_of_X_ne hx, sub_ne_zero_of_ne hx]
      ring1
  nth_rw_lhs 1 [hy₂]
  simp only [XY_ideal, X_class, Y_class, line_polynomial]
  rw [← span_pair_add_mul_right <| AdjoinRoot.mk W.polynomial <| C <| C <| -W.slope x₁ x₂ y₁ y₂, ←
    _root_.map_mul, ← map_add]
  apply congr_arg (_ ∘ _ ∘ _ ∘ _)
  run_tac
    eval_simp
  run_tac
    C_simp
  ring1
#align weierstrass_curve.XY_ideal_eq₂ WeierstrassCurve.xYIdeal_eq₂

theorem addPolynomial_slope (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    W.addPolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂) =
      -((X - C x₁) * (X - C x₂) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂))) := by
  rw [add_polynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective]
  by_cases hx : x₁ = x₂
  · rcases hx, Y_eq_of_Y_ne h₁' h₂' hx (hxy hx) with ⟨rfl, rfl⟩
    rw [equation_iff] at h₁' h₂'
    rw [slope_of_Y_ne rfl <| hxy rfl]
    rw [neg_Y, ← sub_ne_zero] at hxy
    ext
    · rfl
    · simp only [add_X]
      ring1
    · field_simp [hxy rfl]
      ring1
    · linear_combination (norm := (field_simp [hxy rfl]; ring1)) -h₁'
  · rw [equation_iff] at h₁' h₂'
    rw [slope_of_X_ne hx]
    rw [← sub_eq_zero] at hx
    ext
    · rfl
    · simp only [add_X]
      ring1
    · apply mul_right_injective₀ hx
      linear_combination (norm := (field_simp [hx]; ring1)) h₂' - h₁'
    · apply mul_right_injective₀ hx
      linear_combination (norm := (field_simp [hx]; ring1)) x₂ * h₁' - x₁ * h₂'
#align weierstrass_curve.add_polynomial_slope WeierstrassCurve.addPolynomial_slope

theorem CoordinateRing.c_addPolynomial_slope (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    AdjoinRoot.mk W.Polynomial (C <| W.addPolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) =
      -(XClass W x₁ * XClass W x₂ * XClass W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)) :=
  by simpa only [add_polynomial_slope h₁' h₂' hxy, map_neg, neg_inj, _root_.map_mul]
#align weierstrass_curve.coordinate_ring.C_add_polynomial_slope WeierstrassCurve.CoordinateRing.c_addPolynomial_slope

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1686593491.derivative_simp -/
theorem derivative_addPolynomial_slope (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    derivative (W.addPolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) =
      -((X - C x₁) * (X - C x₂) + (X - C x₁) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)) +
          (X - C x₂) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂))) :=
  by rw [add_polynomial_slope h₁' h₂' hxy];
  run_tac
    derivative_simp;
  ring1
#align weierstrass_curve.derivative_add_polynomial_slope WeierstrassCurve.derivative_addPolynomial_slope

/-! ### The addition law on nonsingular rational points on a Weierstrass curve -/


/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2062814307.eval_simp -/
/-- The addition of two affine points in `W` on a sloped line,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$, lies in `W`. -/
theorem equation_add' (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    W.equation (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.addY' x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  rw [equation_add_iff, add_polynomial_slope h₁' h₂' hxy];
  run_tac
    eval_simp
  rw [neg_eq_zero, sub_self, MulZeroClass.mul_zero]
#align weierstrass_curve.equation_add' WeierstrassCurve.equation_add'

/-- The addition of two affine points in `W` on a sloped line lies in `W`. -/
theorem equation_add (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    W.equation (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) :=
  equation_neg <| equation_add' h₁' h₂' hxy
#align weierstrass_curve.equation_add WeierstrassCurve.equation_add

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2062814307.eval_simp -/
/-- The addition of two nonsingular affine points in `W` on a sloped line,
before applying the final negation that maps $Y$ to $-Y - a_1X - a_3$, is nonsingular. -/
theorem nonsingular_add' (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    W.nonsingular (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.addY' x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) :=
  by
  by_cases hx₁ : W.add_X x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₁
  · rwa [add_Y', hx₁, sub_self, MulZeroClass.mul_zero, zero_add]
  · by_cases hx₂ : W.add_X x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₂
    · by_cases hx : x₁ = x₂
      · subst hx
        contradiction
      ·
        rwa [add_Y', ← neg_sub, mul_neg, hx₂, slope_of_X_ne hx,
          div_mul_cancel _ <| sub_ne_zero_of_ne hx, neg_sub, sub_add_cancel]
    · apply W.nonsingular_add_of_eval_derivative_ne_zero _ _ _ _ (equation_add' h₁.1 h₂.1 hxy)
      rw [derivative_add_polynomial_slope h₁.left h₂.left hxy]
      run_tac
        eval_simp
      simpa only [neg_ne_zero, sub_self, MulZeroClass.mul_zero, add_zero] using
        mul_ne_zero (sub_ne_zero_of_ne hx₁) (sub_ne_zero_of_ne hx₂)
#align weierstrass_curve.nonsingular_add' WeierstrassCurve.nonsingular_add'

/-- The addition of two nonsingular affine points in `W` on a sloped line is nonsingular. -/
theorem nonsingular_add (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
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

noncomputable instance : Add W.Point :=
  ⟨add⟩

@[simp]
theorem add_def (P Q : W.Point) : P.add Q = P + Q :=
  rfl
#align weierstrass_curve.point.add_def WeierstrassCurve.Point.add_def

noncomputable instance : AddZeroClass W.Point :=
  ⟨0, (· + ·), by rintro (_ | _) <;> rfl, by rintro (_ | _) <;> rfl⟩

@[simp]
theorem some_add_some_of_Y_eq (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂) : some h₁ + some h₂ = 0 := by
  rw [← add_def, add, dif_pos hx, dif_pos hy]
#align weierstrass_curve.point.some_add_some_of_Y_eq WeierstrassCurve.Point.some_add_some_of_Y_eq

@[simp]
theorem some_add_self_of_Y_eq (hy : y₁ = W.negY x₁ y₁) : some h₁ + some h₁ = 0 :=
  some_add_some_of_Y_eq rfl hy
#align weierstrass_curve.point.some_add_self_of_Y_eq WeierstrassCurve.Point.some_add_self_of_Y_eq

@[simp]
theorem some_add_some_of_Y_ne (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) :
    some h₁ + some h₂ = some (nonsingular_add h₁ h₂ fun _ => hy) := by
  rw [← add_def, add, dif_pos hx, dif_neg hy]
#align weierstrass_curve.point.some_add_some_of_Y_ne WeierstrassCurve.Point.some_add_some_of_Y_ne

theorem some_add_some_of_Y_ne' (hx : x₁ = x₂) (hy : y₁ ≠ W.negY x₂ y₂) :
    some h₁ + some h₂ = -some (nonsingular_add' h₁ h₂ fun _ => hy) :=
  some_add_some_of_Y_ne hx hy
#align weierstrass_curve.point.some_add_some_of_Y_ne' WeierstrassCurve.Point.some_add_some_of_Y_ne'

@[simp]
theorem some_add_self_of_Y_ne (hy : y₁ ≠ W.negY x₁ y₁) :
    some h₁ + some h₁ = some (nonsingular_add h₁ h₁ fun _ => hy) :=
  some_add_some_of_Y_ne rfl hy
#align weierstrass_curve.point.some_add_self_of_Y_ne WeierstrassCurve.Point.some_add_self_of_Y_ne

theorem some_add_self_of_Y_ne' (hy : y₁ ≠ W.negY x₁ y₁) :
    some h₁ + some h₁ = -some (nonsingular_add' h₁ h₁ fun _ => hy) :=
  some_add_some_of_Y_ne rfl hy
#align weierstrass_curve.point.some_add_self_of_Y_ne' WeierstrassCurve.Point.some_add_self_of_Y_ne'

@[simp]
theorem some_add_some_of_X_ne (hx : x₁ ≠ x₂) :
    some h₁ + some h₂ = some (nonsingular_add h₁ h₂ fun h => (hx h).elim) := by
  rw [← add_def, add, dif_neg hx]
#align weierstrass_curve.point.some_add_some_of_X_ne WeierstrassCurve.Point.some_add_some_of_X_ne

theorem some_add_some_of_X_ne' (hx : x₁ ≠ x₂) :
    some h₁ + some h₂ = -some (nonsingular_add' h₁ h₂ fun h => (hx h).elim) :=
  some_add_some_of_X_ne hx
#align weierstrass_curve.point.some_add_some_of_X_ne' WeierstrassCurve.Point.some_add_some_of_X_ne'

end Point

end Addition

section Group

/-! ### The axioms for nonsingular rational points on a Weierstrass curve -/


variable {F : Type u} [Field F] {W : WeierstrassCurve F} {x₁ x₂ y₁ y₂ : F}
  (h₁ : W.nonsingular x₁ y₁) (h₂ : W.nonsingular x₂ y₂) (h₁' : W.equation x₁ y₁)
  (h₂' : W.equation x₂ y₂)

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1008755739.C_simp -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1008755739.C_simp -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1008755739.C_simp -/
theorem xYIdeal_neg_mul : XYIdeal W x₁ (C <| W.negY x₁ y₁) * XYIdeal W x₁ (C y₁) = XIdeal W x₁ := by
  have Y_rw :
    (Y - C (C y₁)) * (Y - C (C (W.neg_Y x₁ y₁))) -
        C (X - C x₁) *
          (C (X ^ 2 + C (x₁ + W.a₂) * X + C (x₁ ^ 2 + W.a₂ * x₁ + W.a₄)) - C (C W.a₁) * Y) =
      W.polynomial * 1 := by
    linear_combination (norm :=
      (rw [neg_Y, WeierstrassCurve.polynomial];
        run_tac
          C_simp;
        ring1))
      congr_arg C (congr_arg C ((W.equation_iff _ _).mp h₁.left).symm)
  simp_rw [XY_ideal, X_class, Y_class, span_pair_mul_span_pair, mul_comm, ← _root_.map_mul,
    adjoin_root.mk_eq_mk.mpr ⟨1, Y_rw⟩, _root_.map_mul, span_insert, ←
    span_singleton_mul_span_singleton, ← mul_sup, ← span_insert]
  convert mul_top _ using 2
  simp_rw [← @Set.image_singleton _ _ <| AdjoinRoot.mk _, ← Set.image_insert_eq, ← map_span]
  convert map_top (AdjoinRoot.mk W.polynomial) using 1
  apply congr_arg
  simp_rw [eq_top_iff_one, mem_span_insert', mem_span_singleton']
  cases' ((W.nonsingular_iff' _ _).mp h₁).right with hx hy
  · let W_X := W.a₁ * y₁ - (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄)
    refine'
      ⟨C (C W_X⁻¹ * -(X + C (2 * x₁ + W.a₂))), C (C <| W_X⁻¹ * W.a₁), 0, C (C <| W_X⁻¹ * -1), _⟩
    rw [← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hx]
    simp only [mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel hx]
    run_tac
      C_simp
    ring1
  · let W_Y := 2 * y₁ + W.a₁ * x₁ + W.a₃
    refine' ⟨0, C (C W_Y⁻¹), C (C <| W_Y⁻¹ * -1), 0, _⟩
    rw [neg_Y, ← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hy]
    simp only [mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel hy]
    run_tac
      C_simp
    ring1
#align weierstrass_curve.XY_ideal_neg_mul WeierstrassCurve.xYIdeal_neg_mul

private theorem XY_ideal'_mul_inv :
    (XYIdeal W x₁ (C y₁) : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
        (XYIdeal W x₁ (C <| W.negY x₁ y₁) * (XIdeal W x₁)⁻¹) =
      1 := by
  rw [← mul_assoc, ← FractionalIdeal.coeIdeal_mul, mul_comm <| XY_ideal W _ _, XY_ideal_neg_mul h₁,
    X_ideal,
    FractionalIdeal.coe_ideal_span_singleton_mul_inv W.function_field <| X_class_ne_zero W x₁]

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1008755739.C_simp -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1008755739.C_simp -/
theorem xYIdeal_mul_xYIdeal (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    XIdeal W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) * (XYIdeal W x₁ (C y₁) * XYIdeal W x₂ (C y₂)) =
      YIdeal W (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) *
        XYIdeal W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)
          (C <| W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  have sup_rw : ∀ a b c d : Ideal W.coordinate_ring, a ⊔ (b ⊔ (c ⊔ d)) = a ⊔ d ⊔ b ⊔ c :=
    fun _ _ c _ => by rw [← sup_assoc, @sup_comm _ _ c, sup_sup_sup_comm, ← sup_assoc]
  rw [XY_ideal_add_eq, X_ideal, mul_comm, W.XY_ideal_eq₁ x₁ y₁ <| W.slope x₁ x₂ y₁ y₂, XY_ideal,
    XY_ideal_eq₂ h₁' h₂' hxy, XY_ideal, span_pair_mul_span_pair]
  simp_rw [span_insert, sup_rw, sup_mul, span_singleton_mul_span_singleton]
  rw [← neg_eq_iff_eq_neg.mpr <| coordinate_ring.C_add_polynomial_slope h₁' h₂' hxy,
    span_singleton_neg, coordinate_ring.C_add_polynomial, _root_.map_mul, Y_class]
  simp_rw [mul_comm <| X_class W x₁, mul_assoc, ← span_singleton_mul_span_singleton, ← mul_sup]
  rw [span_singleton_mul_span_singleton, ← span_insert, ←
    span_pair_add_mul_right <| -(X_class W <| W.add_X x₁ x₂ <| W.slope x₁ x₂ y₁ y₂), mul_neg, ←
    sub_eq_add_neg, ← sub_mul, ← map_sub, sub_sub_sub_cancel_right, span_insert, ←
    span_singleton_mul_span_singleton, ← sup_rw, ← sup_mul, ← sup_mul]
  apply congr_arg (_ ∘ _)
  convert top_mul _
  simp_rw [X_class, ← @Set.image_singleton _ _ <| AdjoinRoot.mk _, ← map_span, ← Ideal.map_sup,
    eq_top_iff_one, mem_map_iff_of_surjective _ <| AdjoinRoot.mk_surjective W.monic_polynomial, ←
    span_insert, mem_span_insert', mem_span_singleton']
  by_cases hx : x₁ = x₂
  · rcases hx, Y_eq_of_Y_ne h₁' h₂' hx (hxy hx) with ⟨rfl, rfl⟩
    let y := (y₁ - W.neg_Y x₁ y₁) ^ 2
    replace hxy := pow_ne_zero 2 (sub_ne_zero_of_ne <| hxy rfl)
    refine'
      ⟨1 + C (C <| y⁻¹ * 4) * W.polynomial,
        ⟨C <| C y⁻¹ * (C 4 * X ^ 2 + C (4 * x₁ + W.b₂) * X + C (4 * x₁ ^ 2 + W.b₂ * x₁ + 2 * W.b₄)),
          0, C (C y⁻¹) * (Y - W.neg_polynomial), _⟩, by
        rw [map_add, map_one, _root_.map_mul, AdjoinRoot.mk_self, MulZeroClass.mul_zero, add_zero]⟩
    rw [WeierstrassCurve.polynomial, neg_polynomial, ←
      mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hxy]
    simp only [mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel hxy]
    linear_combination (norm :=
      (rw [b₂, b₄, neg_Y];
        run_tac
          C_simp;
        ring1))
      -4 * congr_arg C (congr_arg C <| (W.equation_iff _ _).mp h₁')
  · replace hx := sub_ne_zero_of_ne hx
    refine' ⟨_, ⟨⟨C <| C (x₁ - x₂)⁻¹, C <| C <| (x₁ - x₂)⁻¹ * -1, 0, _⟩, map_one _⟩⟩
    rw [← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hx]
    simp only [← mul_assoc, mul_add, ← C_mul, mul_inv_cancel hx]
    run_tac
      C_simp
    ring1
#align weierstrass_curve.XY_ideal_mul_XY_ideal WeierstrassCurve.xYIdeal_mul_xYIdeal

/-- The non-zero fractional ideal $\langle X - x, Y - y \rangle$ of $F(W)$ for some $x, y \in F$. -/
@[simp]
noncomputable def xYIdeal' : (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ :=
  Units.mkOfMulEqOne _ _ <| XY_ideal'_mul_inv h₁
#align weierstrass_curve.XY_ideal' WeierstrassCurve.xYIdeal'

theorem xYIdeal'_eq :
    (xYIdeal' h₁ : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = XYIdeal W x₁ (C y₁) :=
  rfl
#align weierstrass_curve.XY_ideal'_eq WeierstrassCurve.xYIdeal'_eq

theorem mk_xYIdeal'_mul_mk_xYIdeal'_of_Y_eq :
    ClassGroup.mk (xYIdeal' <| nonsingular_neg h₁) * ClassGroup.mk (xYIdeal' h₁) = 1 := by
  rw [← _root_.map_mul]
  exact
    (ClassGroup.mk_eq_one_of_coe_ideal <|
          (FractionalIdeal.coeIdeal_mul _ _).symm.trans
            (fractional_ideal.coe_ideal_inj.mpr <| XY_ideal_neg_mul h₁)).mpr
      ⟨_, X_class_ne_zero W _, rfl⟩
#align weierstrass_curve.mk_XY_ideal'_mul_mk_XY_ideal'_of_Y_eq WeierstrassCurve.mk_xYIdeal'_mul_mk_xYIdeal'_of_Y_eq

theorem mk_xYIdeal'_mul_mk_xYIdeal' (hxy : x₁ = x₂ → y₁ ≠ W.negY x₂ y₂) :
    ClassGroup.mk (xYIdeal' h₁) * ClassGroup.mk (xYIdeal' h₂) =
      ClassGroup.mk (xYIdeal' <| nonsingular_add h₁ h₂ hxy) := by
  rw [← _root_.map_mul]
  exact
    (ClassGroup.mk_eq_mk_of_coe_ideal (FractionalIdeal.coeIdeal_mul _ _).symm <| XY_ideal'_eq _).mpr
      ⟨_, _, X_class_ne_zero W _, Y_class_ne_zero W _, XY_ideal_mul_XY_ideal h₁.left h₂.left hxy⟩
#align weierstrass_curve.mk_XY_ideal'_mul_mk_XY_ideal' WeierstrassCurve.mk_xYIdeal'_mul_mk_xYIdeal'

namespace Point

/-- The set function mapping an affine point $(x, y)$ of `W` to the class of the non-zero fractional
ideal $\langle X - x, Y - y \rangle$ of $F(W)$ in the class group of $F[W]$. -/
@[simp]
noncomputable def toClassFun : W.Point → Additive (ClassGroup W.CoordinateRing)
  | 0 => 0
  | some h => Additive.ofMul <| ClassGroup.mk <| xYIdeal' h
#align weierstrass_curve.point.to_class_fun WeierstrassCurve.Point.toClassFun

/-- The group homomorphism mapping an affine point $(x, y)$ of `W` to the class of the non-zero
fractional ideal $\langle X - x, Y - y \rangle$ of $F(W)$ in the class group of $F[W]$. -/
@[simps]
noncomputable def toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing) where
  toFun := toClassFun
  map_zero' := rfl
  map_add' := by
    rintro (_ | @⟨x₁, y₁, h₁⟩) (_ | @⟨x₂, y₂, h₂⟩)
    any_goals simp only [zero_def, to_class_fun, _root_.zero_add, _root_.add_zero]
    by_cases hx : x₁ = x₂
    · by_cases hy : y₁ = W.neg_Y x₂ y₂
      · substs hx hy
        simpa only [some_add_some_of_Y_eq rfl rfl] using
          (mk_XY_ideal'_mul_mk_XY_ideal'_of_Y_eq h₂).symm
      ·
        simpa only [some_add_some_of_Y_ne hx hy] using
          (mk_XY_ideal'_mul_mk_XY_ideal' h₁ h₂ fun _ => hy).symm
    ·
      simpa only [some_add_some_of_X_ne hx] using
        (mk_XY_ideal'_mul_mk_XY_ideal' h₁ h₂ fun h => (hx h).elim).symm
#align weierstrass_curve.point.to_class WeierstrassCurve.Point.toClass

@[simp]
theorem toClass_zero : toClass (0 : W.Point) = 0 :=
  rfl
#align weierstrass_curve.point.to_class_zero WeierstrassCurve.Point.toClass_zero

theorem toClass_some : toClass (some h₁) = ClassGroup.mk (xYIdeal' h₁) :=
  rfl
#align weierstrass_curve.point.to_class_some WeierstrassCurve.Point.toClass_some

@[simp]
theorem add_eq_zero (P Q : W.Point) : P + Q = 0 ↔ P = -Q := by
  rcases P, Q with ⟨_ | @⟨x₁, y₁, _⟩, _ | @⟨x₂, y₂, _⟩⟩
  any_goals rfl
  · rw [zero_def, zero_add, ← neg_eq_iff_eq_neg, neg_zero, eq_comm]
  · simp only [neg_some]
    constructor
    · intro h
      by_cases hx : x₁ = x₂
      · by_cases hy : y₁ = W.neg_Y x₂ y₂
        · exact ⟨hx, hy⟩
        · rw [some_add_some_of_Y_ne hx hy] at h
          contradiction
      · rw [some_add_some_of_X_ne hx] at h
        contradiction
    · exact fun ⟨hx, hy⟩ => some_add_some_of_Y_eq hx hy
#align weierstrass_curve.point.add_eq_zero WeierstrassCurve.Point.add_eq_zero

@[simp]
theorem add_left_neg (P : W.Point) : -P + P = 0 := by rw [add_eq_zero]
#align weierstrass_curve.point.add_left_neg WeierstrassCurve.Point.add_left_neg

@[simp]
theorem neg_add_eq_zero (P Q : W.Point) : -P + Q = 0 ↔ P = Q := by rw [add_eq_zero, neg_inj]
#align weierstrass_curve.point.neg_add_eq_zero WeierstrassCurve.Point.neg_add_eq_zero

theorem toClass_eq_zero (P : W.Point) : toClass P = 0 ↔ P = 0 :=
  ⟨by
    intro hP
    rcases P with (_ | @⟨_, _, ⟨h, _⟩⟩)
    · rfl
    · rcases(ClassGroup.mk_eq_one_of_coe_ideal <| by rfl).mp hP with ⟨p, h0, hp⟩
      apply (p.nat_degree_norm_ne_one _).elim
      rw [← finrank_quotient_span_eq_natDegree_norm W.CoordinateRing.Basis h0, ←
        (quotient_equiv_alg_of_eq F hp).toLinearEquiv.finrank_eq,
        (quotient_XY_ideal_equiv W h).toLinearEquiv.finrank_eq, FiniteDimensional.finrank_self],
    congr_arg toClass⟩
#align weierstrass_curve.point.to_class_eq_zero WeierstrassCurve.Point.toClass_eq_zero

theorem toClass_injective : Function.Injective <| @toClass _ _ W := by
  rintro (_ | h) _ hP
  all_goals rw [← neg_add_eq_zero, ← to_class_eq_zero, map_add, ← hP]
  · exact zero_add 0
  · exact mk_XY_ideal'_mul_mk_XY_ideal'_of_Y_eq h
#align weierstrass_curve.point.to_class_injective WeierstrassCurve.Point.toClass_injective

theorem add_comm (P Q : W.Point) : P + Q = Q + P :=
  toClass_injective <| by simp only [map_add, add_comm]
#align weierstrass_curve.point.add_comm WeierstrassCurve.Point.add_comm

theorem add_assoc (P Q R : W.Point) : P + Q + R = P + (Q + R) :=
  toClass_injective <| by simp only [map_add, add_assoc]
#align weierstrass_curve.point.add_assoc WeierstrassCurve.Point.add_assoc

noncomputable instance : AddCommGroup W.Point where
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
    · by_cases hy : y₁ = (W.base_change F).negY x₂ y₂
      · simp only [some_add_some_of_Y_eq hx hy, of_base_change_fun]
        rw [some_add_some_of_Y_eq <| congr_arg _ hx]
        · rw [hy, base_change_neg_Y_of_base_change]
      · simp only [some_add_some_of_Y_ne hx hy, of_base_change_fun]
        rw [some_add_some_of_Y_ne <| congr_arg _ hx]
        · simp only [base_change_add_X_of_base_change, base_change_add_Y_of_base_change,
            base_change_slope_of_base_change]
          exact ⟨rfl, rfl⟩
        · rw [base_change_neg_Y_of_base_change]
          contrapose! hy
          exact NoZeroSMulDivisors.algebraMap_injective F K hy
    · simp only [some_add_some_of_X_ne hx, of_base_change_fun]
      rw [some_add_some_of_X_ne]
      · simp only [base_change_add_X_of_base_change, base_change_add_Y_of_base_change,
          base_change_slope_of_base_change]
        exact ⟨rfl, rfl⟩
      · contrapose! hx
        exact NoZeroSMulDivisors.algebraMap_injective F K hx
#align weierstrass_curve.point.of_base_change WeierstrassCurve.Point.ofBaseChange

theorem ofBaseChange_injective : Function.Injective <| ofBaseChange W F K := by
  rintro (_ | _) (_ | _) h
  · rfl
  any_goals contradiction
  simp only
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
