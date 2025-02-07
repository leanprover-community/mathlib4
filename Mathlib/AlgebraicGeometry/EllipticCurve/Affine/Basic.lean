/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# Equations and nonsingularity of Weierstrass curves in affine coordinates

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

 * `WeierstrassCurve.Affine.Equation`: the Weierstrass equation of an affine Weierstrass curve.
 * `WeierstrassCurve.Affine.Nonsingular`: the nonsingular condition on an affine Weierstrass curve.

## Main statements

 * `WeierstrassCurve.Affine.equation_iff_nonsingular`: an elliptic curve in affine coordinates is
    nonsingular at every point.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, affine coordinates
-/

open Polynomial

open scoped Polynomial.Bivariate

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow, evalEval])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀,
    Polynomial.map_ofNat, map_C, map_X, Polynomial.map_neg, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_div, coe_mapRingHom,
    WeierstrassCurve.map])

universe r s u v

/-! ## Weierstrass curves -/

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A : Type u} {B : Type v}

variable (R) in
/-- An abbreviation for a Weierstrass curve in affine  coordinates. -/
abbrev Affine : Type r :=
  WeierstrassCurve R

/-- The coercion to a Weierstrass curve in affine coordinates. -/
abbrev toAffine (W : WeierstrassCurve R) : Affine R :=
  W

namespace Affine

variable [CommRing R] [CommRing S] [CommRing A] [CommRing B] {W : Affine R}

section Equation

/-! ### Weierstrass equations -/

variable (W) in
/-- The polynomial `W(X, Y) := Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` associated to a Weierstrass
curve `W` over `R`. For ease of polynomial manipulation, this is represented as a term of type
`R[X][X]`, where the inner variable represents `X` and the outer variable represents `Y`. For
clarity, the alternative notations `Y` and `R[X][Y]` are provided in the `Polynomial.Bivariate`
scope to represent the outer variable and the bivariate polynomial ring `R[X][X]` respectively. -/
noncomputable def polynomial : R[X][Y] :=
  Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y - C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)

lemma polynomial_eq : W.polynomial = Cubic.toPoly
    ⟨0, 1, Cubic.toPoly ⟨0, 0, W.a₁, W.a₃⟩, Cubic.toPoly ⟨-1, -W.a₂, -W.a₄, -W.a₆⟩⟩ := by
  simp_rw [polynomial, Cubic.toPoly]
  map_simp
  simp only [C_0, C_1]
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
  rcases (monic_polynomial.not_irreducible_iff_exists_add_mul_eq_coeff natDegree_polynomial).mp h
    with ⟨f, g, h0, h1⟩
  simp only [polynomial_eq, Cubic.coeff_eq_c, Cubic.coeff_eq_d] at h0 h1
  apply_fun degree at h0 h1
  rw [Cubic.degree_of_a_ne_zero' <| neg_ne_zero.mpr <| one_ne_zero' R, degree_mul] at h0
  apply (h1.symm.le.trans Cubic.degree_of_b_eq_zero').not_lt
  rcases Nat.WithBot.add_eq_three_iff.mp h0.symm with h | h | h | h
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

variable (W) in
/-- The proposition that an affine point `(x, y)` lies in `W`. In other words, `W(x, y) = 0`. -/
def Equation (x y : R) : Prop :=
  W.polynomial.evalEval x y = 0

lemma equation_iff' (x y : R) : W.Equation x y ↔
    y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
  rw [Equation, evalEval_polynomial]

lemma equation_iff (x y : R) : W.Equation x y ↔
    y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
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

variable (W) in
/-- The partial derivative `W_X(X, Y)` of `W(X, Y)` with respect to `X`. -/
-- TODO: define this in terms of `Polynomial.derivative`.
noncomputable def polynomialX : R[X][Y] :=
  C (C W.a₁) * Y - C (C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄)

lemma evalEval_polynomialX (x y : R) :
    W.polynomialX.evalEval x y = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) := by
  simp only [polynomialX]
  eval_simp

@[simp]
lemma evalEval_polynomialX_zero : W.polynomialX.evalEval 0 0 = -W.a₄ := by
  simp only [evalEval_polynomialX, zero_add, zero_sub, mul_zero, zero_pow <| Nat.succ_ne_zero _]

variable (W) in
/-- The partial derivative `W_Y(X, Y)` of `W(X, Y)` with respect to `Y`. -/
-- TODO: define this in terms of `Polynomial.derivative`.
noncomputable def polynomialY : R[X][Y] :=
  C (C 2) * Y + C (C W.a₁ * X + C W.a₃)

lemma evalEval_polynomialY (x y : R) : W.polynomialY.evalEval x y = 2 * y + W.a₁ * x + W.a₃ := by
  simp only [polynomialY]
  eval_simp
  rw [← add_assoc]

@[simp]
lemma evalEval_polynomialY_zero : W.polynomialY.evalEval 0 0 = W.a₃ := by
  simp only [evalEval_polynomialY, zero_add, mul_zero]

variable (W) in
/-- The proposition that an affine point `(x, y)` in `W` is nonsingular. In other words, either
`W_X(x, y) ≠ 0` or `W_Y(x, y) ≠ 0`.

Note that this definition is only mathematically accurate for fields. -/
-- TODO: generalise this definition to be mathematically accurate for a larger class of rings.
def Nonsingular (x y : R) : Prop :=
  W.Equation x y ∧ (W.polynomialX.evalEval x y ≠ 0 ∨ W.polynomialY.evalEval x y ≠ 0)

lemma nonsingular_iff' (x y : R) : W.Nonsingular x y ↔ W.Equation x y ∧
    (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 ∨ 2 * y + W.a₁ * x + W.a₃ ≠ 0) := by
  rw [Nonsingular, equation_iff', evalEval_polynomialX, evalEval_polynomialY]

lemma nonsingular_iff (x y : R) : W.Nonsingular x y ↔ W.Equation x y ∧
    (W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∨ y ≠ -y - W.a₁ * x - W.a₃) := by
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

lemma equation_zero_iff_nonsingular_zero_of_Δ_ne_zero (hΔ : W.Δ ≠ 0) :
    W.Equation 0 0 ↔ W.Nonsingular 0 0 := by
  simp only [equation_zero, nonsingular_zero, iff_self_and]
  contrapose! hΔ
  simp only [b₂, b₄, b₆, b₈, Δ, hΔ]
  ring1

/-- A Weierstrass curve is nonsingular at every point if its discriminant is non-zero. -/
lemma equation_iff_nonsingular_of_Δ_ne_zero {x y : R} (hΔ : W.Δ ≠ 0) :
    W.Equation x y ↔ W.Nonsingular x y := by
  rw [equation_iff_variableChange, nonsingular_iff_variableChange,
    equation_zero_iff_nonsingular_zero_of_Δ_ne_zero <| by
      rwa [variableChange_Δ, inv_one, Units.val_one, one_pow, one_mul]]

/-- An elliptic curve is nonsingular at every point. -/
lemma equation_iff_nonsingular [Nontrivial R] [W.IsElliptic] {x y : R} :
    W.toAffine.Equation x y ↔ W.toAffine.Nonsingular x y :=
  W.toAffine.equation_iff_nonsingular_of_Δ_ne_zero <| W.coe_Δ' ▸ W.Δ'.ne_zero

@[deprecated (since := "2025-02-01")] alias nonsingular_zero_of_Δ_ne_zero :=
  equation_zero_iff_nonsingular_zero_of_Δ_ne_zero
@[deprecated (since := "2025-02-01")] alias nonsingular_of_Δ_ne_zero :=
  equation_iff_nonsingular_of_Δ_ne_zero
@[deprecated (since := "2025-02-01")] alias nonsingular := equation_iff_nonsingular

end Nonsingular

section Map

/-! ### Maps and base changes -/

variable (f : R →+* S) (x y : R)

lemma map_polynomial : (W.map f).toAffine.polynomial = W.polynomial.map (mapRingHom f) := by
  simp only [polynomial]
  map_simp

variable {x y} in
lemma Equation.map {x y : R} (h : W.Equation x y) : (W.map f).toAffine.Equation (f x) (f y) := by
  rw [Equation, map_polynomial, map_mapRingHom_evalEval, h, map_zero]

variable {f} in
lemma map_equation (hf : Function.Injective f) :
    (W.map f).toAffine.Equation (f x) (f y) ↔ W.Equation x y := by
  simp only [Equation, map_polynomial, map_mapRingHom_evalEval, map_eq_zero_iff f hf]

lemma map_polynomialX : (W.map f).toAffine.polynomialX = W.polynomialX.map (mapRingHom f) := by
  simp only [polynomialX]
  map_simp

lemma map_polynomialY : (W.map f).toAffine.polynomialY = W.polynomialY.map (mapRingHom f) := by
  simp only [polynomialY]
  map_simp

variable {f} in
lemma map_nonsingular (hf : Function.Injective f) :
    (W.map f).toAffine.Nonsingular (f x) (f y) ↔ W.Nonsingular x y := by
  simp only [Nonsingular, evalEval, map_equation _ _ hf, map_polynomialX, map_polynomialY,
    map_mapRingHom_evalEval, map_ne_zero_iff f hf]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A →ₐ[S] B) (x y : A)

lemma baseChange_polynomial : (W.baseChange B).toAffine.polynomial =
    (W.baseChange A).toAffine.polynomial.map (mapRingHom f) := by
  rw [← map_polynomial, map_baseChange]

lemma eval_baseChange_polynomial :
    (W.baseChange R[X][Y]).toAffine.polynomial.evalEval (C X) Y = W.polynomial := by
  rw [map_polynomial, evalEval, eval_map, eval_C_X_eval₂_map_C_X]

@[deprecated (since := "2025-02-01")] alias evalEval_baseChange_polynomial_X_Y :=
  eval_baseChange_polynomial

variable {x y} in
lemma Equation.baseChange (h : (W.baseChange A).toAffine.Equation x y) :
    (W.baseChange B).toAffine.Equation (f x) (f y) := by
  convert Equation.map f.toRingHom h using 1
  rw [AlgHom.toRingHom_eq_coe, map_baseChange]

variable {f} in
lemma baseChange_equation (hf : Function.Injective f) :
    (W.baseChange B).toAffine.Equation (f x) (f y) ↔ (W.baseChange A).toAffine.Equation x y := by
  rw [← map_equation _ _ hf, AlgHom.toRingHom_eq_coe, map_baseChange, RingHom.coe_coe]

lemma baseChange_polynomialX : (W.baseChange B).toAffine.polynomialX =
    (W.baseChange A).toAffine.polynomialX.map (mapRingHom f) := by
  rw [← map_polynomialX, map_baseChange]

lemma baseChange_polynomialY : (W.baseChange B).toAffine.polynomialY =
    (W.baseChange A).toAffine.polynomialY.map (mapRingHom f) := by
  rw [← map_polynomialY, map_baseChange]

variable {f} in
lemma baseChange_nonsingular (hf : Function.Injective f) :
    (W.baseChange B).toAffine.Nonsingular (f x) (f y) ↔
      (W.baseChange A).toAffine.Nonsingular x y := by
  rw [← map_nonsingular _ _ hf, AlgHom.toRingHom_eq_coe, map_baseChange, RingHom.coe_coe]

end Map

end Affine

end WeierstrassCurve
