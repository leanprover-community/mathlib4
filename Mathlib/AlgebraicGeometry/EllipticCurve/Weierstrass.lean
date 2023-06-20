/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata

! This file was ported from Lean 3 source module algebraic_geometry.elliptic_curve.weierstrass
! leanprover-community/mathlib commit e2e7f2ac359e7514e4d40061d7c08bb69487ba4e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CubicDiscriminant
import Mathbin.RingTheory.Norm
import Mathbin.Tactic.LinearCombination

/-!
# Weierstrass equations of elliptic curves

This file defines the structure of an elliptic curve as a nonsingular Weierstrass curve given by a
Weierstrass equation, which is mathematically accurate in many cases but also good for computation.

## Mathematical background

Let `S` be a scheme. The actual category of elliptic curves over `S` is a large category, whose
objects are schemes `E` equipped with a map `E → S`, a section `S → E`, and some axioms (the map
is smooth and proper and the fibres are geometrically-connected one-dimensional group varieties). In
the special case where `S` is the spectrum of some commutative ring `R` whose Picard group is zero
(this includes all fields, all PIDs, and many other commutative rings) it can be shown (using a lot
of algebro-geometric machinery) that every elliptic curve `E` is a projective plane cubic isomorphic
to a Weierstrass curve given by the equation $Y^2 + a_1XY + a_3Y = X^3 + a_2X^2 + a_4X + a_6$ for
some $a_i$ in `R`, and such that a certain quantity called the discriminant of `E` is a unit in `R`.
If `R` is a field, this quantity divides the discriminant of a cubic polynomial whose roots over a
splitting field of `R` are precisely the $X$-coordinates of the non-zero 2-torsion points of `E`.

## Main definitions

 * `weierstrass_curve`: a Weierstrass curve over a commutative ring.
 * `weierstrass_curve.Δ`: the discriminant of a Weierstrass curve.
 * `weierstrass_curve.variable_change`: the Weierstrass curve induced by a change of variables.
 * `weierstrass_curve.base_change`: the Weierstrass curve base changed over an algebra.
 * `weierstrass_curve.two_torsion_polynomial`: the 2-torsion polynomial of a Weierstrass curve.
 * `weierstrass_curve.polynomial`: the polynomial associated to a Weierstrass curve.
 * `weierstrass_curve.equation`: the Weirstrass equation of a Weierstrass curve.
 * `weierstrass_curve.nonsingular`: the nonsingular condition at a point on a Weierstrass curve.
 * `weierstrass_curve.coordinate_ring`: the coordinate ring of a Weierstrass curve.
 * `weierstrass_curve.function_field`: the function field of a Weierstrass curve.
 * `weierstrass_curve.coordinate_ring.basis`: the power basis of the coordinate ring over `R[X]`.
 * `elliptic_curve`: an elliptic curve over a commutative ring.
 * `elliptic_curve.j`: the j-invariant of an elliptic curve.

## Main statements

 * `weierstrass_curve.two_torsion_polynomial_disc`: the discriminant of a Weierstrass curve is a
    constant factor of the cubic discriminant of its 2-torsion polynomial.
 * `weierstrass_curve.nonsingular_of_Δ_ne_zero`: a Weierstrass curve is nonsingular at every point
    if its discriminant is non-zero.
 * `weierstrass_curve.coordinate_ring.is_domain`: the coordinate ring of a Weierstrass curve is
    an integral domain.
 * `weierstrass_curve.coordinate_ring.degree_norm_smul_basis`: the degree of the norm of an element
    in the coordinate ring in terms of the power basis.
 * `elliptic_curve.nonsingular`: an elliptic curve is nonsingular at every point.
 * `elliptic_curve.variable_change_j`: the j-invariant of an elliptic curve is invariant under an
    admissible linear change of variables.

## Implementation notes

The definition of elliptic curves in this file makes sense for all commutative rings `R`, but it
only gives a type which can be beefed up to a category which is equivalent to the category of
elliptic curves over the spectrum $\mathrm{Spec}(R)$ of `R` in the case that `R` has trivial Picard
group $\mathrm{Pic}(R)$ or, slightly more generally, when its 12-torsion is trivial. The issue is
that for a general ring `R`, there might be elliptic curves over $\mathrm{Spec}(R)$ in the sense of
algebraic geometry which are not globally defined by a cubic equation valid over the entire base.

## References

 * [N Katz and B Mazur, *Arithmetic Moduli of Elliptic Curves*][katz_mazur]
 * [P Deligne, *Courbes Elliptiques: Formulaire (d'après J. Tate)*][deligne_formulaire]
 * [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, j invariant
-/


/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def map_simp : tactic Unit :=
  sorry

/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def eval_simp : tactic Unit :=
  sorry

/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def C_simp : tactic Unit :=
  sorry

universe u v w

variable {R : Type u}

/-! ## Weierstrass curves -/


/-- A Weierstrass curve $Y^2 + a_1XY + a_3Y = X^3 + a_2X^2 + a_4X + a_6$ with parameters $a_i$. -/
@[ext]
structure WeierstrassCurve (R : Type u) where
  (a₁ a₂ a₃ a₄ a₆ : R)
#align weierstrass_curve WeierstrassCurve

instance [Inhabited R] : Inhabited <| WeierstrassCurve R :=
  ⟨⟨default, default, default, default, default⟩⟩

namespace WeierstrassCurve

variable [CommRing R] (W : WeierstrassCurve R)

section Quantity

/-! ### Standard quantities -/


/-- The `b₂` coefficient of a Weierstrass curve. -/
@[simp]
def b₂ : R :=
  W.a₁ ^ 2 + 4 * W.a₂
#align weierstrass_curve.b₂ WeierstrassCurve.b₂

/-- The `b₄` coefficient of a Weierstrass curve. -/
@[simp]
def b₄ : R :=
  2 * W.a₄ + W.a₁ * W.a₃
#align weierstrass_curve.b₄ WeierstrassCurve.b₄

/-- The `b₆` coefficient of a Weierstrass curve. -/
@[simp]
def b₆ : R :=
  W.a₃ ^ 2 + 4 * W.a₆
#align weierstrass_curve.b₆ WeierstrassCurve.b₆

/-- The `b₈` coefficient of a Weierstrass curve. -/
@[simp]
def b₈ : R :=
  W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2
#align weierstrass_curve.b₈ WeierstrassCurve.b₈

theorem b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by simp only [b₂, b₄, b₆, b₈]; ring1
#align weierstrass_curve.b_relation WeierstrassCurve.b_relation

/-- The `c₄` coefficient of a Weierstrass curve. -/
@[simp]
def c₄ : R :=
  W.b₂ ^ 2 - 24 * W.b₄
#align weierstrass_curve.c₄ WeierstrassCurve.c₄

/-- The `c₆` coefficient of a Weierstrass curve. -/
@[simp]
def c₆ : R :=
  -W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 216 * W.b₆
#align weierstrass_curve.c₆ WeierstrassCurve.c₆

/-- The discriminant `Δ` of a Weierstrass curve. If `R` is a field, then this polynomial vanishes
if and only if the cubic curve cut out by this equation is singular. Sometimes only defined up to
sign in the literature; we choose the sign used by the LMFDB. For more discussion, see
[the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant). -/
@[simp]
def Δ : R :=
  -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆
#align weierstrass_curve.Δ WeierstrassCurve.Δ

theorem c_relation : 1728 * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2 := by simp only [b₂, b₄, b₆, b₈, c₄, c₆, Δ];
  ring1
#align weierstrass_curve.c_relation WeierstrassCurve.c_relation

end Quantity

section VariableChange

/-! ### Variable changes -/


variable (u : Rˣ) (r s t : R)

/-- The Weierstrass curve over `R` induced by an admissible linear change of variables
$(X, Y) \mapsto (u^2X + r, u^3Y + u^2sX + t)$ for some $u \in R^\times$ and some $r, s, t \in R$. -/
@[simps]
def variableChange : WeierstrassCurve R
    where
  a₁ := ↑u⁻¹ * (W.a₁ + 2 * s)
  a₂ := ↑u⁻¹ ^ 2 * (W.a₂ - s * W.a₁ + 3 * r - s ^ 2)
  a₃ := ↑u⁻¹ ^ 3 * (W.a₃ + r * W.a₁ + 2 * t)
  a₄ := ↑u⁻¹ ^ 4 * (W.a₄ - s * W.a₃ + 2 * r * W.a₂ - (t + r * s) * W.a₁ + 3 * r ^ 2 - 2 * s * t)
  a₆ := ↑u⁻¹ ^ 6 * (W.a₆ + r * W.a₄ + r ^ 2 * W.a₂ + r ^ 3 - t * W.a₃ - t ^ 2 - r * t * W.a₁)
#align weierstrass_curve.variable_change WeierstrassCurve.variableChange

@[simp]
theorem variableChange_b₂ : (W.variableChange u r s t).b₂ = ↑u⁻¹ ^ 2 * (W.b₂ + 12 * r) := by
  simp only [b₂, variable_change_a₁, variable_change_a₂]; ring1
#align weierstrass_curve.variable_change_b₂ WeierstrassCurve.variableChange_b₂

@[simp]
theorem variableChange_b₄ :
    (W.variableChange u r s t).b₄ = ↑u⁻¹ ^ 4 * (W.b₄ + r * W.b₂ + 6 * r ^ 2) := by
  simp only [b₂, b₄, variable_change_a₁, variable_change_a₃, variable_change_a₄]; ring1
#align weierstrass_curve.variable_change_b₄ WeierstrassCurve.variableChange_b₄

@[simp]
theorem variableChange_b₆ :
    (W.variableChange u r s t).b₆ = ↑u⁻¹ ^ 6 * (W.b₆ + 2 * r * W.b₄ + r ^ 2 * W.b₂ + 4 * r ^ 3) :=
  by simp only [b₂, b₄, b₆, variable_change_a₃, variable_change_a₆]; ring1
#align weierstrass_curve.variable_change_b₆ WeierstrassCurve.variableChange_b₆

@[simp]
theorem variableChange_b₈ :
    (W.variableChange u r s t).b₈ =
      ↑u⁻¹ ^ 8 * (W.b₈ + 3 * r * W.b₆ + 3 * r ^ 2 * W.b₄ + r ^ 3 * W.b₂ + 3 * r ^ 4) :=
  by
  simp only [b₂, b₄, b₆, b₈, variable_change_a₁, variable_change_a₂, variable_change_a₃,
    variable_change_a₄, variable_change_a₆]
  ring1
#align weierstrass_curve.variable_change_b₈ WeierstrassCurve.variableChange_b₈

@[simp]
theorem variableChange_c₄ : (W.variableChange u r s t).c₄ = ↑u⁻¹ ^ 4 * W.c₄ := by
  simp only [c₄, variable_change_b₂, variable_change_b₄]; ring1
#align weierstrass_curve.variable_change_c₄ WeierstrassCurve.variableChange_c₄

@[simp]
theorem variableChange_c₆ : (W.variableChange u r s t).c₆ = ↑u⁻¹ ^ 6 * W.c₆ := by
  simp only [c₆, variable_change_b₂, variable_change_b₄, variable_change_b₆]; ring1
#align weierstrass_curve.variable_change_c₆ WeierstrassCurve.variableChange_c₆

@[simp]
theorem variableChange_Δ : (W.variableChange u r s t).Δ = ↑u⁻¹ ^ 12 * W.Δ := by dsimp; ring1
#align weierstrass_curve.variable_change_Δ WeierstrassCurve.variableChange_Δ

end VariableChange

variable (A : Type v) [CommRing A] [Algebra R A] (B : Type w) [CommRing B] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

section BaseChange

/-! ### Base changes -/


/-- The Weierstrass curve over `R` base changed to `A`. -/
@[simps]
def baseChange : WeierstrassCurve A :=
  ⟨algebraMap R A W.a₁, algebraMap R A W.a₂, algebraMap R A W.a₃, algebraMap R A W.a₄,
    algebraMap R A W.a₆⟩
#align weierstrass_curve.base_change WeierstrassCurve.baseChange

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2242074953.map_simp -/
@[simp]
theorem baseChange_b₂ : (W.base_change A).b₂ = algebraMap R A W.b₂ := by
  simp only [b₂, base_change_a₁, base_change_a₂];
  run_tac
    map_simp
#align weierstrass_curve.base_change_b₂ WeierstrassCurve.baseChange_b₂

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2242074953.map_simp -/
@[simp]
theorem baseChange_b₄ : (W.base_change A).b₄ = algebraMap R A W.b₄ := by
  simp only [b₄, base_change_a₁, base_change_a₃, base_change_a₄];
  run_tac
    map_simp
#align weierstrass_curve.base_change_b₄ WeierstrassCurve.baseChange_b₄

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2242074953.map_simp -/
@[simp]
theorem baseChange_b₆ : (W.base_change A).b₆ = algebraMap R A W.b₆ := by
  simp only [b₆, base_change_a₃, base_change_a₆];
  run_tac
    map_simp
#align weierstrass_curve.base_change_b₆ WeierstrassCurve.baseChange_b₆

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2242074953.map_simp -/
@[simp]
theorem baseChange_b₈ : (W.base_change A).b₈ = algebraMap R A W.b₈ :=
  by
  simp only [b₈, base_change_a₁, base_change_a₂, base_change_a₃, base_change_a₄, base_change_a₆]
  run_tac
    map_simp
#align weierstrass_curve.base_change_b₈ WeierstrassCurve.baseChange_b₈

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2242074953.map_simp -/
@[simp]
theorem baseChange_c₄ : (W.base_change A).c₄ = algebraMap R A W.c₄ := by
  simp only [c₄, base_change_b₂, base_change_b₄];
  run_tac
    map_simp
#align weierstrass_curve.base_change_c₄ WeierstrassCurve.baseChange_c₄

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2242074953.map_simp -/
@[simp]
theorem baseChange_c₆ : (W.base_change A).c₆ = algebraMap R A W.c₆ := by
  simp only [c₆, base_change_b₂, base_change_b₄, base_change_b₆];
  run_tac
    map_simp
#align weierstrass_curve.base_change_c₆ WeierstrassCurve.baseChange_c₆

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2242074953.map_simp -/
@[simp, nolint simp_nf]
theorem baseChange_Δ : (W.base_change A).Δ = algebraMap R A W.Δ := by
  simp only [Δ, base_change_b₂, base_change_b₄, base_change_b₆, base_change_b₈];
  run_tac
    map_simp
#align weierstrass_curve.base_change_Δ WeierstrassCurve.baseChange_Δ

theorem baseChange_self : W.base_change R = W := by ext <;> rfl
#align weierstrass_curve.base_change_self WeierstrassCurve.baseChange_self

theorem baseChange_baseChange : (W.base_change A).base_change B = W.base_change B := by
  ext <;> exact (IsScalarTower.algebraMap_apply R A B _).symm
#align weierstrass_curve.base_change_base_change WeierstrassCurve.baseChange_baseChange

end BaseChange

section TorsionPolynomial

/-! ### 2-torsion polynomials -/


/-- A cubic polynomial whose discriminant is a multiple of the Weierstrass curve discriminant. If
`W` is an elliptic curve over a field `R` of characteristic different from 2, then its roots over a
splitting field of `R` are precisely the $X$-coordinates of the non-zero 2-torsion points of `W`. -/
def twoTorsionPolynomial : Cubic R :=
  ⟨4, W.b₂, 2 * W.b₄, W.b₆⟩
#align weierstrass_curve.two_torsion_polynomial WeierstrassCurve.twoTorsionPolynomial

theorem twoTorsionPolynomial_disc : W.twoTorsionPolynomial.disc = 16 * W.Δ := by
  dsimp [two_torsion_polynomial, Cubic.disc]; ring1
#align weierstrass_curve.two_torsion_polynomial_disc WeierstrassCurve.twoTorsionPolynomial_disc

theorem twoTorsionPolynomial_disc_isUnit [Invertible (2 : R)] :
    IsUnit W.twoTorsionPolynomial.disc ↔ IsUnit W.Δ :=
  by
  rw [two_torsion_polynomial_disc, IsUnit.mul_iff, show (16 : R) = 2 ^ 4 by norm_num1]
  exact and_iff_right (isUnit_of_invertible <| 2 ^ 4)
#align weierstrass_curve.two_torsion_polynomial_disc_is_unit WeierstrassCurve.twoTorsionPolynomial_disc_isUnit

theorem twoTorsionPolynomial_disc_ne_zero [Nontrivial R] [Invertible (2 : R)] (hΔ : IsUnit W.Δ) :
    W.twoTorsionPolynomial.disc ≠ 0 :=
  (W.twoTorsionPolynomial_disc_isUnit.mpr hΔ).NeZero
#align weierstrass_curve.two_torsion_polynomial_disc_ne_zero WeierstrassCurve.twoTorsionPolynomial_disc_ne_zero

end TorsionPolynomial

scoped[PolynomialPolynomial] notation "Y" => Polynomial.X

scoped[PolynomialPolynomial] notation R "[X][Y]" => Polynomial (Polynomial R)

section Polynomial

/-! ### Weierstrass equations -/


open Polynomial

open scoped Polynomial PolynomialPolynomial

/-- The polynomial $W(X, Y) := Y^2 + a_1XY + a_3Y - (X^3 + a_2X^2 + a_4X + a_6)$ associated to a
Weierstrass curve `W` over `R`. For ease of polynomial manipulation, this is represented as a term
of type `R[X][X]`, where the inner variable represents $X$ and the outer variable represents $Y$.
For clarity, the alternative notations `Y` and `R[X][Y]` are provided in the `polynomial_polynomial`
locale to represent the outer variable and the bivariate polynomial ring `R[X][X]` respectively. -/
protected noncomputable def polynomial : R[X][Y] :=
  Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y - C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)
#align weierstrass_curve.polynomial WeierstrassCurve.polynomial

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3948480697.C_simp -/
theorem polynomial_eq :
    W.Polynomial =
      Cubic.toPoly
        ⟨0, 1, Cubic.toPoly ⟨0, 0, W.a₁, W.a₃⟩, Cubic.toPoly ⟨-1, -W.a₂, -W.a₄, -W.a₆⟩⟩ :=
  by simp only [WeierstrassCurve.polynomial, Cubic.toPoly];
  run_tac
    C_simp;
  ring1
#align weierstrass_curve.polynomial_eq WeierstrassCurve.polynomial_eq

theorem polynomial_ne_zero [Nontrivial R] : W.Polynomial ≠ 0 := by rw [polynomial_eq];
  exact Cubic.ne_zero_of_b_ne_zero one_ne_zero
#align weierstrass_curve.polynomial_ne_zero WeierstrassCurve.polynomial_ne_zero

@[simp]
theorem degree_polynomial [Nontrivial R] : W.Polynomial.degree = 2 := by rw [polynomial_eq];
  exact Cubic.degree_of_b_ne_zero' one_ne_zero
#align weierstrass_curve.degree_polynomial WeierstrassCurve.degree_polynomial

@[simp]
theorem natDegree_polynomial [Nontrivial R] : W.Polynomial.natDegree = 2 := by rw [polynomial_eq];
  exact Cubic.natDegree_of_b_ne_zero' one_ne_zero
#align weierstrass_curve.nat_degree_polynomial WeierstrassCurve.natDegree_polynomial

theorem monic_polynomial : W.Polynomial.Monic := by nontriviality R;
  simpa only [polynomial_eq] using Cubic.monic_of_b_eq_one'
#align weierstrass_curve.monic_polynomial WeierstrassCurve.monic_polynomial

theorem irreducible_polynomial [IsDomain R] : Irreducible W.Polynomial :=
  by
  by_contra h
  rcases(W.monic_polynomial.not_irreducible_iff_exists_add_mul_eq_coeff W.nat_degree_polynomial).mp
      h with
    ⟨f, g, h0, h1⟩
  simp only [polynomial_eq, Cubic.coeff_eq_c, Cubic.coeff_eq_d] at h0 h1 
  apply_fun degree at h0 h1 
  rw [Cubic.degree_of_a_ne_zero' <| neg_ne_zero.mpr <| one_ne_zero' R, degree_mul] at h0 
  apply (h1.symm.le.trans Cubic.degree_of_b_eq_zero').not_lt
  rcases nat.with_bot.add_eq_three_iff.mp h0.symm with (h | h | h | h)
  any_goals rw [degree_add_eq_left_of_degree_lt] <;> simp only [h] <;> decide
  any_goals rw [degree_add_eq_right_of_degree_lt] <;> simp only [h] <;> decide
#align weierstrass_curve.irreducible_polynomial WeierstrassCurve.irreducible_polynomial

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2480101633.eval_simp -/
@[simp]
theorem eval_polynomial (x y : R) :
    (W.Polynomial.eval <| C y).eval x =
      y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) :=
  by simp only [WeierstrassCurve.polynomial];
  run_tac
    eval_simp;
  rw [add_mul, ← add_assoc]
#align weierstrass_curve.eval_polynomial WeierstrassCurve.eval_polynomial

@[simp]
theorem eval_polynomial_zero : (W.Polynomial.eval 0).eval 0 = -W.a₆ := by
  simp only [← C_0, eval_polynomial, zero_add, zero_sub, MulZeroClass.mul_zero,
    zero_pow (Nat.zero_lt_succ _)]
#align weierstrass_curve.eval_polynomial_zero WeierstrassCurve.eval_polynomial_zero

/-- The proposition that an affine point $(x, y)$ lies in `W`. In other words, $W(x, y) = 0$. -/
def Equation (x y : R) : Prop :=
  (W.Polynomial.eval <| C y).eval x = 0
#align weierstrass_curve.equation WeierstrassCurve.Equation

theorem equation_iff' (x y : R) :
    W.Equation x y ↔
      y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
  by rw [equation, eval_polynomial]
#align weierstrass_curve.equation_iff' WeierstrassCurve.equation_iff'

@[simp]
theorem equation_iff (x y : R) :
    W.Equation x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  rw [equation_iff', sub_eq_zero]
#align weierstrass_curve.equation_iff WeierstrassCurve.equation_iff

@[simp]
theorem equation_zero : W.Equation 0 0 ↔ W.a₆ = 0 := by
  rw [equation, C_0, eval_polynomial_zero, neg_eq_zero]
#align weierstrass_curve.equation_zero WeierstrassCurve.equation_zero

theorem equation_iff_variableChange (x y : R) :
    W.Equation x y ↔ (W.variableChange 1 x 0 y).Equation 0 0 :=
  by
  rw [equation_iff', ← neg_eq_zero, equation_zero, variable_change_a₆, inv_one, Units.val_one]
  congr 2
  ring1
#align weierstrass_curve.equation_iff_variable_change WeierstrassCurve.equation_iff_variableChange

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2242074953.map_simp -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2242074953.map_simp -/
theorem equation_iff_baseChange [Nontrivial A] [NoZeroSMulDivisors R A] (x y : R) :
    W.Equation x y ↔ (W.base_change A).Equation (algebraMap R A x) (algebraMap R A y) :=
  by
  simp only [equation_iff]
  refine' ⟨fun h => _, fun h => _⟩
  ·
    convert congr_arg (algebraMap R A) h <;>
      ·
        run_tac
          map_simp;
        rfl
  · apply NoZeroSMulDivisors.algebraMap_injective R A;
    run_tac
      map_simp;
    exact h
#align weierstrass_curve.equation_iff_base_change WeierstrassCurve.equation_iff_baseChange

theorem equation_iff_baseChange_of_baseChange [Nontrivial B] [NoZeroSMulDivisors A B] (x y : A) :
    (W.base_change A).Equation x y ↔
      (W.base_change B).Equation (algebraMap A B x) (algebraMap A B y) :=
  by rw [equation_iff_base_change (W.base_change A) B, base_change_base_change]
#align weierstrass_curve.equation_iff_base_change_of_base_change WeierstrassCurve.equation_iff_baseChange_of_baseChange

/-! ### Nonsingularity of Weierstrass curves -/


/-- The partial derivative $W_X(X, Y)$ of $W(X, Y)$ with respect to $X$.

TODO: define this in terms of `polynomial.derivative`. -/
noncomputable def polynomialX : R[X][Y] :=
  C (C W.a₁) * Y - C (C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄)
#align weierstrass_curve.polynomial_X WeierstrassCurve.polynomialX

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2480101633.eval_simp -/
@[simp]
theorem eval_polynomialX (x y : R) :
    (W.polynomialX.eval <| C y).eval x = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) := by
  simp only [polynomial_X];
  run_tac
    eval_simp
#align weierstrass_curve.eval_polynomial_X WeierstrassCurve.eval_polynomialX

@[simp]
theorem eval_polynomialX_zero : (W.polynomialX.eval 0).eval 0 = -W.a₄ := by
  simp only [← C_0, eval_polynomial_X, zero_add, zero_sub, MulZeroClass.mul_zero,
    zero_pow zero_lt_two]
#align weierstrass_curve.eval_polynomial_X_zero WeierstrassCurve.eval_polynomialX_zero

/-- The partial derivative $W_Y(X, Y)$ of $W(X, Y)$ with respect to $Y$.

TODO: define this in terms of `polynomial.derivative`. -/
noncomputable def polynomialY : R[X][Y] :=
  C (C 2) * Y + C (C W.a₁ * X + C W.a₃)
#align weierstrass_curve.polynomial_Y WeierstrassCurve.polynomialY

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2480101633.eval_simp -/
@[simp]
theorem eval_polynomialY (x y : R) : (W.polynomialY.eval <| C y).eval x = 2 * y + W.a₁ * x + W.a₃ :=
  by simp only [polynomial_Y];
  run_tac
    eval_simp;
  rw [← add_assoc]
#align weierstrass_curve.eval_polynomial_Y WeierstrassCurve.eval_polynomialY

@[simp]
theorem eval_polynomialY_zero : (W.polynomialY.eval 0).eval 0 = W.a₃ := by
  simp only [← C_0, eval_polynomial_Y, zero_add, MulZeroClass.mul_zero]
#align weierstrass_curve.eval_polynomial_Y_zero WeierstrassCurve.eval_polynomialY_zero

/-- The proposition that an affine point $(x, y)$ on `W` is nonsingular.
In other words, either $W_X(x, y) \ne 0$ or $W_Y(x, y) \ne 0$. -/
def Nonsingular (x y : R) : Prop :=
  W.Equation x y ∧ ((W.polynomialX.eval <| C y).eval x ≠ 0 ∨ (W.polynomialY.eval <| C y).eval x ≠ 0)
#align weierstrass_curve.nonsingular WeierstrassCurve.Nonsingular

theorem nonsingular_iff' (x y : R) :
    W.Nonsingular x y ↔
      W.Equation x y ∧
        (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 ∨ 2 * y + W.a₁ * x + W.a₃ ≠ 0) :=
  by rw [nonsingular, equation_iff', eval_polynomial_X, eval_polynomial_Y]
#align weierstrass_curve.nonsingular_iff' WeierstrassCurve.nonsingular_iff'

@[simp]
theorem nonsingular_iff (x y : R) :
    W.Nonsingular x y ↔
      W.Equation x y ∧ (W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∨ y ≠ -y - W.a₁ * x - W.a₃) :=
  by rw [nonsingular_iff', sub_ne_zero, ← @sub_ne_zero _ _ y]; congr 4 <;> ring1
#align weierstrass_curve.nonsingular_iff WeierstrassCurve.nonsingular_iff

@[simp]
theorem nonsingular_zero : W.Nonsingular 0 0 ↔ W.a₆ = 0 ∧ (W.a₃ ≠ 0 ∨ W.a₄ ≠ 0) := by
  rw [nonsingular, equation_zero, C_0, eval_polynomial_X_zero, neg_ne_zero, eval_polynomial_Y_zero,
    or_comm']
#align weierstrass_curve.nonsingular_zero WeierstrassCurve.nonsingular_zero

theorem nonsingular_iff_variableChange (x y : R) :
    W.Nonsingular x y ↔ (W.variableChange 1 x 0 y).Nonsingular 0 0 :=
  by
  rw [nonsingular_iff', equation_iff_variable_change, equation_zero, ← neg_ne_zero, or_comm',
    nonsingular_zero, variable_change_a₃, variable_change_a₄, inv_one, Units.val_one]
  congr 4 <;> ring1
#align weierstrass_curve.nonsingular_iff_variable_change WeierstrassCurve.nonsingular_iff_variableChange

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2242074953.map_simp -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2242074953.map_simp -/
theorem nonsingular_iff_baseChange [Nontrivial A] [NoZeroSMulDivisors R A] (x y : R) :
    W.Nonsingular x y ↔ (W.base_change A).Nonsingular (algebraMap R A x) (algebraMap R A y) :=
  by
  rw [nonsingular_iff, nonsingular_iff, and_congr <| W.equation_iff_base_change A x y]
  refine'
    ⟨Or.imp (not_imp_not.mpr fun h => _) (not_imp_not.mpr fun h => _),
      Or.imp (not_imp_not.mpr fun h => _) (not_imp_not.mpr fun h => _)⟩
  any_goals apply NoZeroSMulDivisors.algebraMap_injective R A;
    run_tac
      map_simp;
    exact h
  any_goals
    convert congr_arg (algebraMap R A) h <;>
      ·
        run_tac
          map_simp;
        rfl
#align weierstrass_curve.nonsingular_iff_base_change WeierstrassCurve.nonsingular_iff_baseChange

theorem nonsingular_iff_baseChange_of_baseChange [Nontrivial B] [NoZeroSMulDivisors A B] (x y : A) :
    (W.base_change A).Nonsingular x y ↔
      (W.base_change B).Nonsingular (algebraMap A B x) (algebraMap A B y) :=
  by rw [nonsingular_iff_base_change (W.base_change A) B, base_change_base_change]
#align weierstrass_curve.nonsingular_iff_base_change_of_base_change WeierstrassCurve.nonsingular_iff_baseChange_of_baseChange

theorem nonsingular_zero_of_Δ_ne_zero (h : W.Equation 0 0) (hΔ : W.Δ ≠ 0) : W.Nonsingular 0 0 := by
  simp only [equation_zero, nonsingular_zero] at *; contrapose! hΔ; simp [h, hΔ]
#align weierstrass_curve.nonsingular_zero_of_Δ_ne_zero WeierstrassCurve.nonsingular_zero_of_Δ_ne_zero

/-- A Weierstrass curve is nonsingular at every point if its discriminant is non-zero. -/
theorem nonsingular_of_Δ_ne_zero {x y : R} (h : W.Equation x y) (hΔ : W.Δ ≠ 0) :
    W.Nonsingular x y :=
  (W.nonsingular_iff_variableChange x y).mpr <|
    nonsingular_zero_of_Δ_ne_zero _ ((W.equation_iff_variableChange x y).mp h) <| by
      rwa [variable_change_Δ, inv_one, Units.val_one, one_pow, one_mul]
#align weierstrass_curve.nonsingular_of_Δ_ne_zero WeierstrassCurve.nonsingular_of_Δ_ne_zero

/-! ### Ideals in the coordinate ring -/


/-- The coordinate ring $R[W] := R[X, Y] / \langle W(X, Y) \rangle$ of `W`.

Note that `derive comm_ring` generates a reducible instance of `comm_ring` for `coordinate_ring`.
In certain circumstances this might be extremely slow, because all instances in its definition are
unified exponentially many times. In this case, one solution is to manually add the local attribute
`local attribute [irreducible] coordinate_ring.comm_ring` to block this type-level unification.

TODO Lean 4: verify if the new def-eq cache (lean4#1102) fixed this issue.

See Zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.E2.9C.94.20class_group.2Emk -/
def CoordinateRing : Type u :=
  AdjoinRoot W.Polynomial
deriving Inhabited, CommRing
#align weierstrass_curve.coordinate_ring WeierstrassCurve.CoordinateRing

/-- The function field $R(W) := \mathrm{Frac}(R[W])$ of `W`. -/
abbrev FunctionField : Type u :=
  FractionRing W.CoordinateRing
#align weierstrass_curve.function_field WeierstrassCurve.FunctionField

namespace CoordinateRing

open Ideal

instance [IsDomain R] [NormalizedGCDMonoid R] : IsDomain W.CoordinateRing :=
  (Quotient.isDomain_iff_prime _).mpr <| by
    simpa only [span_singleton_prime W.polynomial_ne_zero, ← GCDMonoid.irreducible_iff_prime] using
      W.irreducible_polynomial

instance isDomain_of_field {F : Type u} [Field F] (W : WeierstrassCurve F) :
    IsDomain W.CoordinateRing := by classical infer_instance
#align weierstrass_curve.coordinate_ring.is_domain_of_field WeierstrassCurve.CoordinateRing.isDomain_of_field

variable (x : R) (y : R[X])

/-- The class of the element $X - x$ in $R[W]$ for some $x \in R$. -/
@[simp]
noncomputable def xClass : W.CoordinateRing :=
  AdjoinRoot.mk W.Polynomial <| C <| X - C x
#align weierstrass_curve.coordinate_ring.X_class WeierstrassCurve.CoordinateRing.xClass

theorem xClass_ne_zero [Nontrivial R] : xClass W x ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt W.monic_polynomial (C_ne_zero.mpr <| X_sub_C_ne_zero x) <|
    by rw [nat_degree_polynomial, nat_degree_C]; norm_num1
#align weierstrass_curve.coordinate_ring.X_class_ne_zero WeierstrassCurve.CoordinateRing.xClass_ne_zero

/-- The class of the element $Y - y(X)$ in $R[W]$ for some $y(X) \in R[X]$. -/
@[simp]
noncomputable def yClass : W.CoordinateRing :=
  AdjoinRoot.mk W.Polynomial <| Y - C y
#align weierstrass_curve.coordinate_ring.Y_class WeierstrassCurve.CoordinateRing.yClass

theorem yClass_ne_zero [Nontrivial R] : yClass W y ≠ 0 :=
  AdjoinRoot.mk_ne_zero_of_natDegree_lt W.monic_polynomial (X_sub_C_ne_zero y) <| by
    rw [nat_degree_polynomial, nat_degree_X_sub_C]; norm_num1
#align weierstrass_curve.coordinate_ring.Y_class_ne_zero WeierstrassCurve.CoordinateRing.yClass_ne_zero

/-- The ideal $\langle X - x \rangle$ of $R[W]$ for some $x \in R$. -/
@[simp]
noncomputable def xIdeal : Ideal W.CoordinateRing :=
  span {xClass W x}
#align weierstrass_curve.coordinate_ring.X_ideal WeierstrassCurve.CoordinateRing.xIdeal

/-- The ideal $\langle Y - y(X) \rangle$ of $R[W]$ for some $y(X) \in R[X]$. -/
@[simp]
noncomputable def yIdeal : Ideal W.CoordinateRing :=
  span {yClass W y}
#align weierstrass_curve.coordinate_ring.Y_ideal WeierstrassCurve.CoordinateRing.yIdeal

/-- The ideal $\langle X - x, Y - y(X) \rangle$ of $R[W]$ for some $x \in R$ and $y(X) \in R[X]$. -/
@[simp]
noncomputable def xYIdeal (x : R) (y : R[X]) : Ideal W.CoordinateRing :=
  span {xClass W x, yClass W y}
#align weierstrass_curve.coordinate_ring.XY_ideal WeierstrassCurve.CoordinateRing.xYIdeal

/-! ### The coordinate ring as an `R[X]`-algebra -/


noncomputable instance : Algebra R[X] W.CoordinateRing :=
  Quotient.algebra R[X]

noncomputable instance algebra' : Algebra R W.CoordinateRing :=
  Quotient.algebra R
#align weierstrass_curve.coordinate_ring.algebra' WeierstrassCurve.CoordinateRing.algebra'

instance : IsScalarTower R R[X] W.CoordinateRing :=
  Quotient.isScalarTower R R[X] _

instance [Subsingleton R] : Subsingleton W.CoordinateRing :=
  Module.subsingleton R[X] _

/-- The $R$-algebra isomorphism from $R[W] / \langle X - x, Y - y(X) \rangle$ to $R$ obtained by
evaluation at $y(X)$ and at $x$ provided that $W(x, y(x)) = 0$. -/
noncomputable def quotientXYIdealEquiv {x : R} {y : R[X]} (h : (W.Polynomial.eval y).eval x = 0) :
    (W.CoordinateRing ⧸ xYIdeal W x y) ≃ₐ[R] R :=
  (quotientEquivAlgOfEq R <| by
        simpa only [XY_ideal, X_class, Y_class, ← Set.image_pair, ← map_span]).trans <|
    (DoubleQuot.quotQuotEquivQuotOfLEₐ R <|
          (span_singleton_le_iff_mem _).mpr <|
            mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h).trans <|
      ((quotientSpanCXSubCAlgEquiv (X - C x) y).restrictScalars R).trans <|
        quotientSpanXSubCAlgEquiv x
#align weierstrass_curve.coordinate_ring.quotient_XY_ideal_equiv WeierstrassCurve.CoordinateRing.quotientXYIdealEquiv

/-- The basis $\{1, Y\}$ for the coordinate ring $R[W]$ over the polynomial ring $R[X]$.

Given a Weierstrass curve `W`, write `W^.coordinate_ring.basis` for this basis. -/
protected noncomputable def basis : Basis (Fin 2) R[X] W.CoordinateRing :=
  (subsingleton_or_nontrivial R).byCases (fun _ => default) fun _ =>
    (AdjoinRoot.powerBasis' W.monic_polynomial).Basis.reindex <| finCongr W.nat_degree_polynomial
#align weierstrass_curve.coordinate_ring.basis WeierstrassCurve.CoordinateRing.basis

theorem basis_apply (n : Fin 2) :
    W.CoordinateRing.Basis n = (AdjoinRoot.powerBasis' W.monic_polynomial).gen ^ (n : ℕ) := by
  classical
  nontriviality R
  simpa only [coordinate_ring.basis, Or.by_cases, dif_neg (not_subsingleton R), Basis.reindex_apply,
    PowerBasis.basis_eq_pow]
#align weierstrass_curve.coordinate_ring.basis_apply WeierstrassCurve.CoordinateRing.basis_apply

theorem basis_zero : W.CoordinateRing.Basis 0 = 1 := by simpa only [basis_apply] using pow_zero _
#align weierstrass_curve.coordinate_ring.basis_zero WeierstrassCurve.CoordinateRing.basis_zero

theorem basis_one : W.CoordinateRing.Basis 1 = AdjoinRoot.mk W.Polynomial Y := by
  simpa only [basis_apply] using pow_one _
#align weierstrass_curve.coordinate_ring.basis_one WeierstrassCurve.CoordinateRing.basis_one

@[simp]
theorem coe_basis :
    (W.CoordinateRing.Basis : Fin 2 → W.CoordinateRing) = ![1, AdjoinRoot.mk W.Polynomial Y] := by
  ext n; fin_cases n; exacts [basis_zero W, basis_one W]
#align weierstrass_curve.coordinate_ring.coe_basis WeierstrassCurve.CoordinateRing.coe_basis

variable {W}

theorem smul (x : R[X]) (y : W.CoordinateRing) : x • y = AdjoinRoot.mk W.Polynomial (C x) * y :=
  (algebraMap_smul W.CoordinateRing x y).symm
#align weierstrass_curve.coordinate_ring.smul WeierstrassCurve.CoordinateRing.smul

theorem smul_basis_eq_zero {p q : R[X]} (hpq : p • 1 + q • AdjoinRoot.mk W.Polynomial Y = 0) :
    p = 0 ∧ q = 0 :=
  by
  have h := fintype.linear_independent_iff.mp (coordinate_ring.basis W).LinearIndependent ![p, q]
  erw [Fin.sum_univ_succ, basis_zero, Fin.sum_univ_one, basis_one] at h 
  exact ⟨h hpq 0, h hpq 1⟩
#align weierstrass_curve.coordinate_ring.smul_basis_eq_zero WeierstrassCurve.CoordinateRing.smul_basis_eq_zero

theorem exists_smul_basis_eq (x : W.CoordinateRing) :
    ∃ p q : R[X], p • 1 + q • AdjoinRoot.mk W.Polynomial Y = x :=
  by
  have h := (coordinate_ring.basis W).sum_equivFun x
  erw [Fin.sum_univ_succ, Fin.sum_univ_one, basis_zero, basis_one] at h 
  exact ⟨_, _, h⟩
#align weierstrass_curve.coordinate_ring.exists_smul_basis_eq WeierstrassCurve.CoordinateRing.exists_smul_basis_eq

variable (W)

theorem smul_basis_mul_c (p q : R[X]) :
    (p • 1 + q • AdjoinRoot.mk W.Polynomial Y) * AdjoinRoot.mk W.Polynomial (C y) =
      (p * y) • 1 + (q * y) • AdjoinRoot.mk W.Polynomial Y :=
  by simp only [smul, _root_.map_mul]; ring1
#align weierstrass_curve.coordinate_ring.smul_basis_mul_C WeierstrassCurve.CoordinateRing.smul_basis_mul_c

theorem smul_basis_mul_Y (p q : R[X]) :
    (p • 1 + q • AdjoinRoot.mk W.Polynomial Y) * AdjoinRoot.mk W.Polynomial Y =
      (q * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) • 1 +
        (p - q * (C W.a₁ * X + C W.a₃)) • AdjoinRoot.mk W.Polynomial Y :=
  by
  have Y_sq :
    AdjoinRoot.mk W.polynomial Y ^ 2 =
      AdjoinRoot.mk W.polynomial
        (C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) - C (C W.a₁ * X + C W.a₃) * Y) :=
    adjoin_root.mk_eq_mk.mpr ⟨1, by simp only [WeierstrassCurve.polynomial]; ring1⟩
  simp only [smul, add_mul, mul_assoc, ← sq, Y_sq, map_sub, _root_.map_mul]
  ring1
#align weierstrass_curve.coordinate_ring.smul_basis_mul_Y WeierstrassCurve.CoordinateRing.smul_basis_mul_Y

/-! ### Norms on the coordinate ring -/


theorem norm_smul_basis (p q : R[X]) :
    Algebra.norm R[X] (p • 1 + q • AdjoinRoot.mk W.Polynomial Y) =
      p ^ 2 - p * q * (C W.a₁ * X + C W.a₃) -
        q ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) :=
  by
  simp_rw [Algebra.norm_eq_matrix_det W.CoordinateRing.Basis, Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, basis_zero, mul_one, basis_one, smul_basis_mul_Y, map_add,
    Finsupp.add_apply, map_smul, Finsupp.smul_apply, ← basis_zero, ← basis_one,
    Basis.repr_self_apply, if_pos, if_neg one_ne_zero, if_neg zero_ne_one, smul_eq_mul]
  ring1
#align weierstrass_curve.coordinate_ring.norm_smul_basis WeierstrassCurve.CoordinateRing.norm_smul_basis

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3948480697.C_simp -/
theorem coe_norm_smul_basis (p q : R[X]) :
    ↑(Algebra.norm R[X] <| p • 1 + q • AdjoinRoot.mk W.Polynomial Y) =
      AdjoinRoot.mk W.Polynomial ((C p + C q * X) * (C p + C q * (-Y - C (C W.a₁ * X + C W.a₃)))) :=
  AdjoinRoot.mk_eq_mk.mpr
    ⟨C q ^ 2, by rw [norm_smul_basis, WeierstrassCurve.polynomial];
      run_tac
        C_simp;
      ring1⟩
#align weierstrass_curve.coordinate_ring.coe_norm_smul_basis WeierstrassCurve.CoordinateRing.coe_norm_smul_basis

theorem degree_norm_smul_basis [IsDomain R] (p q : R[X]) :
    (Algebra.norm R[X] <| p • 1 + q • AdjoinRoot.mk W.Polynomial Y).degree =
      max (2 • p.degree) (2 • q.degree + 3) :=
  by
  have hdp : (p ^ 2).degree = 2 • p.degree := degree_pow p 2
  have hdpq : (p * q * (C W.a₁ * X + C W.a₃)).degree ≤ p.degree + q.degree + 1 := by
    simpa only [degree_mul] using add_le_add_left degree_linear_le (p.degree + q.degree)
  have hdq : (q ^ 2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)).degree = 2 • q.degree + 3 :=
    by rw [degree_mul, degree_pow, ← one_mul <| X ^ 3, ← C_1, degree_cubic <| one_ne_zero' R]
  rw [norm_smul_basis]
  by_cases hp : p = 0;
  ·
    simpa only [hp, hdq, neg_zero, zero_sub, MulZeroClass.zero_mul, zero_pow zero_lt_two,
      degree_neg] using (max_bot_left _).symm
  by_cases hq : q = 0;
  ·
    simpa only [hq, hdp, sub_zero, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
      zero_pow zero_lt_two] using (max_bot_right _).symm
  rw [← not_congr degree_eq_bot] at hp hq 
  cases' p.degree with dp; · exact (hp rfl).elim
  cases' q.degree with dq; · exact (hq rfl).elim
  cases' le_or_lt dp (dq + 1) with hpq hpq
  ·
    convert
          (degree_sub_eq_right_of_degree_lt <|
                (degree_sub_le _ _).trans_lt <|
                  max_lt_iff.mpr ⟨hdp.trans_lt _, hdpq.trans_lt _⟩).trans
            (max_eq_right_of_lt _).symm <;>
        rw [hdq] <;>
      exact with_bot.coe_lt_coe.mpr (by linarith only [hpq])
  · rw [sub_sub]
    convert
          (degree_sub_eq_left_of_degree_lt <|
                (degree_add_le _ _).trans_lt <|
                  max_lt_iff.mpr ⟨hdpq.trans_lt _, hdq.trans_lt _⟩).trans
            (max_eq_left_of_lt _).symm <;>
        rw [hdp] <;>
      exact with_bot.coe_lt_coe.mpr (by linarith only [hpq])
#align weierstrass_curve.coordinate_ring.degree_norm_smul_basis WeierstrassCurve.CoordinateRing.degree_norm_smul_basis

variable {W}

theorem degree_norm_ne_one [IsDomain R] (x : W.CoordinateRing) : (Algebra.norm R[X] x).degree ≠ 1 :=
  by
  rcases exists_smul_basis_eq x with ⟨p, q, rfl⟩
  rw [degree_norm_smul_basis]
  rcases p.degree with (_ | _ | _ | _) <;> cases q.degree
  any_goals rintro (_ | _)
  exact (lt_max_of_lt_right (by decide)).ne'
#align weierstrass_curve.coordinate_ring.degree_norm_ne_one WeierstrassCurve.CoordinateRing.degree_norm_ne_one

theorem natDegree_norm_ne_one [IsDomain R] (x : W.CoordinateRing) :
    (Algebra.norm R[X] x).natDegree ≠ 1 :=
  mt (degree_eq_iff_natDegree_eq_of_pos zero_lt_one).mpr <| degree_norm_ne_one x
#align weierstrass_curve.coordinate_ring.nat_degree_norm_ne_one WeierstrassCurve.CoordinateRing.natDegree_norm_ne_one

end CoordinateRing

end Polynomial

end WeierstrassCurve

/-! ## Elliptic curves -/


/-- An elliptic curve over a commutative ring. Note that this definition is only mathematically
accurate for certain rings whose Picard group has trivial 12-torsion, such as a field or a PID. -/
@[ext]
structure EllipticCurve (R : Type u) [CommRing R] extends WeierstrassCurve R where
  Δ' : Rˣ
  coe_Δ' : ↑Δ' = to_weierstrass_curve.Δ
#align elliptic_curve EllipticCurve

instance : Inhabited <| EllipticCurve ℚ :=
  ⟨⟨⟨0, 0, 1, -1, 0⟩, ⟨37, 37⁻¹, by norm_num1, by norm_num1⟩, by dsimp; ring1⟩⟩

namespace EllipticCurve

variable [CommRing R] (E : EllipticCurve R)

/-- The j-invariant `j` of an elliptic curve, which is invariant under isomorphisms over `R`. -/
@[simp]
def j : R :=
  ↑E.Δ'⁻¹ * E.c₄ ^ 3
#align elliptic_curve.j EllipticCurve.j

theorem twoTorsionPolynomial_disc_ne_zero [Nontrivial R] [Invertible (2 : R)] :
    E.twoTorsionPolynomial.disc ≠ 0 :=
  E.twoTorsionPolynomial_disc_ne_zero <| E.coe_Δ' ▸ E.Δ'.IsUnit
#align elliptic_curve.two_torsion_polynomial_disc_ne_zero EllipticCurve.twoTorsionPolynomial_disc_ne_zero

theorem nonsingular [Nontrivial R] {x y : R} (h : E.Equation x y) : E.Nonsingular x y :=
  E.nonsingular_of_Δ_ne_zero h <| E.coe_Δ' ▸ E.Δ'.NeZero
#align elliptic_curve.nonsingular EllipticCurve.nonsingular

section VariableChange

/-! ### Variable changes -/


variable (u : Rˣ) (r s t : R)

/-- The elliptic curve over `R` induced by an admissible linear change of variables
$(X, Y) \mapsto (u^2X + r, u^3Y + u^2sX + t)$ for some $u \in R^\times$ and some $r, s, t \in R$.
When `R` is a field, any two Weierstrass equations isomorphic to `E` are related by this. -/
@[simps]
def variableChange : EllipticCurve R :=
  ⟨E.variableChange u r s t, u⁻¹ ^ 12 * E.Δ', by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, coe_Δ', E.variable_change_Δ]⟩
#align elliptic_curve.variable_change EllipticCurve.variableChange

theorem coe_variableChange_Δ' : (↑(E.variableChange u r s t).Δ' : R) = ↑u⁻¹ ^ 12 * E.Δ' := by
  rw [variable_change_Δ', Units.val_mul, Units.val_pow_eq_pow_val]
#align elliptic_curve.coe_variable_change_Δ' EllipticCurve.coe_variableChange_Δ'

theorem coe_inv_variableChange_Δ' : (↑(E.variableChange u r s t).Δ'⁻¹ : R) = u ^ 12 * ↑E.Δ'⁻¹ := by
  rw [variable_change_Δ', mul_inv, inv_pow, inv_inv, Units.val_mul, Units.val_pow_eq_pow_val]
#align elliptic_curve.coe_inv_variable_change_Δ' EllipticCurve.coe_inv_variableChange_Δ'

@[simp]
theorem variableChange_j : (E.variableChange u r s t).j = E.j :=
  by
  rw [j, coe_inv_variable_change_Δ']
  have hu : (u * ↑u⁻¹ : R) ^ 12 = 1 := by rw [u.mul_inv, one_pow]
  linear_combination (norm := (dsimp; ring1)) E.j * hu
#align elliptic_curve.variable_change_j EllipticCurve.variableChange_j

end VariableChange

section BaseChange

/-! ### Base changes -/


variable (A : Type v) [CommRing A] [Algebra R A]

/-- The elliptic curve over `R` base changed to `A`. -/
@[simps]
def baseChange : EllipticCurve A :=
  ⟨E.base_change A, Units.map (↑(algebraMap R A)) E.Δ', by
    rw [Units.coe_map, RingHom.coe_monoidHom, coe_Δ', E.base_change_Δ]⟩
#align elliptic_curve.base_change EllipticCurve.baseChange

theorem coeBase_change_Δ' : ↑(E.base_change A).Δ' = algebraMap R A E.Δ' :=
  rfl
#align elliptic_curve.coe_base_change_Δ' EllipticCurve.coeBase_change_Δ'

theorem coe_inv_baseChange_Δ' : ↑(E.base_change A).Δ'⁻¹ = algebraMap R A ↑E.Δ'⁻¹ :=
  rfl
#align elliptic_curve.coe_inv_base_change_Δ' EllipticCurve.coe_inv_baseChange_Δ'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2242074953.map_simp -/
@[simp]
theorem baseChange_j : (E.base_change A).j = algebraMap R A E.j :=
  by
  simp only [j, coe_inv_base_change_Δ', base_change_to_weierstrass_curve, E.base_change_c₄]
  run_tac
    map_simp
#align elliptic_curve.base_change_j EllipticCurve.baseChange_j

end BaseChange

end EllipticCurve

