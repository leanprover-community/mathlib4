/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.Data.MvPolynomial.CommRing

/-!
# Projective coordinates for Weierstrass curves

This file defines the type of points on a Weierstrass curve as a tuple, consisting of a equivalence
class of triples up to scaling by a unit, satisfying a Weierstrass equation with a nonsingular
condition. This file also defines the negation and addition operations of the group law for this
type, and proves that they respect the Weierstrass equation and the nonsingular condition. The fact
that they form an abelian group is proven in `Mathlib.AlgebraicGeometry.EllipticCurve.Group`.

## Mathematical background

Let `W` be a Weierstrass curve over a field `F`. A point on the projective plane is an equivalence
class of triples $[x:y:z]$ with coordinates in `F` such that $(x, y, z) \sim (x', y', z')$ precisely
if there is some unit $u$ in `F` such that $(x, y, z) = (ux', uy', uz')$, with an extra condition
that $(x, y, z) \ne (0, 0, 0)$. As described in `Mathlib.AlgebraicGeometry.EllipticCurve.Affine`, a
rational point is a point on the projective plane satisfying a homogeneous Weierstrass equation, and
being nonsingular means the partial derivatives $W_X(X, Y, Z)$, $W_Y(X, Y, Z)$, and $W_Z(X, Y, Z)$
do not vanish simultaneously. Note that the vanishing of the Weierstrass equation and its partial
derivatives are independent of the representative for $[x:y:z]$, and the nonsingularity condition
already implies that $(x, y, z) \ne (0, 0, 0)$, so a nonsingular rational point on `W` can simply be
given by a tuple consisting of $[x:y:z]$ and the nonsingular condition on any representative.

As in `Mathlib.AlgebraicGeometry.EllipticCurve.Affine`, the set of nonsingular rational points forms
an abelian group under the same secant-and-tangent process, but the polynomials involved are
homogeneous, and any instances of division become multiplication in the $Z$-coordinate.
Note that most computational proofs follow from their analogous proofs for affine coordinates.

## Main definitions

 * `WeierstrassCurve.Projective.PointRep`: the representative of a point in the projective plane.
 * `WeierstrassCurve.Projective.PointClass`: the equivalence class of a point representative.
 * `WeierstrassCurve.Projective.toAffine`: the Weierstrass curve in affine coordinates.
 * `WeierstrassCurve.Projective.nonsingular`: the nonsingular condition on a point representative.
 * `WeierstrassCurve.Projective.nonsingular_lift`: the nonsingular condition on a point class.
 * `WeierstrassCurve.Projective.neg`: the negation operation on a point representative.
 * `WeierstrassCurve.Projective.neg_map`: the negation operation on a point class.
 * `WeierstrassCurve.Projective.add`: the addition operation on a point representative.
 * `WeierstrassCurve.Projective.add_map`: the addition operation on a point class.
 * `WeierstrassCurve.Projective.Point`: a nonsingular rational point.
 * `WeierstrassCurve.Projective.Point.neg`: the negation operation on a nonsingular rational point.
 * `WeierstrassCurve.Projective.Point.add`: the addition operation on a nonsingular rational point.
 * `WeierstrassCurve.Projective.Point.toAffine_addEquiv`: the equivalence between the nonsingular
    rational points on a projective Weierstrass curve with those on an affine Weierstrass curve.

## Main statements

 * `WeierstrassCurve.Projective.polynomial_relation`: Euler's homogeneous function theorem.
 * `WeierstrassCurve.Projective.nonsingular_neg`: negation preserves the nonsingular condition.
 * `WeierstrassCurve.Projective.nonsingular_add`: addition preserves the nonsingular condition.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, projective coordinates
-/

universe u

/-! ## Weierstrass curves -/

/-- An abbreviation for a Weierstrass curve in projective coordinates. -/
abbrev WeierstrassCurve.Projective :=
  WeierstrassCurve

namespace WeierstrassCurve.Projective

open MvPolynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow])

/-- The representative of a point in the projective plane. -/
structure PointRep (R : Type u) where
  (x y z : R)

/-- The $X$-coordinate of a point representative. -/
add_decl_doc PointRep.x

/-- The $Y$-coordinate of a point representative. -/
add_decl_doc PointRep.y

/-- The $Z$-coordinate of a point representative. -/
add_decl_doc PointRep.z

variable (R : Type u) [CommRing R]

/-- The equivalence relation for a point representative. -/
def PointRel (P Q : PointRep R) : Prop :=
  ∃ u : Rˣ, P.x = (u : R) * Q.x ∧ P.y = (u : R) * Q.y ∧ P.z = (u : R) * Q.z

lemma PointEquiv : Equivalence <| PointRel R :=
  ⟨fun _ => ⟨1, by simp only [Units.val_one, one_pow, one_mul, and_self]⟩,
    fun ⟨u, hu⟩ =>
      ⟨u⁻¹, by simp only [hu, ← u.val_pow_eq_pow_val, inv_pow, u.inv_mul_cancel_left, and_self]⟩,
    fun ⟨u, hu⟩ ⟨u', hu'⟩ =>
      ⟨u * u', by simp only [hu, hu', u.val_mul, mul_pow, mul_assoc, and_self]⟩⟩

instance instSetoidPointRep : Setoid <| PointRep R :=
  ⟨PointRel R, PointEquiv R⟩

/-- The equivalence class of a point representative. -/
abbrev PointClass : Type u :=
  Quotient <| instSetoidPointRep R

variable {R} (W : Projective R)

/-- The coercion to a Weierstrass curve in affine coordinates. -/
@[pp_dot]
abbrev toAffine : Affine R :=
  W

section Equation

/-! ### Equations and nonsingularity -/

/-- The polynomial $W(X, Y, Z) := Y^2Z + a_1XYZ + a_3YZ^2 - (X^3 + a_2X^2Z + a_4XZ^2 + a_6Z^3)$
associated to a Weierstrass curve `W` over `R`. This is represented as a term of type
`MvPolynomial (Fin 3) R`, where `X 0`, `X 1`, and `X 2` represent $X$, $Y$, and $Z$ respectively. -/
@[pp_dot]
noncomputable def polynomial : MvPolynomial (Fin 3) R :=
  X 1 ^ 2 * X 2 + C W.a₁ * X 0 * X 1 * X 2 + C W.a₃ * X 1 * X 2 ^ 2
    - (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 * X 2 + C W.a₄ * X 0 * X 2 ^ 2 + C W.a₆ * X 2 ^ 3)

lemma eval_polynomial (P : PointRep R) : eval ![P.x, P.y, P.z] W.polynomial =
    P.y ^ 2 * P.z + W.a₁ * P.x * P.y * P.z + W.a₃ * P.y * P.z ^ 2
      - (P.x ^ 3 + W.a₂ * P.x ^ 2 * P.z + W.a₄ * P.x * P.z ^ 2 + W.a₆ * P.z ^ 3) := by
  rw [polynomial]
  eval_simp
  rfl

/-- The proposition that a point representative $(x, y, z)$ lies in `W`.
In other words, $W(x, y, z) = 0$. -/
@[pp_dot]
def equation (P : PointRep R) : Prop :=
  eval ![P.x, P.y, P.z] W.polynomial = 0

lemma equation_iff (P : PointRep R) : W.equation P ↔
    P.y ^ 2 * P.z + W.a₁ * P.x * P.y * P.z + W.a₃ * P.y * P.z ^ 2
      = P.x ^ 3 + W.a₂ * P.x ^ 2 * P.z + W.a₄ * P.x * P.z ^ 2 + W.a₆ * P.z ^ 3 := by
  rw [equation, eval_polynomial, sub_eq_zero]

lemma equation_zero (y : R) : W.equation ⟨0, y, 0⟩ :=
  (W.equation_iff ⟨0, y, 0⟩).mpr <| by ring1

lemma equation_some (x y : R) : W.equation ⟨x, y, 1⟩ ↔ W.toAffine.equation x y := by
  rw [equation_iff, W.toAffine.equation_iff]
  congr! 1 <;> ring1

@[simp]
lemma equation_mul_iff (P : PointRep R) (u : Rˣ) :
    W.equation ⟨u * P.x, u * P.y, u * P.z⟩ ↔ W.equation P :=
  have (u : Rˣ) {P : PointRep R} (h : W.equation P) : W.equation ⟨u * P.x, u * P.y, u * P.z⟩ := by
    rw [equation_iff] at h ⊢
    linear_combination (norm := ring1) (u : R) ^ 3 * h
  ⟨fun h => by convert this u⁻¹ h <;> exact (u.inv_mul_cancel_left _).symm, this u⟩

/-- The partial derivative $W_X(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $X$.

TODO: define this in terms of `MvPolynomial.pderiv`. -/
@[pp_dot]
noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  C W.a₁ * X 1 * X 2 - (C 3 * X 0 ^ 2 + C (2 * W.a₂) * X 0 * X 2 + C W.a₄ * X 2 ^ 2)

lemma eval_polynomialX (P : PointRep R) : eval ![P.x, P.y, P.z] W.polynomialX =
    W.a₁ * P.y * P.z - (3 * P.x ^ 2 + 2 * W.a₂ * P.x * P.z + W.a₄ * P.z ^ 2) := by
  rw [polynomialX]
  eval_simp
  rfl

/-- The partial derivative $W_Y(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $Y$.

TODO: define this in terms of `MvPolynomial.pderiv`. -/
@[pp_dot]
noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  C 2 * X 1 * X 2 + C W.a₁ * X 0 * X 2 + C W.a₃ * X 2 ^ 2

lemma eval_polynomialY (P : PointRep R) :
    eval ![P.x, P.y, P.z] W.polynomialY = 2 * P.y * P.z + W.a₁ * P.x * P.z + W.a₃ * P.z ^ 2 := by
  rw [polynomialY]
  eval_simp
  rfl

/-- The partial derivative $W_Z(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $Z$.

TODO: define this in terms of `MvPolynomial.pderiv`. -/
@[pp_dot]
noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C (2 * W.a₃) * X 1 * X 2
    - (C W.a₂ * X 0 ^ 2 + C (2 * W.a₄) * X 0 * X 2 + C (3 * W.a₆) * X 2 ^ 2)

lemma eval_polynomialZ (P : PointRep R) : eval ![P.x, P.y, P.z] W.polynomialZ =
    P.y ^ 2 + W.a₁ * P.x * P.y + 2 * W.a₃ * P.y * P.z
      - (W.a₂ * P.x ^ 2 + 2 * W.a₄ * P.x * P.z + 3 * W.a₆ * P.z ^ 2) := by
  rw [polynomialZ]
  eval_simp
  rfl

/-- Euler's homogeneous function theorem. -/
theorem polynomial_relation (P : PointRep R) : 3 * eval ![P.x, P.y, P.z] W.polynomial =
    P.x * eval ![P.x, P.y, P.z] W.polynomialX + P.y * eval ![P.x, P.y, P.z] W.polynomialY
      + P.z * eval ![P.x, P.y, P.z] W.polynomialZ := by
  rw [eval_polynomial, eval_polynomialX, eval_polynomialY, eval_polynomialZ]
  ring1

/-- The proposition that a point representative $(x, y, z)$ in `W` is nonsingular.
In other words, either $W_X(x, y, z) \ne 0$, $W_Y(x, y, z) \ne 0$, or $W_Z(x, y, z) \ne 0$. -/
@[pp_dot]
def nonsingular (P : PointRep R) : Prop :=
  W.equation P ∧ (eval ![P.x, P.y, P.z] W.polynomialX ≠ 0 ∨ eval ![P.x, P.y, P.z] W.polynomialY ≠ 0
    ∨ eval ![P.x, P.y, P.z] W.polynomialZ ≠ 0)

lemma nonsingular_iff (P : PointRep R) : W.nonsingular P ↔ W.equation P ∧
    (W.a₁ * P.y * P.z ≠ 3 * P.x ^ 2 + 2 * W.a₂ * P.x * P.z + W.a₄ * P.z ^ 2 ∨
      P.y * P.z ≠ -P.y * P.z - W.a₁ * P.x * P.z - W.a₃ * P.z ^ 2 ∨
      P.y ^ 2 + W.a₁ * P.x * P.y + 2 * W.a₃ * P.y * P.z
        ≠ W.a₂ * P.x ^ 2 + 2 * W.a₄ * P.x * P.z + 3 * W.a₆ * P.z ^ 2) := by
  rw [nonsingular, eval_polynomialX, eval_polynomialY, eval_polynomialZ, sub_ne_zero, sub_ne_zero,
    ← sub_ne_zero (a := P.y * P.z)]
  congr! 4
  ring1

lemma nonsingular_zero [Nontrivial R] : W.nonsingular ⟨0, 1, 0⟩ :=
  (W.nonsingular_iff ⟨0, 1, 0⟩).mpr ⟨W.equation_zero 1, by simp⟩

lemma nonsingular_zero' [NoZeroDivisors R] {y : R} (hy : y ≠ 0) : W.nonsingular ⟨0, y, 0⟩ :=
  (W.nonsingular_iff ⟨0, y, 0⟩).mpr ⟨W.equation_zero y, by simpa⟩

lemma nonsingular_some (x y : R) : W.nonsingular ⟨x, y, 1⟩ ↔ W.toAffine.nonsingular x y := by
  simp only [nonsingular_iff, W.toAffine.nonsingular_iff, equation_some, and_congr_right_iff,
    W.toAffine.equation_iff, ← not_and_or, not_iff_not, one_pow, mul_one, Iff.comm, iff_self_and]
  intro h hX hY
  linear_combination (norm := ring1) 3 * h - x * hX - y * hY

@[simp]
lemma nonsingular_mul_iff (P : PointRep R) (u : Rˣ) :
    W.nonsingular ⟨u * P.x, u * P.y, u * P.z⟩ ↔ W.nonsingular P :=
  have (u : Rˣ) {P : PointRep R} (h : W.nonsingular ⟨u * P.x, u * P.y, u * P.z⟩) :
      W.nonsingular P := by
    rcases (W.nonsingular_iff _).mp h with ⟨h, h'⟩
    refine (W.nonsingular_iff P).mpr ⟨(W.equation_mul_iff P u).mp h, ?_⟩
    contrapose! h'
    exact ⟨by linear_combination (norm := ring1) (u : R) ^ 2 * h'.left,
      by linear_combination (norm := ring1) (u : R) ^ 2 * h'.right.left,
      by linear_combination (norm := ring1) (u : R) ^ 2 * h'.right.right⟩
  ⟨this u, fun h => this u⁻¹ <| by simpa only [u.inv_mul_cancel_left] using h⟩

lemma nonsingular_of_equiv {P Q : PointRep R} (h : P ≈ Q) : W.nonsingular P ↔ W.nonsingular Q := by
  rcases P, h with ⟨⟨_, _, _⟩, ⟨u, ⟨rfl, rfl, rfl⟩⟩⟩
  exact W.nonsingular_mul_iff Q u

/-- The proposition that a point class on `W` is nonsingular. If `P` is a point representative,
then `W.nonsingular_lift ⟦P⟧` is definitionally equivalent to `W.nonsingular P`. -/
@[pp_dot]
def nonsingular_lift (P : PointClass R) : Prop :=
  P.lift W.nonsingular fun _ _ => propext ∘ W.nonsingular_of_equiv

@[simp]
lemma nonsingular_lift_eq (P : PointRep R) : W.nonsingular_lift ⟦P⟧ = W.nonsingular P :=
  rfl

lemma nonsingular_lift_zero [Nontrivial R] : W.nonsingular_lift ⟦⟨0, 1, 0⟩⟧ :=
  W.nonsingular_zero

lemma nonsingular_lift_zero' [NoZeroDivisors R] {y : R} (hy : y ≠ 0) :
    W.nonsingular_lift ⟦⟨0, y, 0⟩⟧ :=
  W.nonsingular_zero' hy

lemma nonsingular_lift_some (x y : R) :
    W.nonsingular_lift ⟦⟨x, y, 1⟩⟧ ↔ W.toAffine.nonsingular x y :=
  W.nonsingular_some x y

variable {F : Type u} [Field F] {W : Projective F}

lemma equiv_of_Zeq0 {P Q : PointRep F} (hP : W.nonsingular P) (hQ : W.nonsingular Q) (hPz : P.z = 0)
    (hQz : Q.z = 0) : P ≈ Q := by
  rcases P, Q with ⟨⟨_, y, _⟩, ⟨_, y', _⟩⟩
  subst hPz hQz
  simp [nonsingular_iff, equation_iff] at hP hQ
  rcases pow_eq_zero hP.left.symm, pow_eq_zero hQ.left.symm with ⟨⟨_⟩, ⟨_⟩⟩
  simp at hP hQ
  exact ⟨Units.mk0 (y / y') <| div_ne_zero hP hQ, by simpa using (div_mul_cancel y hQ).symm⟩

lemma equiv_zero_of_Zeq0 {P : PointRep F} (h : W.nonsingular P) (hPz : P.z = 0) : P ≈ ⟨0, 1, 0⟩ :=
  equiv_of_Zeq0 h W.nonsingular_zero hPz rfl

lemma equiv_some_of_Zne0 {P : PointRep F} (hPz : P.z ≠ 0) : P ≈ ⟨P.x / P.z, P.y / P.z, 1⟩ :=
  ⟨Units.mk0 _ hPz, ⟨(mul_div_cancel' _ hPz).symm, (mul_div_cancel' _ hPz).symm, (mul_one _).symm⟩⟩

lemma nonsingular_iff_affine_of_Zne0 {P : PointRep F} (hPz : P.z ≠ 0) :
    W.nonsingular P ↔ W.toAffine.nonsingular (P.x / P.z) (P.y / P.z) :=
  (W.nonsingular_of_equiv <| equiv_some_of_Zne0 hPz).trans <| W.nonsingular_some ..

lemma nonsingular_of_affine_of_Zne0 {P : PointRep F}
    (h : W.toAffine.nonsingular (P.x / P.z) (P.y / P.z)) (hPz : P.z ≠ 0) : W.nonsingular P :=
  (nonsingular_iff_affine_of_Zne0 hPz).mpr h

lemma nonsingular_affine_of_Zne0 {P : PointRep F} (h : W.nonsingular P) (hPz : P.z ≠ 0) :
    W.toAffine.nonsingular (P.x / P.z) (P.y / P.z) :=
  (nonsingular_iff_affine_of_Zne0 hPz).mp h

end Equation

section Polynomial

/-! ### Group operation polynomials -/

/-- The $Y$-coordinate of the negation of a point representative. -/
@[pp_dot, simp]
def negY (P : PointRep R) : R :=
  -P.y - W.a₁ * P.x - W.a₃ * P.z

lemma negY_mul (P : PointRep R) (u : Rˣ) : W.negY ⟨u * P.x, u * P.y, u * P.z⟩ = u * W.negY P := by
  simp only [negY]
  ring1

/-- The truncated $X$-coordinate of the addition of two point representatives, where their
$Z$-coordinates are non-zero and their $X$-coordinates divided by $Z$-coordinates are distinct.
This is only an auxiliary definition needed to define `WeierstrassCurve.Projective.addY'_of_Xne`,
and the full $X$-coordinate is defined in `WeierstrassCurve.Projective.addX_of_Xne`. -/
@[pp_dot, simp]
def addX'_of_Xne (P Q : PointRep R) : R :=
  P.z * Q.z * (P.y * Q.z - P.z * Q.y) ^ 2
    + W.a₁ * P.z * Q.z * (P.y * Q.z - P.z * Q.y) * (P.x * Q.z - P.z * Q.x)
    - (W.a₂ * P.z * Q.z + P.x * Q.z + P.z * Q.x) * (P.x * Q.z - P.z * Q.x) ^ 2

lemma addX'_of_Xne_mul (P Q : PointRep R) (u v : Rˣ) :
    W.addX'_of_Xne ⟨u * P.x, u * P.y, u * P.z⟩ ⟨v * Q.x, v * Q.y, v * Q.z⟩ =
      (u : R) ^ 3 * (v : R) ^ 3 * W.addX'_of_Xne P Q := by
  simp only [addX'_of_Xne]
  ring1

/-- The truncated $X$-coordinate of the doubling of a point representative, where its
$Z$-coordinate is non-zero and its $Y$-coordinate is distinct from that of its negation.
This is only an auxiliary definition needed to define `WeierstrassCurve.Projective.addY'_of_Yne`,
and the full $X$-coordinate is defined in `WeierstrassCurve.Projective.addX_of_Yne`. -/
@[pp_dot, simp]
def addX'_of_Yne (P : PointRep R) : R :=
  (3 * P.x ^ 2 + 2 * W.a₂ * P.x * P.z + W.a₄ * P.z ^ 2 - W.a₁ * P.y * P.z) ^ 2
    + W.a₁ * P.z * (3 * P.x ^ 2 + 2 * W.a₂ * P.x * P.z + W.a₄ * P.z ^ 2 - W.a₁ * P.y * P.z)
      * (P.y - W.negY P)
    - (W.a₂ * P.z ^ 2 + 2 * P.x * P.z) * (P.y - W.negY P) ^ 2

lemma addX'_of_Yne_mul (P : PointRep R) (u : Rˣ) :
    W.addX'_of_Yne ⟨u * P.x, u * P.y, u * P.z⟩ = (u : R) ^ 4 * W.addX'_of_Yne P := by
  simp only [addX'_of_Yne, negY_mul]
  ring1

/-- The $Y$-coordinate of the addition of two point representatives, before applying the final
negation that maps $Y$ to $-Y - a_1X - a_3Z$, where their $Z$-coordinates are non-zero and their
$X$-coordinates divided by $Z$-coordinates are distinct. -/
@[pp_dot, simp]
def addY'_of_Xne (P Q : PointRep R) : R :=
  (P.y * Q.z - P.z * Q.y) * (W.addX'_of_Xne P Q - P.x * Q.z * (P.x * Q.z - P.z * Q.x) ^ 2)
    + P.y * Q.z * (P.x * Q.z - P.z * Q.x) ^ 3

lemma addY'_of_Xne_mul (P Q : PointRep R) (u v : Rˣ) :
    W.addY'_of_Xne ⟨u * P.x, u * P.y, u * P.z⟩ ⟨v * Q.x, v * Q.y, v * Q.z⟩ =
      (u : R) ^ 4 * (v : R) ^ 4 * W.addY'_of_Xne P Q := by
  simp only [addY'_of_Xne, addX'_of_Xne_mul]
  ring1

/-- The $Y$-coordinate of the doubling of a point representative, before applying the final negation
that maps $Y$ to $-Y - a_1X - a_3Z$, where its $Z$-coordinate is non-zero and its $Y$-coordinate is
distinct from that of its negation. -/
@[pp_dot, simp]
def addY'_of_Yne (P : PointRep R) : R :=
  (3 * P.x ^ 2 + 2 * W.a₂ * P.x * P.z + W.a₄ * P.z ^ 2 - W.a₁ * P.y * P.z)
      * (W.addX'_of_Yne P - P.x * P.z * (P.y - W.negY P) ^ 2)
    + P.y * (P.z ^ 2 * (P.y - W.negY P) ^ 3)

lemma addY'_of_Yne_mul (P : PointRep R) (u : Rˣ) :
    W.addY'_of_Yne ⟨u * P.x, u * P.y, u * P.z⟩ = (u : R) ^ 6 * W.addY'_of_Yne P := by
  simp only [addY'_of_Yne, negY_mul, addX'_of_Yne_mul]
  ring1

/-- The $Z$-coordinate of the addition of two point representatives, where their $Z$-coordinates are
non-zero and their $X$-coordinates divided by $Z$-coordinates are distinct. -/
@[simp]
def addZ_of_Xne (P Q : PointRep R) : R :=
  P.z * Q.z * (P.x * Q.z - P.z * Q.x) ^ 3

lemma addZ_of_Xne_mul (P Q : PointRep R) (u v : Rˣ) :
    addZ_of_Xne ⟨u * P.x, u * P.y, u * P.z⟩ ⟨v * Q.x, v * Q.y, v * Q.z⟩ =
      (u : R) ^ 4 * (v : R) ^ 4 * addZ_of_Xne P Q := by
  simp only [addZ_of_Xne]
  ring1

/-- The $Z$-coordinate of the doubling of a point representative, where its $Z$-coordinate is
non-zero and its $Y$-coordinate is distinct from that of its negation. -/
@[pp_dot, simp]
def addZ_of_Yne (P : PointRep R) : R :=
  P.z ^ 3 * (P.y - W.negY P) ^ 3

lemma addZ_of_Yne_mul (P : PointRep R) (u : Rˣ) :
    W.addZ_of_Yne ⟨u * P.x, u * P.y, u * P.z⟩ = (u : R) ^ 6 * W.addZ_of_Yne P := by
  simp only [addZ_of_Yne, negY_mul]
  ring1

/-- The $X$-coordinate of the addition of two point representatives, where their $Z$-coordinates are
non-zero and their $X$-coordinates divided by $Z$-coordinates are distinct. -/
@[pp_dot, simp]
def addX_of_Xne (P Q : PointRep R) : R :=
  W.addX'_of_Xne P Q * (P.x * Q.z - P.z * Q.x)

lemma addX_of_Xne_mul (P Q : PointRep R) (u v : Rˣ) :
    W.addX_of_Xne ⟨u * P.x, u * P.y, u * P.z⟩ ⟨v * Q.x, v * Q.y, v * Q.z⟩ =
      (u : R) ^ 4 * (v : R) ^ 4 * W.addX_of_Xne P Q := by
  simp only [addX_of_Xne, addX'_of_Xne_mul]
  ring1

/-- The $X$-coordinate of the doubling of a point representative, where its $Z$-coordinate is
non-zero and its $Y$-coordinate is distinct from that of its negation. -/
@[pp_dot, simp]
def addX_of_Yne (P : PointRep R) : R :=
  W.addX'_of_Yne P * P.z * (P.y - W.negY P)

lemma addX_of_Yne_mul (P : PointRep R) (u : Rˣ) :
    W.addX_of_Yne ⟨u * P.x, u * P.y, u * P.z⟩ = (u : R) ^ 6 * W.addX_of_Yne P := by
  simp only [addX_of_Yne, negY_mul, addX'_of_Yne_mul]
  ring1

/-- The $Y$-coordinate of the addition of two point representatives, where their $Z$-coordinates are
non-zero and their $X$-coordinates divided by $Z$-coordinates are distinct. -/
@[pp_dot, simp]
def addY_of_Xne (P Q : PointRep R) : R :=
  W.negY <| ⟨W.addX_of_Xne P Q, W.addY'_of_Xne P Q, addZ_of_Xne P Q⟩

lemma addY_of_Xne_mul (P Q : PointRep R) (u v : Rˣ) :
    W.addY_of_Xne ⟨u * P.x, u * P.y, u * P.z⟩ ⟨v * Q.x, v * Q.y, v * Q.z⟩ =
      (u : R) ^ 4 * (v : R) ^ 4 * W.addY_of_Xne P Q := by
  simp only [addY_of_Xne, negY, addX_of_Xne_mul, addY'_of_Xne_mul, addZ_of_Xne_mul]
  ring1

/-- The $Y$-coordinate of the doubling of a point representative, where its $Z$-coordinate is
non-zero and its $Y$-coordinate is distinct from that of its negation. -/
@[pp_dot, simp]
def addY_of_Yne (P : PointRep R) : R :=
  W.negY <| ⟨W.addX_of_Yne P, W.addY'_of_Yne P, W.addZ_of_Yne P⟩

lemma addY_of_Yne_mul (P : PointRep R) (u : Rˣ) :
    W.addY_of_Yne ⟨u * P.x, u * P.y, u * P.z⟩ = (u : R) ^ 6 * W.addY_of_Yne P := by
  simp only [addY_of_Yne, negY, addX_of_Yne_mul, addY'_of_Yne_mul, addZ_of_Yne_mul]
  ring1

end Polynomial

section Group

/-! ### Group operations -/

/-- The negation of a point representative. -/
@[pp_dot]
def neg (P : PointRep R) : PointRep R :=
  ⟨P.x, W.negY P, P.z⟩

@[simp]
lemma neg_zero : W.neg ⟨0, 1, 0⟩ = ⟨0, -1, 0⟩ := by
  simp only [neg, negY, sub_zero, mul_zero]

@[simp]
lemma neg_some (x y : R) : W.neg ⟨x, y, 1⟩ = ⟨x, -y - W.a₁ * x - W.a₃, 1⟩ := by
  simp only [neg, negY, mul_one]

lemma neg_equiv {P Q : PointRep R} (h : P ≈ Q) : W.neg P ≈ W.neg Q := by
  rcases P, h with ⟨⟨_, _, _⟩, ⟨u, ⟨rfl, rfl, rfl⟩⟩⟩
  exact ⟨u, ⟨rfl, W.negY_mul Q u, rfl⟩⟩

/-- The negation of a point class. If `P` is a point representative,
then `W.neg_map ⟦P⟧` is definitionally equivalent to `W.neg P`. -/
@[pp_dot]
def neg_map (P : PointClass R) : PointClass R :=
  P.map W.neg fun _ _ => W.neg_equiv

lemma neg_map_eq {P : PointRep R} : W.neg_map ⟦P⟧ = ⟦W.neg P⟧ :=
  rfl

@[simp]
lemma neg_map_zero : W.neg_map ⟦⟨0, 1, 0⟩⟧ = ⟦⟨0, 1, 0⟩⟧ := by
  simpa only [neg_map_eq, neg_zero, Quotient.eq] using ⟨-1, by simp⟩

@[simp]
lemma neg_map_some (x y : R) : W.neg_map ⟦⟨x, y, 1⟩⟧ = ⟦⟨x, -y - W.a₁ * x - W.a₃, 1⟩⟧ := by
  rw [neg_map_eq, neg_some]

open scoped Classical

/-- The addition of two point representatives. -/
@[pp_dot]
noncomputable def add (P Q : PointRep R) : PointRep R :=
  if P.z = 0 then Q else if Q.z = 0 then P else if P.x * Q.z = P.z * Q.x then
    if P.y * Q.z = P.z * W.negY Q then ⟨0, 1, 0⟩ else
      ⟨W.addX_of_Yne P, W.addY_of_Yne P, W.addZ_of_Yne P⟩
  else ⟨W.addX_of_Xne P Q, W.addY_of_Xne P Q, addZ_of_Xne P Q⟩

@[simp]
lemma add_of_Zeq0_left {P Q : PointRep R} (hPz : P.z = 0) : W.add P Q = Q :=
  if_pos hPz

lemma add_zero_left (P : PointRep R) : W.add ⟨0, 1, 0⟩ P = P :=
  W.add_of_Zeq0_left rfl

@[simp]
lemma add_of_Zeq0_right {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z = 0) : W.add P Q = P := by
  rw [add, if_neg hPz, if_pos hQz]

lemma add_zero_right {P : PointRep R} (hPz : P.z ≠ 0) : W.add P ⟨0, 1, 0⟩ = P :=
  W.add_of_Zeq0_right hPz rfl

@[simp]
lemma add_of_Yeq {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x)
    (hy : P.y * Q.z = P.z * W.negY Q) : W.add P Q = ⟨0, 1, 0⟩ := by
  rw [add, if_neg hPz, if_neg hQz, if_pos hx, if_pos hy]

@[simp]
lemma add_of_Yne {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x)
    (hy : P.y * Q.z ≠ P.z * W.negY Q) :
    W.add P Q = ⟨W.addX_of_Yne P, W.addY_of_Yne P, W.addZ_of_Yne P⟩ := by
  rw [add, if_neg hPz, if_neg hQz, if_pos hx, if_neg hy]

@[simp]
lemma add_of_Xne {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z ≠ P.z * Q.x) :
    W.add P Q = ⟨W.addX_of_Xne P Q, W.addY_of_Xne P Q, addZ_of_Xne P Q⟩ := by
  rw [add, if_neg hPz, if_neg hQz, if_neg hx]

variable [IsDomain R]

lemma add_mul_equiv (P Q : PointRep R) (u v : Rˣ) :
    W.add ⟨u * P.x, u * P.y, u * P.z⟩ ⟨v * Q.x, v * Q.y, v * Q.z⟩ ≈ W.add P Q := by
  have huv : (u * v : R) ≠ 0 := mul_ne_zero u.ne_zero v.ne_zero
  by_cases hPz : P.z = 0
  · rw [hPz, mul_zero, W.add_of_Zeq0_left <| by exact rfl, W.add_of_Zeq0_left hPz]
    exact ⟨v, ⟨rfl, rfl, rfl⟩⟩
  · have huz : (⟨u * P.x, u * P.y, u * P.z⟩ : PointRep R).z ≠ 0 := mul_ne_zero u.ne_zero hPz
    by_cases hQz : Q.z = 0
    · rw [hQz, mul_zero, W.add_of_Zeq0_right huz <| by exact rfl, W.add_of_Zeq0_right hPz hQz]
      exact ⟨u, ⟨rfl, rfl, rfl⟩⟩
    · have hvz : (⟨v * Q.x, v * Q.y, v * Q.z⟩ : PointRep R).z ≠ 0 := mul_ne_zero v.ne_zero hQz
      by_cases hx : P.x * Q.z = P.z * Q.x
      · by_cases hy : P.y * Q.z = P.z * W.negY Q
        · rw [W.add_of_Yeq huz hvz (by rw [mul_mul_mul_comm, hx, mul_mul_mul_comm]) <|
            by simp only [negY_mul, mul_mul_mul_comm, hy], W.add_of_Yeq hPz hQz hx hy]
        · rw [W.add_of_Yne huz hvz (by rw [mul_mul_mul_comm, hx, mul_mul_mul_comm]) <|
            by simpa only [negY_mul, mul_mul_mul_comm] using hy ∘ mul_left_cancel₀ huv,
            W.add_of_Yne hPz hQz hx hy]
          exact ⟨u ^ 6, by simp only [Units.val_pow_eq_pow_val,
            addX_of_Yne_mul, addY_of_Yne_mul, addZ_of_Yne_mul, and_self]⟩
      · rw [W.add_of_Xne huz hvz <|
          by simpa only [mul_mul_mul_comm] using hx ∘ mul_left_cancel₀ huv, W.add_of_Xne hPz hQz hx]
        exact ⟨u ^ 4 * v ^ 4, by simp only [Units.val_mul, Units.val_pow_eq_pow_val,
          addX_of_Xne_mul, addY_of_Xne_mul, addZ_of_Xne_mul, and_self]⟩

lemma add_equiv {P P' Q Q' : PointRep R} (hP : P ≈ P') (hQ : Q ≈ Q') : W.add P Q ≈ W.add P' Q' := by
  rcases P, Q with ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩
  rcases hP, hQ with ⟨⟨u, ⟨rfl, rfl, rfl⟩⟩, ⟨v, ⟨rfl, rfl, rfl⟩⟩⟩
  exact W.add_mul_equiv P' Q' u v

/-- The addition of two point classes. If `P` is a point representative,
then `W.add_map ⟦P⟧ ⟦Q⟧` is definitionally equivalent to `W.add P Q`. -/
@[pp_dot]
noncomputable def add_map (P Q : PointClass R) : PointClass R :=
  Quotient.map₂ W.add (fun _ _ hP _ _ hQ => W.add_equiv hP hQ) P Q

lemma add_map_eq (P Q : PointRep R) : W.add_map ⟦P⟧ ⟦Q⟧ = ⟦W.add P Q⟧ :=
  rfl

@[simp]
lemma add_map_of_Zeq0_left {P : PointRep R} {Q : PointClass R} (hPz : P.z = 0) :
    W.add_map ⟦P⟧ Q = Q := by
  rcases Q with ⟨Q⟩
  erw [add_map_eq, W.add_of_Zeq0_left hPz]
  rfl

lemma add_map_zero_left (P : PointClass R) : W.add_map ⟦⟨0, 1, 0⟩⟧ P = P :=
  W.add_map_of_Zeq0_left rfl

@[simp]
lemma add_map_of_Zeq0_right {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z = 0) :
    W.add_map ⟦P⟧ ⟦Q⟧ = ⟦P⟧ := by
  rw [add_map_eq, W.add_of_Zeq0_right hPz hQz]

lemma add_map_zero_right {P : PointRep R} (hPz : P.z ≠ 0) : W.add_map ⟦P⟧ ⟦⟨0, 1, 0⟩⟧ = ⟦P⟧ := by
  rw [add_map_eq, W.add_zero_right hPz]

@[simp]
lemma add_map_of_Yeq {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x)
    (hy : P.y * Q.z = P.z * W.negY Q) : W.add_map ⟦P⟧ ⟦Q⟧ = ⟦⟨0, 1, 0⟩⟧ := by
  rw [add_map_eq, W.add_of_Yeq hPz hQz hx hy]

@[simp]
lemma add_map_of_Yne {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x)
    (hy : P.y * Q.z ≠ P.z * W.negY Q) :
    W.add_map ⟦P⟧ ⟦Q⟧ = ⟦⟨W.addX_of_Yne P, W.addY_of_Yne P, W.addZ_of_Yne P⟩⟧ := by
  rw [add_map_eq, W.add_of_Yne hPz hQz hx hy]

@[simp]
lemma add_map_of_Xne {P Q : PointRep R} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0)
    (hx : P.x * Q.z ≠ P.z * Q.x) :
    W.add_map ⟦P⟧ ⟦Q⟧ = ⟦⟨W.addX_of_Xne P Q, W.addY_of_Xne P Q, addZ_of_Xne P Q⟩⟧ := by
  rw [add_map_eq, W.add_of_Xne hPz hQz hx]

variable {F : Type u} [Field F] {W : Projective F}

@[simp]
lemma add_map_of_Zeq0_right' {P : PointClass F} {Q : PointRep F} (hP : W.nonsingular_lift P)
    (hQ : W.nonsingular Q) (hQz : Q.z = 0) : W.add_map P ⟦Q⟧ = P := by
  rcases P with ⟨P⟩
  by_cases hPz : P.z = 0
  · erw [W.add_map_of_Zeq0_left hPz, Quotient.eq]
    exact equiv_of_Zeq0 hQ hP hQz hPz
  · exact W.add_map_of_Zeq0_right hPz hQz

lemma add_map_zero_right' {P : PointClass F} (hP : W.nonsingular_lift P) :
    W.add_map P ⟦⟨0, 1, 0⟩⟧ = P :=
  add_map_of_Zeq0_right' hP W.nonsingular_zero rfl

end Group

section Nonsingular

/-! ### Group operations preserve nonsingularity -/

variable {F : Type u} [Field F] {W : Projective F}

private lemma negY_divZ {P : PointRep F} (hPz : P.z ≠ 0) :
    W.negY P / P.z = W.toAffine.negY (P.x / P.z) (P.y / P.z) := by
  rw [negY, Affine.negY]
  linear_combination (norm := ring1) -W.a₃ * mul_inv_cancel hPz

/-- The negation of a nonsingular point representative in `W` lies in `W`. -/
lemma nonsingular_neg {P : PointRep F} (h : W.nonsingular P) : W.nonsingular <| W.neg P := by
  by_cases hPz : P.z = 0
  · rw [W.nonsingular_of_equiv <| W.neg_equiv <| equiv_zero_of_Zeq0 h hPz, neg_zero]
    exact W.nonsingular_zero' <| neg_ne_zero.mpr one_ne_zero
  · rw [nonsingular_iff_affine_of_Zne0 <| by exact hPz] at h ⊢
    rwa [← Affine.nonsingular_neg_iff, ← negY_divZ hPz] at h

lemma nonsingular_lift_neg_map {P : PointClass F} (h : W.nonsingular_lift P) :
    W.nonsingular_lift <| W.neg_map P := by
  rcases P with ⟨_⟩
  exact nonsingular_neg h

private lemma Yne_of_Yne {P Q : PointRep F} (hP : W.nonsingular P) (hQ : W.nonsingular Q)
    (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x) (hy : P.y * Q.z ≠ P.z * W.negY Q) :
    P.y ≠ W.negY P := by
  simp only [mul_comm P.z, ne_eq, ← div_eq_div_iff hPz hQz] at hx hy
  have hy' : P.y / P.z = Q.y / Q.z := Affine.Yeq_of_Yne (nonsingular_affine_of_Zne0 hP hPz).left
    (nonsingular_affine_of_Zne0 hQ hQz).left hx <| (negY_divZ hQz).symm ▸ hy
  simp_rw [negY, sub_div, neg_div, mul_div_assoc, ← hy', ← hx, div_self hQz, ← div_self hPz,
    ← mul_div_assoc, ← neg_div, ← sub_div, div_left_inj' hPz] at hy
  exact hy

private lemma addX_of_Xne_div_addZ_of_Xne_of_Yne {P Q : PointRep F} (hP : W.nonsingular P)
    (hQ : W.nonsingular Q) (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x)
    (hy : P.y * Q.z ≠ P.z * W.negY Q) : (W.add P Q).x / (W.add P Q).z =
      W.toAffine.addX (P.x / P.z) (Q.x / Q.z)
        (W.toAffine.slope (P.x / P.z) (Q.x / Q.z) (P.y / P.z) (Q.y / Q.z)) := by
  have : P.y - W.negY P ≠ 0 := sub_ne_zero_of_ne <| Yne_of_Yne hP hQ hPz hQz hx hy
  rw [W.add_of_Yne hPz hQz hx hy]
  simp only [mul_comm P.z, ne_eq, ← div_eq_div_iff hPz hQz] at hx hy
  rw [Affine.slope_of_Yne hx <| (negY_divZ hQz).symm ▸ hy, ← hx, ← negY_divZ hPz]
  sorry
  -- field_simp
  -- ring1

private lemma addX_of_Xne_div_addZ_of_Xne_of_Xne {P Q : PointRep F} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0)
    (hx : P.x * Q.z ≠ P.z * Q.x) : (W.add P Q).x / (W.add P Q).z =
      W.toAffine.addX (P.x / P.z) (Q.x / Q.z)
        (W.toAffine.slope (P.x / P.z) (Q.x / Q.z) (P.y / P.z) (Q.y / Q.z)) := by
  have : P.x * Q.z - P.z * Q.x ≠ 0 := sub_ne_zero_of_ne hx
  rw [W.add_of_Xne hPz hQz hx,
    Affine.slope_of_Xne <| by rwa [ne_eq, div_eq_div_iff hPz hQz, mul_comm Q.x]]
  sorry
  -- field_simp
  -- ring1

private lemma addY_of_Xne_div_addZ_of_Xne_of_Yne {P Q : PointRep F} (hP : W.nonsingular P)
    (hQ : W.nonsingular Q) (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x)
    (hy : P.y * Q.z ≠ P.z * W.negY Q) : (W.add P Q).y / (W.add P Q).z =
      W.toAffine.addY (P.x / P.z) (Q.x / Q.z) (P.y / P.z)
        (W.toAffine.slope (P.x / P.z) (Q.x / Q.z) (P.y / P.z) (Q.y / Q.z)) := by
  have : P.y - W.negY P ≠ 0 := sub_ne_zero_of_ne <| Yne_of_Yne hP hQ hPz hQz hx hy
  rw [W.add_of_Yne hPz hQz hx hy]
  simp only [mul_comm P.z, ne_eq, ← div_eq_div_iff hPz hQz] at hx hy
  rw [Affine.slope_of_Yne hx <| (negY_divZ hQz).symm ▸ hy, ← hx, ← negY_divZ hPz]
  sorry
  -- field_simp
  -- ring1

private lemma addY_of_Xne_div_addZ_of_Xne_of_Xne {P Q : PointRep F} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0)
    (hx : P.x * Q.z ≠ P.z * Q.x) : (W.add P Q).y / (W.add P Q).z =
      W.toAffine.addY (P.x / P.z) (Q.x / Q.z) (P.y / P.z)
        (W.toAffine.slope (P.x / P.z) (Q.x / Q.z) (P.y / P.z) (Q.y / Q.z)) := by
  have : P.x * Q.z - P.z * Q.x ≠ 0 := sub_ne_zero_of_ne hx
  rw [W.add_of_Xne hPz hQz hx,
    Affine.slope_of_Xne <| by rwa [ne_eq, div_eq_div_iff hPz hQz, mul_comm Q.x]]
  sorry
  -- field_simp
  -- ring1

private lemma addZ_of_Xne_ne_zero_of_Yne {P Q : PointRep F} (hP : W.nonsingular P)
    (hQ : W.nonsingular Q) (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0) (hx : P.x * Q.z = P.z * Q.x)
    (hy : P.y * Q.z ≠ P.z * W.negY Q) : (W.add P Q).z ≠ 0 := by
  rw [W.add_of_Yne hPz hQz hx hy]
  exact mul_ne_zero (pow_ne_zero 3 hPz) <| pow_ne_zero 3 <| sub_ne_zero_of_ne <|
    Yne_of_Yne hP hQ hPz hQz hx hy

private lemma addZ_of_Xne_ne_zero_of_Xne {P Q : PointRep F} (hPz : P.z ≠ 0) (hQz : Q.z ≠ 0)
    (hx : P.x * Q.z ≠ P.z * Q.x) : (W.add P Q).z ≠ 0 := by
  rw [W.add_of_Xne hPz hQz hx]
  exact mul_ne_zero (mul_ne_zero hPz hQz) <| pow_ne_zero 3 <| sub_ne_zero_of_ne hx

/-- The addition of two nonsingular point representatives in `W` lies in `W`. -/
lemma nonsingular_add {P Q : PointRep F} (hP : W.nonsingular P) (hQ : W.nonsingular Q) :
    W.nonsingular <| W.add P Q := by
  by_cases hPz : P.z = 0
  · rwa [W.nonsingular_of_equiv <| W.add_equiv (equiv_zero_of_Zeq0 hP hPz) <| Setoid.refl Q,
      W.add_of_Zeq0_left <| by exact rfl]
  · by_cases hQz : Q.z = 0
    · rwa [W.nonsingular_of_equiv <| W.add_equiv (Setoid.refl P) <| equiv_zero_of_Zeq0 hQ hQz,
        W.add_of_Zeq0_right hPz <| by exact rfl]
    · by_cases hx : P.x * Q.z = P.z * Q.x
      · by_cases hy : P.y * Q.z = P.z * W.negY Q
        · simpa only [W.add_of_Yeq hPz hQz hx hy] using W.nonsingular_zero
        · rw [nonsingular_iff_affine_of_Zne0 <| addZ_of_Xne_ne_zero_of_Yne hP hQ hPz hQz hx hy,
            addX_of_Xne_div_addZ_of_Xne_of_Yne hP hQ hPz hQz hx hy,
            addY_of_Xne_div_addZ_of_Xne_of_Yne hP hQ hPz hQz hx hy]
          exact W.toAffine.nonsingular_add (nonsingular_affine_of_Zne0 hP hPz)
            (nonsingular_affine_of_Zne0 hQ hQz)
            fun _ => (negY_divZ hQz).symm ▸ (mul_comm P.z _ ▸ hy) ∘ (div_eq_div_iff hPz hQz).mp
      · rw [nonsingular_iff_affine_of_Zne0 <| addZ_of_Xne_ne_zero_of_Xne hPz hQz hx,
          addX_of_Xne_div_addZ_of_Xne_of_Xne hPz hQz hx,
          addY_of_Xne_div_addZ_of_Xne_of_Xne hPz hQz hx]
        exact W.toAffine.nonsingular_add (nonsingular_affine_of_Zne0 hP hPz)
          (nonsingular_affine_of_Zne0 hQ hQz)
          fun h => (hx <| mul_comm Q.x P.z ▸ (div_eq_div_iff hPz hQz).mp h).elim

lemma nonsingular_lift_add_map {P Q : PointClass F} (hP : W.nonsingular_lift P)
    (hQ : W.nonsingular_lift Q) : W.nonsingular_lift <| W.add_map P Q := by
  rcases P, Q with ⟨⟨_⟩, ⟨_⟩⟩
  exact nonsingular_add hP hQ

end Nonsingular

section Group

/-! ### Group operations -/

/-- A nonsingular rational point on `W`. -/
@[pp_dot]
structure Point where
  {point : PointClass R}
  (nonsingular : W.nonsingular_lift point)

attribute [pp_dot] Point.point
attribute [pp_dot] Point.nonsingular

/-- The point class underlying a nonsingular rational point on `W`. -/
add_decl_doc Point.point

/-- The nonsingular condition underlying a nonsingular rational point on `W`. -/
add_decl_doc Point.nonsingular

namespace Point

variable {W}

instance instZeroPoint [Nontrivial R] : Zero W.Point :=
  ⟨⟨W.nonsingular_lift_zero⟩⟩

lemma zero_def [Nontrivial R] : (⟨W.nonsingular_lift_zero⟩ : W.Point) = 0 :=
  rfl

/-- The map from a nonsingular rational point on a Weierstrass curve `W` in affine coordinates
to the corresponding nonsingular rational point on `W` in projective coordinates. -/
def fromAffine [Nontrivial R] : W.toAffine.Point → W.Point
  | 0 => 0
  | Affine.Point.some h => ⟨(W.nonsingular_lift_some ..).mpr h⟩

@[simp]
lemma fromAffine_zero [Nontrivial R] : fromAffine 0 = (0 : W.Point) :=
  rfl

@[simp]
lemma fromAffine_some [Nontrivial R] {x y : R} (h : W.toAffine.nonsingular x y) :
    fromAffine (Affine.Point.some h) = ⟨(W.nonsingular_lift_some ..).mpr h⟩ :=
  rfl

variable {F : Type u} [Field F] {W : Projective F}

/-- The negation of a nonsingular rational point on `W`.

Given a nonsingular rational point `P` on `W`, use `-P` instead of `neg P`. -/
@[pp_dot]
def neg (P : W.Point) : W.Point :=
  ⟨W.nonsingular_lift_neg_map P.nonsingular⟩

instance instNegPoint : Neg W.Point :=
  ⟨neg⟩

lemma neg_def (P : W.Point) : P.neg = -P :=
  rfl

@[simp]
lemma neg_zero : (-⟨W.nonsingular_lift_zero⟩ : W.Point) = ⟨W.nonsingular_lift_zero⟩ := by
  simp only [← neg_def, neg, neg_map_zero]

/-- The addition of two nonsingular rational points on `W`.

Given two nonsingular rational points `P` and `Q` on `W`, use `P + Q` instead of `add P Q`. -/
@[pp_dot]
noncomputable def add (P Q : W.Point) : W.Point :=
  ⟨W.nonsingular_lift_add_map P.nonsingular Q.nonsingular⟩

noncomputable instance instAddPoint : Add W.Point :=
  ⟨add⟩

lemma add_def (P Q : W.Point) : P.add Q = P + Q :=
  rfl

@[simp]
lemma zero_add (P : W.Point) : ⟨W.nonsingular_lift_zero⟩ + P = P := by
  simp only [← add_def, add, add_map_zero_left]

@[simp]
lemma add_zero (P : W.Point) : P + ⟨W.nonsingular_lift_zero⟩ = P := by
  simp only [← add_def, add, add_map_zero_right' P.nonsingular]

noncomputable instance instAddZeroClassPoint : AddZeroClass W.Point where
  zero_add := zero_add
  add_zero := add_zero

open scoped Classical

/-- The map from a point representative that is nonsingular on a Weierstrass curve `W` in projective
coordinates to the corresponding nonsingular rational point on `W` in affine coordinates. -/
noncomputable def toAffine {P : PointRep F} (h : W.nonsingular P) : W.toAffine.Point :=
  if hPz : P.z = 0 then 0 else Affine.Point.some <| nonsingular_affine_of_Zne0 h hPz

lemma toAffine_of_Zeq0 {P : PointRep F} {h : W.nonsingular P} (hPz : P.z = 0) : toAffine h = 0 :=
  dif_pos hPz

lemma toAffine_zero : toAffine W.nonsingular_zero = 0 :=
  toAffine_of_Zeq0 rfl

lemma toAffine_of_Zne0 {P : PointRep F} {h : W.nonsingular P} (hPz : P.z ≠ 0) :
    toAffine h = Affine.Point.some (nonsingular_affine_of_Zne0 h hPz) :=
  dif_neg hPz

lemma toAffine_some {x y : F} (h : W.nonsingular ⟨x, y, 1⟩) :
    toAffine h = Affine.Point.some ((W.nonsingular_some x y).mp h) := by
  rw [toAffine_of_Zne0 <| by exact one_ne_zero]
  simp only [div_one]

lemma toAffine_neg {P : PointRep F} (hP : W.nonsingular P) :
    toAffine (nonsingular_neg hP) = -toAffine hP := by
  by_cases hPz : P.z = 0
  · rw [toAffine_of_Zeq0 <| by exact hPz, toAffine_of_Zeq0 hPz, Affine.Point.neg_zero]
  · rw [toAffine_of_Zne0 <| by exact hPz, toAffine_of_Zne0 hPz, Affine.Point.neg_some,
      Affine.Point.some.injEq]
    exact ⟨rfl, negY_divZ hPz⟩

lemma toAffine_add {P Q : PointRep F} (hP : W.nonsingular P) (hQ : W.nonsingular Q) :
    toAffine (nonsingular_add hP hQ) = toAffine hP + toAffine hQ := by
  by_cases hPz : P.z = 0
  · simp only [W.add_of_Zeq0_left hPz, toAffine_of_Zeq0 hPz, _root_.zero_add]
  · by_cases hQz : Q.z = 0
    · simp only [W.add_of_Zeq0_right hPz hQz, toAffine_of_Zeq0 hQz, _root_.add_zero]
    · by_cases hx : P.x * Q.z = P.z * Q.x
      · have hx' : P.x / P.z = Q.x / Q.z := (div_eq_div_iff hPz hQz).mpr <| mul_comm P.z _ ▸ hx
        rw [toAffine_of_Zne0 hPz, toAffine_of_Zne0 hQz]
        by_cases hy : P.y * Q.z = P.z * W.negY Q
        · have hy' : P.y / P.z = W.negY Q / Q.z :=
            (div_eq_div_iff hPz hQz).mpr <| mul_comm P.z _ ▸ hy
          simp only [W.add_of_Yeq hPz hQz hx hy]
          rw [toAffine_zero, Affine.Point.some_add_some_of_Yeq hx' <| by rwa [← negY_divZ hQz]]
        · have hy' : P.y / P.z ≠ W.negY Q / Q.z :=
            (mul_comm P.z _ ▸ hy) ∘ (div_eq_div_iff hPz hQz).mp
          rw [toAffine_of_Zne0 <| addZ_of_Xne_ne_zero_of_Yne hP hQ hPz hQz hx hy,
            Affine.Point.some_add_some_of_Yne hx' <| (negY_divZ hQz).symm ▸ hy',
            Affine.Point.some.injEq]
          exact ⟨addX_of_Xne_div_addZ_of_Xne_of_Yne hP hQ hPz hQz hx hy,
            addY_of_Xne_div_addZ_of_Xne_of_Yne hP hQ hPz hQz hx hy⟩
      · have hx' : P.x / P.z ≠ Q.x / Q.z := (mul_comm P.z _ ▸ hx) ∘ (div_eq_div_iff hPz hQz).mp
        rw [toAffine_of_Zne0 <| addZ_of_Xne_ne_zero_of_Xne hPz hQz hx, toAffine_of_Zne0 hPz,
          toAffine_of_Zne0 hQz, Affine.Point.some_add_some_of_Xne hx', Affine.Point.some.injEq]
        exact ⟨addX_of_Xne_div_addZ_of_Xne_of_Xne hPz hQz hx,
          addY_of_Xne_div_addZ_of_Xne_of_Xne hPz hQz hx⟩

lemma toAffine_of_equiv (P Q : PointRep F) (h : P ≈ Q) :
    HEq (toAffine (W := W) (P := P)) (toAffine (W := W) (P := Q)) := by
  rcases P, h with ⟨⟨_, _, _⟩, ⟨u, ⟨rfl, rfl, rfl⟩⟩⟩
  refine Function.hfunext (propext <| W.nonsingular_mul_iff Q u) <| fun _ _ _ => ?_
  by_cases hPz : Q.z = 0
  · rw [toAffine_of_Zeq0 <| by exact u.mul_right_eq_zero.mpr hPz, toAffine_of_Zeq0 hPz]
  · rw [toAffine_of_Zne0 <| by exact mul_ne_zero u.ne_zero hPz, toAffine_of_Zne0 hPz]
    simp only [heq_eq_eq, Affine.Point.some.injEq, mul_div_mul_left _ _ u.ne_zero]

/-- The map from a nonsingular rational point on a Weierstrass curve `W` in projective coordinates
to the corresponding nonsingular rational point on `W` in affine coordinates. -/
noncomputable def toAffine_lift (P : W.Point) : W.toAffine.Point :=
  P.point.hrecOn (fun _ => toAffine) toAffine_of_equiv P.nonsingular

lemma toAffine_lift_eq {P : PointRep F} (h : W.nonsingular_lift ⟦P⟧) :
    toAffine_lift ⟨h⟩ = toAffine h :=
  rfl

lemma toAffine_lift_of_Zeq0 {P : PointRep F} {h : W.nonsingular_lift ⟦P⟧} (hPz : P.z = 0) :
    toAffine_lift ⟨h⟩ = 0 :=
  toAffine_of_Zeq0 hPz (h := h)

lemma toAffine_lift_zero : toAffine_lift (0 : W.Point) = 0 :=
  toAffine_zero

lemma toAffine_lift_of_Zne0 {P : PointRep F} {h : W.nonsingular_lift ⟦P⟧} (hPz : P.z ≠ 0) :
    toAffine_lift ⟨h⟩ = Affine.Point.some (nonsingular_affine_of_Zne0 h hPz) :=
  toAffine_of_Zne0 hPz (h := h)

lemma toAffine_lift_some {x y : F} (h : W.nonsingular_lift ⟦⟨x, y, 1⟩⟧) :
    toAffine_lift ⟨h⟩ = Affine.Point.some ((W.nonsingular_some x y).mp h) :=
  toAffine_some h

lemma toAffine_lift_neg {P : PointRep F} (h : W.nonsingular_lift ⟦P⟧) :
    toAffine_lift (-⟨h⟩) = -toAffine_lift ⟨h⟩ :=
  toAffine_neg h

lemma toAffine_lift_add {P Q : PointRep F} (hP : W.nonsingular_lift ⟦P⟧)
    (hQ : W.nonsingular_lift ⟦Q⟧) :
    toAffine_lift (⟨hP⟩ + ⟨hQ⟩) = toAffine_lift ⟨hP⟩ + toAffine_lift ⟨hQ⟩ :=
  toAffine_add hP hQ

/-- The equivalence between the nonsingular rational points on a Weierstrass curve `W` in projective
coordinates with the nonsingular rational points on `W` in affine coordinates. -/
@[simps]
noncomputable def toAffine_addEquiv : W.Point ≃+ W.toAffine.Point where
  toFun := toAffine_lift
  invFun := fromAffine
  left_inv := by
    rintro @⟨⟨P⟩, h⟩
    by_cases hPz : P.z = 0
    · erw [toAffine_lift_eq, toAffine_of_Zeq0 hPz, fromAffine_zero, mk.injEq, Quotient.eq]
      exact Setoid.symm <| equiv_zero_of_Zeq0 h hPz
    · erw [toAffine_lift_eq, toAffine_of_Zne0 hPz, fromAffine_some, mk.injEq, Quotient.eq]
      exact Setoid.symm <| equiv_some_of_Zne0 hPz
  right_inv := by
    rintro (_ | _)
    · erw [fromAffine_zero, toAffine_lift_zero, Affine.Point.zero_def]
    · rw [fromAffine_some, toAffine_lift_some]
  map_add' := by
    rintro @⟨⟨_⟩, _⟩ @⟨⟨_⟩, _⟩
    simpa only using toAffine_lift_add ..

end Point

end Group

end WeierstrassCurve.Projective
