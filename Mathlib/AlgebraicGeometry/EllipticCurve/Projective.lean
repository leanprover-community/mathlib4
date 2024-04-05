/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Data.MvPolynomial.PDeriv

/-!
# Projective coordinates for Weierstrass curves

This file defines the type of points on a Weierstrass curve as a tuple, consisting of an equivalence
class of triples up to scaling by a unit, satisfying a Weierstrass equation with a nonsingular
condition.

## Mathematical background

Let `W` be a Weierstrass curve over a field `F`. A point on the projective plane is an equivalence
class of triples $[x:y:z]$ with coordinates in `F` such that $(x, y, z) \sim (x', y', z')$ precisely
if there is some unit $u$ of `F` such that $(x, y, z) = (ux', uy', uz')$, with an extra condition
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

## Main definitions

 * `WeierstrassCurve.Projective.PointClass`: the equivalence class of a point representative.
 * `WeierstrassCurve.Projective.toAffine`: the Weierstrass curve in affine coordinates.
 * `WeierstrassCurve.Projective.Nonsingular`: the nonsingular condition on a point representative.
 * `WeierstrassCurve.Projective.NonsingularLift`: the nonsingular condition on a point class.

## Main statements

 * `WeierstrassCurve.Projective.polynomial_relation`: Euler's homogeneous function theorem.

## Implementation notes

A point representative is implemented as a term `P` of type `Fin 3 → R`, which allows for the vector
notation `![x, y, z]`. However, `P` is not definitionally equivalent to the expanded vector
`![P x, P y, P z]`, so the auxiliary lemma `fin3_def` can be used to convert between the two forms.
The equivalence of two point representatives `P` and `Q` is implemented as an equivalence of orbits
of the action of `Rˣ`, or equivalently that there is some unit `u` of `R` such that `P = u • Q`.
However, `u • Q` is again not definitionally equal to `![u * Q x, u * Q y, u * Q z]`, so the
auxiliary lemmas `smul_fin3` and `smul_fin3_ext` can be used to convert between the two forms.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, projective coordinates
-/

local notation "x" => 0

local notation "y" => 1

local notation "z" => 2

local macro "matrix_simp" : tactic =>
  `(tactic| simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])

universe u

/-! ## Weierstrass curves -/

/-- An abbreviation for a Weierstrass curve in projective coordinates. -/
abbrev WeierstrassCurve.Projective :=
  WeierstrassCurve

namespace WeierstrassCurve.Projective

open MvPolynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow])

local macro "pderiv_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, pderiv_mul, pderiv_pow,
    pderiv_C, pderiv_X_self, pderiv_X_of_ne one_ne_zero, pderiv_X_of_ne one_ne_zero.symm,
    pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0), pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 2),
    pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 1), pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 2)])

variable {R : Type u} [CommRing R] (W : Projective R)

lemma fin3_def (P : Fin 3 → R) : ![P x, P y, P z] = P := by
  ext n; fin_cases n <;> rfl

lemma fin3_def_ext {X Y Z : R} : ![X, Y, Z] x = X ∧ ![X, Y, Z] y = Y ∧ ![X, Y, Z] z = Z :=
  ⟨rfl, rfl, rfl⟩

lemma smul_fin3 (P : Fin 3 → R) (u : Rˣ) : u • P = ![u * P x, u * P y, u * P z] := by
  rw [← fin3_def P]
  matrix_simp
  rfl

lemma smul_fin3_ext (P : Fin 3 → R) (u : Rˣ) :
    (u • P) x = u * P x ∧ (u • P) y = u * P y ∧ (u • P) z = u * P z :=
  ⟨rfl, rfl, rfl⟩

/-- The equivalence setoid for a point representative. -/
scoped instance instSetoidPoint : Setoid <| Fin 3 → R :=
  MulAction.orbitRel Rˣ <| Fin 3 → R

/-- The equivalence class of a point representative. -/
abbrev PointClass (R : Type u) [CommRing R] : Type u :=
  MulAction.orbitRel.Quotient Rˣ <| Fin 3 → R

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

lemma eval_polynomial (P : Fin 3 → R) : eval P W.polynomial =
    P y ^ 2 * P z + W.a₁ * P x * P y * P z + W.a₃ * P y * P z ^ 2
      - (P x ^ 3 + W.a₂ * P x ^ 2 * P z + W.a₄ * P x * P z ^ 2 + W.a₆ * P z ^ 3) := by
  rw [polynomial]
  eval_simp

/-- The proposition that a point representative $(x, y, z)$ lies in `W`.
In other words, $W(x, y, z) = 0$. -/
@[pp_dot]
def Equation (P : Fin 3 → R) : Prop :=
  eval P W.polynomial = 0

lemma equation_iff (P : Fin 3 → R) : W.Equation P ↔
    P y ^ 2 * P z + W.a₁ * P x * P y * P z + W.a₃ * P y * P z ^ 2
      = P x ^ 3 + W.a₂ * P x ^ 2 * P z + W.a₄ * P x * P z ^ 2 + W.a₆ * P z ^ 3 := by
  rw [Equation, eval_polynomial, sub_eq_zero]

lemma equation_zero (Y : R) : W.Equation ![0, Y, 0] :=
  (W.equation_iff ![0, Y, 0]).mpr <| by matrix_simp; ring1

lemma equation_some (X Y : R) : W.Equation ![X, Y, 1] ↔ W.toAffine.equation X Y := by
  rw [equation_iff, W.toAffine.equation_iff]
  congr! 1 <;> matrix_simp <;> ring1

lemma equation_smul_iff (P : Fin 3 → R) (u : Rˣ) : W.Equation (u • P) ↔ W.Equation P :=
  have (u : Rˣ) {P : Fin 3 → R} (h : W.Equation P) : W.Equation <| u • P := by
    rw [equation_iff] at h ⊢
    linear_combination (norm := (simp only [smul_fin3_ext]; ring1)) (u : R) ^ 3 * h
  ⟨fun h => by convert this u⁻¹ h; rw [inv_smul_smul], this u⟩

/-- The partial derivative $W_X(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $X$. -/
@[pp_dot]
noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  pderiv x W.polynomial

lemma polynomialX_eq : W.polynomialX =
    C W.a₁ * X 1 * X 2 - (C 3 * X 0 ^ 2 + C (2 * W.a₂) * X 0 * X 2 + C W.a₄ * X 2 ^ 2) := by
  rw [polynomialX, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialX (P : Fin 3 → R) : eval P W.polynomialX =
    W.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W.a₂ * P x * P z + W.a₄ * P z ^ 2) := by
  rw [polynomialX_eq]
  eval_simp

/-- The partial derivative $W_Y(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $Y$. -/
@[pp_dot]
noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  pderiv y W.polynomial

lemma polynomialY_eq : W.polynomialY =
    C 2 * X 1 * X 2 + C W.a₁ * X 0 * X 2 + C W.a₃ * X 2 ^ 2 := by
  rw [polynomialY, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialY (P : Fin 3 → R) :
    eval P W.polynomialY = 2 * P y * P z + W.a₁ * P x * P z + W.a₃ * P z ^ 2 := by
  rw [polynomialY_eq]
  eval_simp

/-- The partial derivative $W_Z(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $Z$. -/
@[pp_dot]
noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  pderiv z W.polynomial

lemma polynomialZ_eq : W.polynomialZ =
    X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C (2 * W.a₃) * X 1 * X 2
      - (C W.a₂ * X 0 ^ 2 + C (2 * W.a₄) * X 0 * X 2 + C (3 * W.a₆) * X 2 ^ 2) := by
  rw [polynomialZ, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialZ (P : Fin 3 → R) : eval P W.polynomialZ =
    P y ^ 2 + W.a₁ * P x * P y + 2 * W.a₃ * P y * P z
      - (W.a₂ * P x ^ 2 + 2 * W.a₄ * P x * P z + 3 * W.a₆ * P z ^ 2) := by
  rw [polynomialZ_eq]
  eval_simp

/-- Euler's homogeneous function theorem. -/
theorem polynomial_relation (P : Fin 3 → R) : 3 * eval P W.polynomial =
    P x * eval P W.polynomialX + P y * eval P W.polynomialY + P z * eval P W.polynomialZ := by
  rw [eval_polynomial, eval_polynomialX, eval_polynomialY, eval_polynomialZ]
  ring1

/-- The proposition that a point representative $(x, y, z)$ in `W` is nonsingular.
In other words, either $W_X(x, y, z) \ne 0$, $W_Y(x, y, z) \ne 0$, or $W_Z(x, y, z) \ne 0$. -/
@[pp_dot]
def Nonsingular (P : Fin 3 → R) : Prop :=
  W.Equation P ∧ (eval P W.polynomialX ≠ 0 ∨ eval P W.polynomialY ≠ 0 ∨ eval P W.polynomialZ ≠ 0)

lemma nonsingular_iff (P : Fin 3 → R) : W.Nonsingular P ↔ W.Equation P ∧
    (W.a₁ * P y * P z ≠ 3 * P x ^ 2 + 2 * W.a₂ * P x * P z + W.a₄ * P z ^ 2 ∨
      P y * P z ≠ -P y * P z - W.a₁ * P x * P z - W.a₃ * P z ^ 2 ∨
      P y ^ 2 + W.a₁ * P x * P y + 2 * W.a₃ * P y * P z
        ≠ W.a₂ * P x ^ 2 + 2 * W.a₄ * P x * P z + 3 * W.a₆ * P z ^ 2) := by
  rw [Nonsingular, eval_polynomialX, eval_polynomialY, eval_polynomialZ, sub_ne_zero, sub_ne_zero,
    ← sub_ne_zero (a := P y * P z)]
  congr! 4
  ring1

lemma nonsingular_zero [Nontrivial R] : W.Nonsingular ![0, 1, 0] :=
  (W.nonsingular_iff ![0, 1, 0]).mpr ⟨W.equation_zero 1, by simp⟩

lemma nonsingular_zero' [NoZeroDivisors R] {Y : R} (hy : Y ≠ 0) : W.Nonsingular ![0, Y, 0] :=
  (W.nonsingular_iff ![0, Y, 0]).mpr ⟨W.equation_zero Y, by simpa⟩

lemma nonsingular_some (X Y : R) : W.Nonsingular ![X, Y, 1] ↔ W.toAffine.nonsingular X Y := by
  simp only [nonsingular_iff, fin3_def_ext, W.toAffine.nonsingular_iff, equation_some,
    and_congr_right_iff, W.toAffine.equation_iff, ← not_and_or, not_iff_not, one_pow, mul_one,
    Iff.comm, iff_self_and]
  intro h hX hY
  linear_combination (norm := ring1) 3 * h - X * hX - Y * hY

lemma nonsingular_smul_iff (P : Fin 3 → R) (u : Rˣ) : W.Nonsingular (u • P) ↔ W.Nonsingular P :=
  have (u : Rˣ) {P : Fin 3 → R} (h : W.Nonsingular <| u • P) : W.Nonsingular P := by
    rcases (W.nonsingular_iff _).mp h with ⟨h, h'⟩
    refine (W.nonsingular_iff P).mpr ⟨(W.equation_smul_iff P u).mp h, ?_⟩
    contrapose! h'
    simp only [smul_fin3_ext]
    exact ⟨by linear_combination (norm := ring1) (u : R) ^ 2 * h'.left,
      by linear_combination (norm := ring1) (u : R) ^ 2 * h'.right.left,
      by linear_combination (norm := ring1) (u : R) ^ 2 * h'.right.right⟩
  ⟨this u, fun h => this u⁻¹ <| by rwa [inv_smul_smul]⟩

lemma nonsingular_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W.Nonsingular P ↔ W.Nonsingular Q := by
  rcases h with ⟨u, rfl⟩
  exact W.nonsingular_smul_iff Q u

/-- The proposition that a point class on `W` is nonsingular. If `P` is a point representative,
then `W.NonsingularLift ⟦P⟧` is definitionally equivalent to `W.Nonsingular P`. -/
@[pp_dot]
def NonsingularLift (P : PointClass R) : Prop :=
  P.lift W.Nonsingular fun _ _ => propext ∘ W.nonsingular_of_equiv

@[simp]
lemma nonsingularLift_iff (P : Fin 3 → R) : W.NonsingularLift ⟦P⟧ ↔ W.Nonsingular P :=
  Iff.rfl

lemma nonsingularLift_zero [Nontrivial R] : W.NonsingularLift ⟦![0, 1, 0]⟧ :=
  W.nonsingular_zero

lemma nonsingularLift_zero' [NoZeroDivisors R] {Y : R} (hy : Y ≠ 0) :
    W.NonsingularLift ⟦![0, Y, 0]⟧ :=
  W.nonsingular_zero' hy

lemma nonsingularLift_some (X Y : R) :
    W.NonsingularLift ⟦![X, Y, 1]⟧ ↔ W.toAffine.nonsingular X Y :=
  W.nonsingular_some X Y

variable {F : Type u} [Field F] {W : Projective F}

lemma equiv_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : P ≈ Q := by
  rw [← fin3_def P, hPz] at hP ⊢
  rw [← fin3_def Q, hQz] at hQ ⊢
  simp only [nonsingular_iff, equation_iff, fin3_def_ext, zero_pow two_ne_zero,
    zero_pow three_ne_zero, mul_zero, add_zero, sub_zero, @eq_comm F 0,
    pow_eq_zero_iff three_ne_zero] at hP hQ
  simp only [hP, hQ, true_and, zero_pow two_ne_zero, mul_zero, ne_self_iff_false, false_or,
    zero_mul, add_zero, pow_ne_zero_iff two_ne_zero] at hP hQ ⊢
  exact ⟨Units.mk0 (P y / Q y) <| div_ne_zero hP hQ, by simp [div_mul_cancel₀ _ hQ]⟩

lemma equiv_zero_of_Z_eq_zero {P : Fin 3 → F} (h : W.Nonsingular P) (hPz : P z = 0) :
    P ≈ ![0, 1, 0] :=
  equiv_of_Z_eq_zero h W.nonsingular_zero hPz rfl

lemma equiv_some_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) : P ≈ ![P x / P z, P y / P z, 1] :=
  ⟨Units.mk0 _ hPz, by simp [fin3_def P, mul_div_cancel₀ _ hPz]⟩

lemma nonsingular_iff_affine_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.toAffine.nonsingular (P x / P z) (P y / P z) :=
  (W.nonsingular_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| W.nonsingular_some ..

lemma nonsingular_of_affine_of_Z_ne_zero {P : Fin 3 → F}
    (h : W.toAffine.nonsingular (P x / P z) (P y / P z)) (hPz : P z ≠ 0) : W.Nonsingular P :=
  (nonsingular_iff_affine_of_Z_ne_zero hPz).mpr h

lemma nonsingular_affine_of_Z_ne_zero {P : Fin 3 → F} (h : W.Nonsingular P) (hPz : P z ≠ 0) :
    W.toAffine.nonsingular (P x / P z) (P y / P z) :=
  (nonsingular_iff_affine_of_Z_ne_zero hPz).mp h

end Equation

section Polynomial

/-! ### Group operation polynomials -/

/-- The $Y$-coordinate of the negation of a point representative. -/
@[pp_dot]
def negY (P : Fin 3 → R) : R :=
  -P y - W.a₁ * P x - W.a₃ * P z

lemma negY_smul (P : Fin 3 → R) (u : Rˣ) : W.negY (u • P) = u * W.negY P := by
  simp only [negY, smul_fin3_ext]
  ring1

/-- The truncated $X$-coordinate of the addition of two point representatives, where their
$Z$-coordinates are non-zero and their $X$-coordinates divided by $Z$-coordinates are distinct.
This is only an auxiliary definition needed to define `WeierstrassCurve.Projective.addY'_of_X_ne`,
and the full $X$-coordinate is defined in `WeierstrassCurve.Projective.addX_of_X_ne`. -/
@[pp_dot]
def addX'_of_X_ne (P Q : Fin 3 → R) : R :=
  (P y * Q z - P z * Q y) ^ 2 * P z * Q z
    + W.a₁ * (P y * Q z - P z * Q y) * P z * Q z * (P x * Q z - P z * Q x)
    - W.a₂ * P z * Q z * (P x * Q z - P z * Q x) ^ 2 - P x * Q z * (P x * Q z - P z * Q x) ^ 2
    - Q x * P z * (P x * Q z - P z * Q x) ^ 2

lemma addX'_of_X_ne_smul (P Q : Fin 3 → R) (u v : Rˣ) :
    W.addX'_of_X_ne (u • P) (v • Q) = (u : R) ^ 3 * (v : R) ^ 3 * W.addX'_of_X_ne P Q := by
  simp only [addX'_of_X_ne, smul_fin3_ext]
  ring1

/-- The truncated $X$-coordinate of the doubling of a point representative, where its
$Z$-coordinate is non-zero and its $Y$-coordinate is distinct from that of its negation.
This is only an auxiliary definition needed to define `WeierstrassCurve.Projective.addY'_of_Y_ne`,
and the full $X$-coordinate is defined in `WeierstrassCurve.Projective.addX_of_Y_ne`. -/
@[pp_dot]
def addX'_of_Y_ne (P : Fin 3 → R) : R :=
  (3 * P x ^ 2 + 2 * W.a₂ * P x * P z + W.a₄ * P z ^ 2 - W.a₁ * P y * P z) ^ 2
    + W.a₁ * (3 * P x ^ 2 + 2 * W.a₂ * P x * P z + W.a₄ * P z ^ 2 - W.a₁ * P y * P z) * P z
      * (P y - W.negY P)
    - W.a₂ * P z ^ 2 * (P y - W.negY P) ^ 2 - 2 * P x * P z * (P y - W.negY P) ^ 2

lemma addX'_of_Y_ne_smul (P : Fin 3 → R) (u : Rˣ) :
    W.addX'_of_Y_ne (u • P) = (u : R) ^ 4 * W.addX'_of_Y_ne P := by
  simp only [addX'_of_Y_ne, negY_smul, smul_fin3_ext]
  ring1

/-- The $Y$-coordinate of the addition of two point representatives, before applying the final
negation that maps $Y$ to $-Y - a_1X - a_3Z$, where their $Z$-coordinates are non-zero and their
$X$-coordinates divided by $Z$-coordinates are distinct. -/
@[pp_dot]
def addY'_of_X_ne (P Q : Fin 3 → R) : R :=
  (P y * Q z - P z * Q y) * (W.addX'_of_X_ne P Q - P x * Q z * (P x * Q z - P z * Q x) ^ 2)
    + P y * Q z * (P x * Q z - P z * Q x) ^ 2 * (P x * Q z - P z * Q x)

lemma addY'_of_X_ne_smul (P Q : Fin 3 → R) (u v : Rˣ) :
    W.addY'_of_X_ne (u • P) (v • Q) = (u : R) ^ 4 * (v : R) ^ 4 * W.addY'_of_X_ne P Q := by
  simp only [addY'_of_X_ne, addX'_of_X_ne_smul, smul_fin3_ext]
  ring1

/-- The $Y$-coordinate of the doubling of a point representative, before applying the final negation
that maps $Y$ to $-Y - a_1X - a_3Z$, where its $Z$-coordinate is non-zero and its $Y$-coordinate is
distinct from that of its negation. -/
@[pp_dot]
def addY'_of_Y_ne (P : Fin 3 → R) : R :=
  (3 * P x ^ 2 + 2 * W.a₂ * P x * P z + W.a₄ * P z ^ 2 - W.a₁ * P y * P z)
    * (W.addX'_of_Y_ne P - P x * P z * (P y - W.negY P) ^ 2)
    + P y * P z ^ 2 * (P y - W.negY P) ^ 2 * (P y - W.negY P)

lemma addY'_of_Y_ne_smul (P : Fin 3 → R) (u : Rˣ) :
    W.addY'_of_Y_ne (u • P) = (u : R) ^ 6 * W.addY'_of_Y_ne P := by
  simp only [addY'_of_Y_ne, addX'_of_Y_ne_smul, negY_smul, smul_fin3_ext]
  ring1

/-- The $Z$-coordinate of the addition of two point representatives, where their $Z$-coordinates are
non-zero and their $X$-coordinates divided by $Z$-coordinates are distinct. -/
def addZ_of_X_ne (P Q : Fin 3 → R) : R :=
  P z * Q z * (P x * Q z - P z * Q x) ^ 2 * (P x * Q z - P z * Q x)

lemma addZ_of_X_ne_smul (P Q : Fin 3 → R) (u v : Rˣ) :
    addZ_of_X_ne (u • P) (v • Q) = (u : R) ^ 4 * (v : R) ^ 4 * addZ_of_X_ne P Q := by
  simp only [addZ_of_X_ne, smul_fin3_ext]
  ring1

/-- The $Z$-coordinate of the doubling of a point representative, where its $Z$-coordinate is
non-zero and its $Y$-coordinate is distinct from that of its negation. -/
@[pp_dot]
def addZ_of_Y_ne (P : Fin 3 → R) : R :=
  P z ^ 2 * (P y - W.negY P) ^ 2 * (P z * (P y - W.negY P))

lemma addZ_of_Y_ne_smul (P : Fin 3 → R) (u : Rˣ) :
    W.addZ_of_Y_ne (u • P) = (u : R) ^ 6 * W.addZ_of_Y_ne P := by
  simp only [addZ_of_Y_ne, negY_smul, smul_fin3_ext]
  ring1

/-- The $X$-coordinate of the addition of two point representatives, where their $Z$-coordinates are
non-zero and their $X$-coordinates divided by $Z$-coordinates are distinct. -/
@[pp_dot]
def addX_of_X_ne (P Q : Fin 3 → R) : R :=
  W.addX'_of_X_ne P Q * (P x * Q z - P z * Q x)

lemma addX_of_X_ne_smul (P Q : Fin 3 → R) (u v : Rˣ) :
    W.addX_of_X_ne (u • P) (v • Q) = (u : R) ^ 4 * (v : R) ^ 4 * W.addX_of_X_ne P Q := by
  simp only [addX_of_X_ne, addX'_of_X_ne_smul, smul_fin3_ext]
  ring1

/-- The $X$-coordinate of the doubling of a point representative, where its $Z$-coordinate is
non-zero and its $Y$-coordinate is distinct from that of its negation. -/
@[pp_dot]
def addX_of_Y_ne (P : Fin 3 → R) : R :=
  W.addX'_of_Y_ne P * (P z * (P y - W.negY P))

lemma addX_of_Y_ne_smul (P : Fin 3 → R) (u : Rˣ) :
    W.addX_of_Y_ne (u • P) = (u : R) ^ 6 * W.addX_of_Y_ne P := by
  simp only [addX_of_Y_ne, addX'_of_Y_ne_smul, negY_smul, smul_fin3_ext]
  ring1

/-- The $Y$-coordinate of the addition of two point representatives, where their $Z$-coordinates are
non-zero and their $X$-coordinates divided by $Z$-coordinates are distinct. -/
@[pp_dot]
def addY_of_X_ne (P Q : Fin 3 → R) : R :=
  W.negY ![W.addX_of_X_ne P Q, W.addY'_of_X_ne P Q, addZ_of_X_ne P Q]

lemma addY_of_X_ne_smul (P Q : Fin 3 → R) (u v : Rˣ) :
    W.addY_of_X_ne (u • P) (v • Q) = (u : R) ^ 4 * (v : R) ^ 4 * W.addY_of_X_ne P Q := by
  simp only [addY_of_X_ne, negY, addX_of_X_ne_smul, addY'_of_X_ne_smul, addZ_of_X_ne_smul]
  matrix_simp
  ring1

/-- The $Y$-coordinate of the doubling of a point representative, where its $Z$-coordinate is
non-zero and its $Y$-coordinate is distinct from that of its negation. -/
@[pp_dot]
def addY_of_Y_ne (P : Fin 3 → R) : R :=
  W.negY ![W.addX_of_Y_ne P, W.addY'_of_Y_ne P, W.addZ_of_Y_ne P]

lemma addY_of_Y_ne_smul (P : Fin 3 → R) (u : Rˣ) :
    W.addY_of_Y_ne (u • P) = (u : R) ^ 6 * W.addY_of_Y_ne P := by
  simp only [addY_of_Y_ne, negY, addX_of_Y_ne_smul, addY'_of_Y_ne_smul, addZ_of_Y_ne_smul]
  matrix_simp
  ring1

variable {F : Type u} [Field F] {W : Projective F}

lemma negY_divZ {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.negY P / P z = W.toAffine.negY (P x / P z) (P y / P z) := by
  field_simp [negY]
  ring1

lemma Y_ne_of_Y_ne {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = P z * Q x) (hy : P y * Q z ≠ P z * W.negY Q) :
    P y ≠ W.negY P := by
  simp only [mul_comm <| P z, ne_eq, ← div_eq_div_iff hPz hQz] at hx hy
  have hy' : P y / P z = Q y / Q z :=
    Affine.Yeq_of_Yne (nonsingular_affine_of_Z_ne_zero hP hPz).left
      (nonsingular_affine_of_Z_ne_zero hQ hQz).left hx <| (negY_divZ hQz).symm ▸ hy
  simp_rw [negY, sub_div, neg_div, mul_div_assoc, ← hy', ← hx, div_self hQz, ← div_self hPz,
    ← mul_div_assoc, ← neg_div, ← sub_div, div_left_inj' hPz] at hy
  exact hy

private lemma addX_eq {P Q : Fin 3 → F} {n d : F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hd : d ≠ 0) :
    W.toAffine.addX (P x / P z) (Q x / Q z) (n / d) =
      (n ^ 2 * P z * Q z + W.a₁ * n * P z * Q z * d - W.a₂ * P z * Q z * d ^ 2 - P x * Q z * d ^ 2
        - Q x * P z * d ^ 2) / (P z * Q z * d ^ 2) := by
  field_simp [pow_ne_zero 2 hd]
  ring1

private lemma addX_eq' {P : Fin 3 → F} {n d : F} (hPz : P z ≠ 0) (hd : d ≠ 0) :
    W.toAffine.addX (P x / P z) (P x / P z) (n / (P z * d)) =
      (n ^ 2 + W.a₁ * n * P z * d - W.a₂ * P z ^ 2 * d ^ 2 - 2 * P x * P z * d ^ 2)
        / (P z ^ 2 * d ^ 2) := by
  field_simp [mul_ne_zero hPz hd]
  ring1

private lemma slope_eq {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ≠ P z * Q x) :
    W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z) =
      (P y * Q z - P z * Q y) / (P x * Q z - P z * Q x) := by
  rw [Affine.slope_of_Xne <| by rwa [ne_eq, div_eq_div_iff hPz hQz, mul_comm <| Q x]]
  field_simp

private lemma slope_eq' {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = P z * Q x) (hy : P y * Q z ≠ P z * W.negY Q) :
    W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z) =
      (3 * P x ^ 2 + 2 * W.a₂ * P x * P z + W.a₄ * P z ^ 2 - W.a₁ * P y * P z)
        / (P z * (P y - W.negY P)) := by
  have hPy : P y - W.negY P ≠ 0 := sub_ne_zero_of_ne <| Y_ne_of_Y_ne hP hQ hPz hQz hx hy
  simp only [mul_comm <| P z, ne_eq, ← div_eq_div_iff hPz hQz] at hx hy
  rw [Affine.slope_of_Yne hx <| (negY_divZ hQz).symm ▸ hy, ← negY_divZ hPz]
  field_simp [pow_ne_zero 2 hPz]
  ring1

lemma addX_div_addZ_of_X_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ≠ P z * Q x) : W.addX_of_X_ne P Q / addZ_of_X_ne P Q =
      W.toAffine.addX (P x / P z) (Q x / Q z)
        (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [addX_of_X_ne, addX'_of_X_ne, addZ_of_X_ne, mul_div_mul_right _ _ <| sub_ne_zero_of_ne hx,
    slope_eq hPz hQz hx, addX_eq hPz hQz <| sub_ne_zero_of_ne hx]

lemma addX_div_addZ_of_Y_ne {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = P z * Q x) (hy : P y * Q z ≠ P z * W.negY Q) :
    W.addX_of_Y_ne P / W.addZ_of_Y_ne P = W.toAffine.addX (P x / P z) (Q x / Q z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  have hPy : P y - W.negY P ≠ 0 := sub_ne_zero_of_ne <| Y_ne_of_Y_ne hP hQ hPz hQz hx hy
  rw [addX_of_Y_ne, addX'_of_Y_ne, addZ_of_Y_ne, mul_div_mul_right _ _ <| mul_ne_zero hPz hPy,
    slope_eq' hP hQ hPz hQz hx hy, ← (div_eq_div_iff hPz hQz).mpr <| mul_comm (P z) _ ▸ hx,
    addX_eq' hPz hPy]

lemma addY'_div_addZ_of_X_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ≠ P z * Q x) : W.addY'_of_X_ne P Q / addZ_of_X_ne P Q =
      W.toAffine.addY' (P x / P z) (Q x / Q z) (P y / P z)
        (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [Affine.addY', ← addX_div_addZ_of_X_ne hPz hQz hx, slope_eq hPz hQz hx, addY'_of_X_ne,
    addX_of_X_ne, addZ_of_X_ne, add_div]
  nth_rw 1 [mul_comm <| _ * _ * _, mul_div_mul_comm, sub_div _ <| _ * _ * _]
  simp only [mul_div_mul_right _ _ hQz, mul_div_mul_right _ _ <| sub_ne_zero_of_ne hx,
    mul_div_mul_right _ _ <| pow_ne_zero 2 <| sub_ne_zero_of_ne hx]

lemma addY'_div_addZ_of_Y_ne {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = P z * Q x) (hy : P y * Q z ≠ P z * W.negY Q) :
    W.addY'_of_Y_ne P / W.addZ_of_Y_ne P = W.toAffine.addY' (P x / P z) (Q x / Q z) (P y / P z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  have hPy : P y - W.negY P ≠ 0 := sub_ne_zero_of_ne <| Y_ne_of_Y_ne hP hQ hPz hQz hx hy
  rw [Affine.addY', ← addX_div_addZ_of_Y_ne hP hQ hPz hQz hx hy, slope_eq' hP hQ hPz hQz hx hy,
    addY'_of_Y_ne, addX_of_Y_ne, addZ_of_Y_ne, add_div]
  nth_rw 1 [mul_comm <| _ ^ 2 * _]
  rw [mul_div_mul_comm, sub_div _ <| _ * _ ^ 2, mul_div_mul_right _ _ <| mul_ne_zero hPz hPy]
  simp only [sq, ← mul_assoc, mul_comm (_ * _ * _) <| P z, mul_div_mul_right _ _ hPy,
    mul_div_mul_right _ _ hPz, mul_div_mul_right _ _ <| pow_ne_zero 2 hPy]

lemma addZ_ne_zero_of_X_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ≠ P z * Q x) : addZ_of_X_ne P Q ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) <| pow_ne_zero 2 ?_) ?_
  any_goals exact hPz
  any_goals exact hQz
  any_goals exact sub_ne_zero_of_ne hx

lemma addZ_ne_zero_of_Y_ne {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = P z * Q x) (hy : P y * Q z ≠ P z * W.negY Q) :
    W.addZ_of_Y_ne P ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ?_) <| pow_ne_zero 2 ?_) <| mul_ne_zero ?_ ?_
  any_goals exact hPz
  any_goals exact sub_ne_zero_of_ne <| Y_ne_of_Y_ne hP hQ hPz hQz hx hy

lemma addY_div_addZ_of_X_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ≠ P z * Q x) : W.addY_of_X_ne P Q / addZ_of_X_ne P Q =
      W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
        (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [Affine.addY, ← addX_div_addZ_of_X_ne hPz hQz hx, ← addY'_div_addZ_of_X_ne hPz hQz hx]
  exact negY_divZ <| addZ_ne_zero_of_X_ne hPz hQz hx

lemma addY_div_addZ_of_Y_ne {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = P z * Q x) (hy : P y * Q z ≠ P z * W.negY Q) :
    W.addY_of_Y_ne P / W.addZ_of_Y_ne P = W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [Affine.addY, ← addX_div_addZ_of_Y_ne hP hQ hPz hQz hx hy,
    ← addY'_div_addZ_of_Y_ne hP hQ hPz hQz hx hy]
  exact negY_divZ <| addZ_ne_zero_of_Y_ne hP hQ hPz hQz hx hy

end Polynomial

end WeierstrassCurve.Projective
