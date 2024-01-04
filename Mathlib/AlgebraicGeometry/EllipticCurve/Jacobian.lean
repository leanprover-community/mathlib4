/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.Data.MvPolynomial.CommRing

/-!
# Jacobian coordinates for Weierstrass curves

This file defines the type of points on a Weierstrass curve as a tuple, consisting of an equivalence
class of triples up to scaling by weights, satisfying a Weierstrass equation with a nonsingular
condition. This file also defines the negation and addition operations of the group law for this
type, and proves that they respect the Weierstrass equation and the nonsingular condition. The fact
that they form an abelian group is proven in `Mathlib.AlgebraicGeometry.EllipticCurve.Group`.

## Mathematical background

Let `W` be a Weierstrass curve over a field `F`. A point on the weighted projective plane with
weights $(2, 3, 1)$ is an equivalence class of triples $[x:y:z]$ with coordinates in `F` such that
$(x, y, z) \sim (x', y', z')$ precisely if there is some unit $u$ of `F` such that
$(x, y, z) = (u^2x', u^3y', uz')$, with an extra condition that $(x, y, z) \ne (0, 0, 0)$.
A rational point is a point on the $(2, 3, 1)$-projective plane satisfying a $(2, 3, 1)$-homogeneous
Weierstrass equation $Y^2 + a_1XYZ + a_3YZ^3 = X^3 + a_2X^2Z^2 + a_4XZ^4 + a_6Z^6$, and being
nonsingular means the partial derivatives $W_X(X, Y, Z)$, $W_Y(X, Y, Z)$, and $W_Z(X, Y, Z)$ do not
vanish simultaneously. Note that the vanishing of the Weierstrass equation and its partial
derivatives are independent of the representative for $[x:y:z]$, and the nonsingularity condition
already implies that $(x, y, z) \ne (0, 0, 0)$, so a nonsingular rational point on `W` can simply be
given by a tuple consisting of $[x:y:z]$ and the nonsingular condition on any representative.
In cryptography, as well as in this file, this is often called the Jacobian coordinates of `W`.

As in `Mathlib.AlgebraicGeometry.EllipticCurve.Affine`, the set of nonsingular rational points forms
an abelian group under the same secant-and-tangent process, but the polynomials involved are
$(2, 3, 1)$-homogeneous, and any instances of division become multiplication in the $Z$-coordinate.
Note that most computational proofs follow from their analogous proofs for affine coordinates.

## Main definitions

 * `WeierstrassCurve.Jacobian.PointClass`: the equivalence class of a point representative.
 * `WeierstrassCurve.Jacobian.toAffine`: the Weierstrass curve in affine coordinates.
 * `WeierstrassCurve.Jacobian.nonsingular`: the nonsingular condition on a point representative.
 * `WeierstrassCurve.Jacobian.nonsingular_lift`: the nonsingular condition on a point class.
 * `WeierstrassCurve.Jacobian.neg`: the negation operation on a point representative.
 * `WeierstrassCurve.Jacobian.neg_map`: the negation operation on a point class.
 * `WeierstrassCurve.Jacobian.add`: the addition operation on a point representative.
 * `WeierstrassCurve.Jacobian.add_map`: the addition operation on a point class.
 * `WeierstrassCurve.Jacobian.Point`: a nonsingular rational point.
 * `WeierstrassCurve.Jacobian.Point.neg`: the negation operation on a nonsingular rational point.
 * `WeierstrassCurve.Jacobian.Point.add`: the addition operation on a nonsingular rational point.
 * `WeierstrassCurve.Jacobian.Point.toAffine_addEquiv`: the equivalence between the nonsingular
    rational points on a Jacobian Weierstrass curve with those on an affine Weierstrass curve.

## Main statements

 * `WeierstrassCurve.Jacobian.nonsingular_neg`: negation preserves the nonsingular condition.
 * `WeierstrassCurve.Jacobian.nonsingular_add`: addition preserves the nonsingular condition.

## Implementation notes

A point representative is implemented as a term `P` of type `Fin 3 → R`, which allows for the vector
notation `![x, y, z]`. However, `P` is not definitionally equivalent to the expanded vector
`![P x, P y, P z]`, so the auxiliary lemma `fin3_def` can be used to convert between the two forms.
The equivalence of two point representatives `P` and `Q` is implemented as an equivalence of orbits
of the action of `Rˣ`, or equivalently that there is some unit `u` of `R` such that `P = u • Q`.
However, `u • Q` is again not definitionally equal to `![u² * Q x, u³ * Q y, u * Q z]`, so the
auxiliary lemmas `smul_fin3` and `smul_fin3_ext` can be used to convert between the two forms.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, Jacobian coordinates
-/

local notation "x" => 0

local notation "y" => 1

local notation "z" => 2

local macro "matrix_simp" : tactic =>
  `(tactic| simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])

universe u

lemma fin3_def {R : Type u} (P : Fin 3 → R) : P = ![P x, P y, P z] := by
  ext n; fin_cases n <;> rfl

private instance {R : Type u} [CommRing R] : SMul Rˣ <| Fin 3 → R :=
  ⟨fun u P => ![u ^ 2 * P x, u ^ 3 * P y, u * P z]⟩

lemma smul_fin3 {R : Type u} [CommRing R] (P : Fin 3 → R) (u : Rˣ) :
    u • P = ![u ^ 2 * P x, u ^ 3 * P y, u * P z] :=
  rfl

lemma smul_fin3_ext {R : Type u} [CommRing R] (P : Fin 3 → R) (u : Rˣ) :
    (u • P) 0 = u ^ 2 * P x ∧ (u • P) 1 = u ^ 3 * P y ∧ (u • P) 2 = u * P z :=
  ⟨rfl, rfl, rfl⟩

private instance {R : Type u} [CommRing R] : MulAction Rˣ <| Fin 3 → R where
  one_smul := fun _ => by
    simp only [smul_fin3, Units.val_one, one_pow, one_mul, ← fin3_def]
  mul_smul := fun u v P => by
    simp only [smul_fin3, Units.val_mul, mul_pow, mul_assoc]
    matrix_simp

/-! ## Weierstrass curves -/

/-- An abbreviation for a Weierstrass curve in Jacobian coordinates. -/
abbrev WeierstrassCurve.Jacobian :=
  WeierstrassCurve

namespace WeierstrassCurve.Jacobian

open MvPolynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow])

variable (R : Type u) [CommRing R]

/-- The equivalence setoid for a point representative. -/
def PointSetoid : Setoid <| Fin 3 → R :=
  MulAction.orbitRel Rˣ <| Fin 3 → R

attribute [local instance] PointSetoid

/-- The equivalence class of a point representative. -/
abbrev PointClass : Type u :=
  MulAction.orbitRel.Quotient Rˣ <| Fin 3 → R

variable {R} (W : Jacobian R)

/-- The coercion to a Weierstrass curve in affine coordinates. -/
@[pp_dot]
abbrev toAffine : Affine R :=
  W

section Equation

/-! ### Equations and nonsingularity -/

/-- The polynomial $W(X, Y, Z) := Y^2 + a_1XYZ + a_3YZ^3 - (X^3 + a_2X^2Z^2 + a_4XZ^4 + a_6Z^6)$
associated to a Weierstrass curve `W` over `R`. This is represented as a term of type
`MvPolynomial (Fin 3) R`, where `X 0`, `X 1`, and `X 2` represent $X$, $Y$, and $Z$ respectively. -/
@[pp_dot]
noncomputable def polynomial : MvPolynomial (Fin 3) R :=
  X 1 ^ 2 + C W.a₁ * X 0 * X 1 * X 2 + C W.a₃ * X 1 * X 2 ^ 3
    - (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 * X 2 ^ 2 + C W.a₄ * X 0 * X 2 ^ 4 + C W.a₆ * X 2 ^ 6)

lemma eval_polynomial (P : Fin 3 → R) : eval P W.polynomial =
    P y ^ 2 + W.a₁ * P x * P y * P z + W.a₃ * P y * P z ^ 3
      - (P x ^ 3 + W.a₂ * P x ^ 2 * P z ^ 2 + W.a₄ * P x * P z ^ 4 + W.a₆ * P z ^ 6) := by
  rw [polynomial]
  eval_simp

/-- The proposition that a point representative $(x, y, z)$ lies in `W`.
In other words, $W(x, y, z) = 0$. -/
@[pp_dot]
def equation (P : Fin 3 → R) : Prop :=
  eval P W.polynomial = 0

lemma equation_iff (P : Fin 3 → R) : W.equation P ↔
    P y ^ 2 + W.a₁ * P x * P y * P z + W.a₃ * P y * P z ^ 3
      = P x ^ 3 + W.a₂ * P x ^ 2 * P z ^ 2 + W.a₄ * P x * P z ^ 4 + W.a₆ * P z ^ 6 := by
  rw [equation, eval_polynomial, sub_eq_zero]

lemma equation_zero : W.equation ![1, 1, 0] :=
  (W.equation_iff ![1, 1, 0]).mpr <| by matrix_simp; ring1

lemma equation_zero' (Y : R) : W.equation ![Y ^ 2, Y ^ 3, 0] :=
  (W.equation_iff ![Y ^ 2, Y ^ 3, 0]).mpr <| by matrix_simp; ring1

lemma equation_some (X Y : R) : W.equation ![X, Y, 1] ↔ W.toAffine.equation X Y := by
  rw [equation_iff, W.toAffine.equation_iff]
  congr! 1 <;> matrix_simp <;> ring1

lemma equation_smul_iff (P : Fin 3 → R) (u : Rˣ) : W.equation (u • P) ↔ W.equation P :=
  have (u : Rˣ) {P : Fin 3 → R} (h : W.equation P) : W.equation <| u • P := by
    rw [equation_iff] at h ⊢
    linear_combination (norm := (simp only [smul_fin3_ext]; ring1)) (u : R) ^ 6 * h
  ⟨fun h => by convert this u⁻¹ h; rw [inv_smul_smul], this u⟩

/-- The partial derivative $W_X(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $X$.

TODO: define this in terms of `MvPolynomial.pderiv`. -/
@[pp_dot]
noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  C W.a₁ * X 1 * X 2 - (C 3 * X 0 ^ 2 + C (2 * W.a₂) * X 0 * X 2 ^ 2 + C W.a₄ * X 2 ^ 4)

lemma eval_polynomialX (P : Fin 3 → R) : eval P W.polynomialX =
    W.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W.a₂ * P x * P z ^ 2 + W.a₄ * P z ^ 4) := by
  rw [polynomialX]
  eval_simp

/-- The partial derivative $W_Y(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $Y$.

TODO: define this in terms of `MvPolynomial.pderiv`. -/
@[pp_dot]
noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  C 2 * X 1 + C W.a₁ * X 0 * X 2 + C W.a₃ * X 2 ^ 3

lemma eval_polynomialY (P : Fin 3 → R) :
    eval P W.polynomialY = 2 * P y + W.a₁ * P x * P z + W.a₃ * P z ^ 3 := by
  rw [polynomialY]
  eval_simp

/-- The partial derivative $W_Z(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $Z$.

TODO: define this in terms of `MvPolynomial.pderiv`. -/
@[pp_dot]
noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  C W.a₁ * X 0 * X 1 + C (3 * W.a₃) * X 1 * X 2 ^ 2
    - (C (2 * W.a₂) * X 0 ^ 2 * X 2 + C (4 * W.a₄) * X 0 * X 2 ^ 3 + C (6 * W.a₆) * X 2 ^ 5)

lemma eval_polynomialZ (P : Fin 3 → R) : eval P W.polynomialZ =
    W.a₁ * P x * P y + 3 * W.a₃ * P y * P z ^ 2
      - (2 * W.a₂ * P x ^ 2 * P z + 4 * W.a₄ * P x * P z ^ 3 + 6 * W.a₆ * P z ^ 5) := by
  rw [polynomialZ]
  eval_simp

/-- The proposition that a point representative $(x, y, z)$ in `W` is nonsingular.
In other words, either $W_X(x, y, z) \ne 0$, $W_Y(x, y, z) \ne 0$, or $W_Z(x, y, z) \ne 0$. -/
@[pp_dot]
def nonsingular (P : Fin 3 → R) : Prop :=
  W.equation P ∧ (eval P W.polynomialX ≠ 0 ∨ eval P W.polynomialY ≠ 0 ∨ eval P W.polynomialZ ≠ 0)

lemma nonsingular_iff (P : Fin 3 → R) : W.nonsingular P ↔ W.equation P ∧
    (W.a₁ * P y * P z ≠ 3 * P x ^ 2 + 2 * W.a₂ * P x * P z ^ 2 + W.a₄ * P z ^ 4 ∨
      P y ≠ -P y - W.a₁ * P x * P z - W.a₃ * P z ^ 3 ∨
      W.a₁ * P x * P y + 3 * W.a₃ * P y * P z ^ 2
        ≠ 2 * W.a₂ * P x ^ 2 * P z + 4 * W.a₄ * P x * P z ^ 3 + 6 * W.a₆ * P z ^ 5) := by
  rw [nonsingular, eval_polynomialX, eval_polynomialY, eval_polynomialZ, sub_ne_zero, sub_ne_zero,
    ← sub_ne_zero (a := P y)]
  congr! 4
  ring1

lemma nonsingular_zero [Nontrivial R] : W.nonsingular ![1, 1, 0] :=
  (W.nonsingular_iff ![1, 1, 0]).mpr ⟨W.equation_zero,
    by simp; by_contra! h; exact one_ne_zero <| by linear_combination -h.1 - h.2.1⟩

lemma nonsingular_zero' [NoZeroDivisors R] {Y : R} (hy : Y ≠ 0) :
    W.nonsingular ![Y ^ 2, Y ^ 3, 0] :=
  (W.nonsingular_iff ![Y ^ 2, Y ^ 3, 0]).mpr ⟨W.equation_zero' Y,
    by simp [hy]; by_contra! h; exact pow_ne_zero 3 hy <| by linear_combination Y ^ 3 * h.1 - h.2.1⟩

lemma nonsingular_some (X Y : R) : W.nonsingular ![X, Y, 1] ↔ W.toAffine.nonsingular X Y := by
  rw [nonsingular_iff]
  matrix_simp
  simp only [W.toAffine.nonsingular_iff, equation_some, and_congr_right_iff,
    W.toAffine.equation_iff, ← not_and_or, not_iff_not, one_pow, mul_one, Iff.comm, iff_self_and]
  intro h hX hY
  linear_combination (norm := ring1) 6 * h - 2 * X * hX - 3 * Y * hY

lemma nonsingular_smul_iff (P : Fin 3 → R) (u : Rˣ) : W.nonsingular (u • P) ↔ W.nonsingular P :=
  have (u : Rˣ) {P : Fin 3 → R} (h : W.nonsingular <| u • P) : W.nonsingular P := by
    rcases (W.nonsingular_iff _).mp h with ⟨h, h'⟩
    refine (W.nonsingular_iff P).mpr ⟨(W.equation_smul_iff P u).mp h, ?_⟩
    contrapose! h'
    simp only [smul_fin3_ext]
    exact ⟨by linear_combination (norm := ring1) (u : R) ^ 4 * h'.left,
      by linear_combination (norm := ring1) (u : R) ^ 3 * h'.right.left,
      by linear_combination (norm := ring1) (u : R) ^ 5 * h'.right.right⟩
  ⟨this u, fun h => this u⁻¹ <| by rwa [inv_smul_smul]⟩

lemma nonsingular_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W.nonsingular P ↔ W.nonsingular Q := by
  rcases h with ⟨u, rfl⟩
  exact W.nonsingular_smul_iff Q u

/-- The proposition that a point class on `W` is nonsingular. If `P` is a point representative,
then `W.nonsingular_lift ⟦P⟧` is definitionally equivalent to `W.nonsingular P`. -/
@[pp_dot]
def nonsingular_lift (P : PointClass R) : Prop :=
  P.lift W.nonsingular fun _ _ => propext ∘ W.nonsingular_of_equiv

@[simp]
lemma nonsingular_lift_eq (P : Fin 3 → R) : W.nonsingular_lift ⟦P⟧ = W.nonsingular P :=
  rfl

lemma nonsingular_lift_zero [Nontrivial R] : W.nonsingular_lift ⟦![1, 1, 0]⟧ :=
  W.nonsingular_zero

lemma nonsingular_lift_zero' [NoZeroDivisors R] {Y : R} (hy : Y ≠ 0) :
    W.nonsingular_lift ⟦![Y ^ 2, Y ^ 3, 0]⟧ :=
  W.nonsingular_zero' hy

lemma nonsingular_lift_some (X Y : R) :
    W.nonsingular_lift ⟦![X, Y, 1]⟧ ↔ W.toAffine.nonsingular X Y :=
  W.nonsingular_some X Y

variable {F : Type u} [Field F] {W : Jacobian F}

lemma equiv_of_Zeq0 {P Q : Fin 3 → F} (hP : W.nonsingular P) (hQ : W.nonsingular Q) (hPz : P z = 0)
    (hQz : Q z = 0) : P ≈ Q := by
  rw [fin3_def P, hPz] at hP ⊢
  rw [fin3_def Q, hQz] at hQ ⊢
  simp [nonsingular_iff, equation_iff] at hP hQ
  have hPx : P x ≠ 0 := fun h => by simp [h] at hP; simp [hP] at hP
  have hQx : Q x ≠ 0 := fun h => by simp [h] at hQ; simp [hQ] at hQ
  have hPy : P y ≠ 0 := fun h => by simp [h] at hP; exact hPx <| pow_eq_zero hP.left.symm
  have hQy : Q y ≠ 0 := fun h => by simp [h] at hQ; exact hQx <| pow_eq_zero hQ.left.symm
  use Units.mk0 _ <| mul_ne_zero (div_ne_zero hPy hPx) (div_ne_zero hQx hQy)
  simp [smul_fin3, mul_pow, div_pow]
  congr! 2
  · field_simp [hP.left, hQ.left]
    ring1
  · field_simp [← hP.left, ← hQ.left]
    ring1

lemma equiv_zero_of_Zeq0 {P : Fin 3 → F} (h : W.nonsingular P) (hPz : P z = 0) : P ≈ ![1, 1, 0] :=
  equiv_of_Zeq0 h W.nonsingular_zero hPz rfl

lemma equiv_some_of_Zne0 {P : Fin 3 → F} (hPz : P z ≠ 0) : P ≈ ![P x / P z ^ 2, P y / P z ^ 3, 1] :=
  ⟨Units.mk0 _ hPz, by simp [smul_fin3, ← fin3_def P, mul_div_cancel' _ <| pow_ne_zero _ hPz]⟩

lemma nonsingular_iff_affine_of_Zne0 {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.nonsingular P ↔ W.toAffine.nonsingular (P x / P z ^ 2) (P y / P z ^ 3) :=
  (W.nonsingular_of_equiv <| equiv_some_of_Zne0 hPz).trans <| W.nonsingular_some ..

lemma nonsingular_of_affine_of_Zne0 {P : Fin 3 → F}
    (h : W.toAffine.nonsingular (P x / P z ^ 2) (P y / P z ^ 3)) (hPz : P z ≠ 0) :
    W.nonsingular P :=
  (nonsingular_iff_affine_of_Zne0 hPz).mpr h

lemma nonsingular_affine_of_Zne0 {P : Fin 3 → F} (h : W.nonsingular P) (hPz : P z ≠ 0) :
    W.toAffine.nonsingular (P x / P z ^ 2) (P y / P z ^ 3) :=
  (nonsingular_iff_affine_of_Zne0 hPz).mp h

end Equation

section Polynomial

/-! ### Group operation polynomials -/

/-- The $Y$-coordinate of the negation of a point representative. -/
@[pp_dot]
def negY (P : Fin 3 → R) : R :=
  -P y - W.a₁ * P x * P z - W.a₃ * P z ^ 3

lemma negY_smul (P : Fin 3 → R) (u : Rˣ) : W.negY (u • P) = u ^ 3 * W.negY P := by
  simp only [negY, smul_fin3_ext]
  ring1

/-- The $X$-coordinate of the addition of two point representatives, where their $Z$-coordinates are
non-zero and their $X$-coordinates divided by $Z$-coordinates squared are distinct. -/
@[pp_dot]
def addX_of_Xne (P Q : Fin 3 → R) : R :=
  (P y * Q z ^ 3 - P z ^ 3 * Q y) ^ 2
    + W.a₁ * P z * Q z * (P y * Q z ^ 3 - P z ^ 3 * Q y) * (P x * Q z ^ 2 - P z ^ 2 * Q x)
    - (W.a₂ * P z ^ 2 * Q z ^ 2 + P x * Q z ^ 2 + P z ^ 2 * Q x)
      * (P x * Q z ^ 2 - P z ^ 2 * Q x) ^ 2

lemma addX_of_Xne_smul (P Q : Fin 3 → R) (u v : Rˣ) :
    W.addX_of_Xne (u • P) (v • Q) = (u : R) ^ 6 * (v : R) ^ 6 * W.addX_of_Xne P Q := by
  simp only [addX_of_Xne, smul_fin3_ext]
  ring1

/-- The $X$-coordinate of the doubling of a point representative, where its $Z$-coordinate is
non-zero and its $Y$-coordinate is distinct from that of its negation. -/
@[pp_dot]
def addX_of_Yne (P : Fin 3 → R) : R :=
  (3 * P x ^ 2 + 2 * W.a₂ * P x * P z ^ 2 + W.a₄ * P z ^ 4 - W.a₁ * P y * P z) ^ 2
    + W.a₁ * (3 * P x ^ 2 + 2 * W.a₂ * P x * P z ^ 2 + W.a₄ * P z ^ 4 - W.a₁ * P y * P z)
      * (P y * P z - W.negY P * P z)
    - (W.a₂ * P z ^ 2 + 2 * P x) * (P y - W.negY P) ^ 2

lemma addX_of_Yne_smul (P : Fin 3 → R) (u : Rˣ) :
    W.addX_of_Yne (u • P) = (u : R) ^ 8 * W.addX_of_Yne P := by
  simp only [addX_of_Yne, negY_smul, smul_fin3_ext]
  ring1

/-- The $Y$-coordinate of the addition of two point representatives, before applying the final
negation that maps $Y$ to $-Y - a_1XZ - a_3Z^3$, where their $Z$-coordinates are non-zero and their
$X$-coordinates divided by $Z$-coordinates squared are distinct. -/
@[pp_dot]
def addY'_of_Xne (P Q : Fin 3 → R) : R :=
  (P y * Q z ^ 3 - P z ^ 3 * Q y)
      * (W.addX_of_Xne P Q - P x * Q z ^ 2 * (P x * Q z ^ 2 - P z ^ 2 * Q x) ^ 2)
    + P y * Q z ^ 3 * (P x * Q z ^ 2 - P z ^ 2 * Q x) ^ 3

lemma addY'_of_Xne_smul (P Q : Fin 3 → R) (u v : Rˣ) :
    W.addY'_of_Xne (u • P) (v • Q) = (u : R) ^ 9 * (v : R) ^ 9 * W.addY'_of_Xne P Q := by
  simp only [addY'_of_Xne, addX_of_Xne_smul, smul_fin3_ext]
  ring1

/-- The $Y$-coordinate of the doubling of a point representative, before applying the final negation
that maps $Y$ to $-Y - a_1XZ - a_3Z^3$, where its $Z$-coordinate is non-zero and its $Y$-coordinate
is distinct from that of its negation. -/
@[pp_dot]
def addY'_of_Yne (P : Fin 3 → R) : R :=
  (3 * P x ^ 2 + 2 * W.a₂ * P x * P z ^ 2 + W.a₄ * P z ^ 4 - W.a₁ * P y * P z)
      * (W.addX_of_Yne P - P x * (P y - W.negY P) ^ 2)
    + P y * (P y - W.negY P) ^ 3

lemma addY'_of_Yne_smul (P : Fin 3 → R) (u : Rˣ) :
    W.addY'_of_Yne (u • P) = (u : R) ^ 12 * W.addY'_of_Yne P := by
  simp only [addY'_of_Yne, addX_of_Yne_smul, negY_smul, smul_fin3_ext]
  ring1

/-- The $Z$-coordinate of the addition of two point representatives, where their $Z$-coordinates are
non-zero and their $X$-coordinates divided by $Z$-coordinates squared are distinct. -/
def addZ_of_Xne (P Q : Fin 3 → R) : R :=
  P z * Q z * (P x * Q z ^ 2 - P z ^ 2 * Q x)

lemma addZ_of_Xne_smul (P Q : Fin 3 → R) (u v : Rˣ) :
    addZ_of_Xne (u • P) (v • Q) = (u : R) ^ 3 * (v : R) ^ 3 * addZ_of_Xne P Q := by
  simp only [addZ_of_Xne, smul_fin3_ext]
  ring1

/-- The $Z$-coordinate of the doubling of a point representative, where its $Z$-coordinate is
non-zero and its $Y$-coordinate is distinct from that of its negation. -/
@[pp_dot]
def addZ_of_Yne (P : Fin 3 → R) : R :=
  P z * (P y - W.negY P)

lemma addZ_of_Yne_smul (P : Fin 3 → R) (u : Rˣ) :
    W.addZ_of_Yne (u • P) = (u : R) ^ 4 * W.addZ_of_Yne P := by
  simp only [addZ_of_Yne, negY_smul, smul_fin3_ext]
  ring1

/-- The $Y$-coordinate of the addition of two point representatives, where their $Z$-coordinates are
non-zero and their $X$-coordinates divided by $Z$-coordinates squared are distinct. -/
@[pp_dot]
def addY_of_Xne (P Q : Fin 3 → R) : R :=
  W.negY ![W.addX_of_Xne P Q, W.addY'_of_Xne P Q, addZ_of_Xne P Q]

lemma addY_of_Xne_smul (P Q : Fin 3 → R) (u v : Rˣ) :
    W.addY_of_Xne (u • P) (v • Q) = (u : R) ^ 9 * (v : R) ^ 9 * W.addY_of_Xne P Q := by
  simp only [addY_of_Xne, negY, addX_of_Xne_smul, addY'_of_Xne_smul, addZ_of_Xne_smul]
  matrix_simp
  ring1

/-- The $Y$-coordinate of the doubling of a point representative, where its $Z$-coordinate is
non-zero and its $Y$-coordinate is distinct from that of its negation. -/
@[pp_dot]
def addY_of_Yne (P : Fin 3 → R) : R :=
  W.negY ![W.addX_of_Yne P, W.addY'_of_Yne P, W.addZ_of_Yne P]

lemma addY_of_Yne_smul (P : Fin 3 → R) (u : Rˣ) :
    W.addY_of_Yne (u • P) = (u : R) ^ 12 * W.addY_of_Yne P := by
  simp only [addY_of_Yne, negY, addX_of_Yne_smul, addY'_of_Yne_smul, addZ_of_Yne_smul]
  matrix_simp
  ring1

variable {F : Type u} [Field F] {W : Jacobian F}

lemma negY_divZ {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.negY P / P z ^ 3 = W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3) := by
  field_simp [negY, Affine.negY]
  ring1

lemma Yne_of_Yne {P Q : Fin 3 → F} (hP : W.nonsingular P) (hQ : W.nonsingular Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = P z ^ 2 * Q x) (hy : P y * Q z ^ 3 ≠ P z ^ 3 * W.negY Q) :
    P y ≠ W.negY P := by
  simp only [mul_comm <| P z ^ _, ne_eq, ← div_eq_div_iff (pow_ne_zero _ hPz) (pow_ne_zero _ hQz)]
    at hx hy
  have hx' : P x * (P z / P z ^ 3) = Q x * (Q z / Q z ^ 3) := by
    simp_rw [pow_succ _ 2, div_mul_right _ hPz, div_mul_right _ hQz, mul_one_div, hx]
  have hy' : P y / P z ^ 3 = Q y / Q z ^ 3 :=
    Affine.Yeq_of_Yne (nonsingular_affine_of_Zne0 hP hPz).left
      (nonsingular_affine_of_Zne0 hQ hQz).left hx <| (negY_divZ hQz).symm ▸ hy
  simp_rw [negY, sub_div, neg_div, mul_div_assoc, mul_assoc, ← hy', ← hx',
    div_self <| pow_ne_zero 3 hQz, ← div_self <| pow_ne_zero 3 hPz, ← mul_assoc, ← mul_div_assoc,
    ← neg_div, ← sub_div, div_left_inj' <| pow_ne_zero 3 hPz] at hy
  exact hy

lemma addX_div_addZ_of_Xne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 ≠ P z ^ 2 * Q x) : W.addX_of_Xne P Q / addZ_of_Xne P Q ^ 2 =
      W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
        (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [Affine.slope_of_Xne <|
    by rwa [ne_eq, div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz), mul_comm <| Q x]]
  field_simp [sub_ne_zero_of_ne hx, addX_of_Xne, addZ_of_Xne]
  ring1

lemma addX_div_addZ_of_Yne {P Q : Fin 3 → F} (hP : W.nonsingular P) (hQ : W.nonsingular Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = P z ^ 2 * Q x)
    (hy : P y * Q z ^ 3 ≠ P z ^ 3 * W.negY Q) :
    W.addX_of_Yne P / W.addZ_of_Yne P ^ 2 = W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  have := sub_ne_zero_of_ne <| Yne_of_Yne hP hQ hPz hQz hx hy
  simp only [mul_comm <| P z ^ _, ne_eq, ← div_eq_div_iff (pow_ne_zero _ hPz) (pow_ne_zero _ hQz)]
    at hx hy
  rw [Affine.slope_of_Yne hx <| (negY_divZ hQz).symm ▸ hy, ← hx, ← negY_divZ hPz]
  field_simp [addX_of_Yne, addX_of_Yne, addZ_of_Yne]
  ring1

lemma addY'_div_addZ_of_Xne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 ≠ P z ^ 2 * Q x) : W.addY'_of_Xne P Q / addZ_of_Xne P Q ^ 3 =
      W.toAffine.addY' (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
        (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [Affine.addY', ← addX_div_addZ_of_Xne hPz hQz hx, Affine.slope_of_Xne <|
    by rwa [ne_eq, div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz), mul_comm <| Q x]]
  field_simp [sub_ne_zero_of_ne hx, addY'_of_Xne, addX_of_Xne, addZ_of_Xne]
  ring1

lemma addY'_div_addZ_of_Yne {P Q : Fin 3 → F} (hP : W.nonsingular P) (hQ : W.nonsingular Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = P z ^ 2 * Q x)
    (hy : P y * Q z ^ 3 ≠ P z ^ 3 * W.negY Q) : W.addY'_of_Yne P / W.addZ_of_Yne P ^ 3 =
    W.toAffine.addY' (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  have := sub_ne_zero_of_ne <| Yne_of_Yne hP hQ hPz hQz hx hy
  rw [Affine.addY', ← addX_div_addZ_of_Yne hP hQ hPz hQz hx hy]
  simp only [mul_comm <| P z ^ _, ne_eq, ← div_eq_div_iff (pow_ne_zero _ hPz) (pow_ne_zero _ hQz)]
    at hx hy
  rw [Affine.slope_of_Yne hx <| (negY_divZ hQz).symm ▸ hy, ← negY_divZ hPz]
  field_simp [addY'_of_Yne, addX_of_Yne, addZ_of_Yne]
  ring1

lemma addZ_ne_zero_of_Xne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 ≠ P z ^ 2 * Q x) : addZ_of_Xne P Q ≠ 0 :=
  mul_ne_zero (mul_ne_zero hPz hQz) <| sub_ne_zero_of_ne hx

lemma addZ_ne_zero_of_Yne {P Q : Fin 3 → F} (hP : W.nonsingular P) (hQ : W.nonsingular Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = P z ^ 2 * Q x)
    (hy : P y * Q z ^ 3 ≠ P z ^ 3 * W.negY Q) : W.addZ_of_Yne P ≠ 0 :=
  mul_ne_zero hPz <| sub_ne_zero_of_ne <| Yne_of_Yne hP hQ hPz hQz hx hy

lemma addY_div_addZ_of_Xne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 ≠ P z ^ 2 * Q x) : W.addY_of_Xne P Q / addZ_of_Xne P Q ^ 3 =
      W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
        (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [Affine.addY, ← addX_div_addZ_of_Xne hPz hQz hx, ← addY'_div_addZ_of_Xne hPz hQz hx]
  exact negY_divZ <| addZ_ne_zero_of_Xne hPz hQz hx

lemma addY_div_addZ_of_Yne {P Q : Fin 3 → F} (hP : W.nonsingular P) (hQ : W.nonsingular Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = P z ^ 2 * Q x)
    (hy : P y * Q z ^ 3 ≠ P z ^ 3 * W.negY Q) : W.addY_of_Yne P / W.addZ_of_Yne P ^ 3 =
      W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
        (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [Affine.addY, ← addX_div_addZ_of_Yne hP hQ hPz hQz hx hy,
    ← addY'_div_addZ_of_Yne hP hQ hPz hQz hx hy]
  exact negY_divZ <| addZ_ne_zero_of_Yne hP hQ hPz hQz hx hy

end Polynomial

section Representative

/-! ### Group operations on point representatives -/

/-- The negation of a point representative. -/
@[pp_dot]
def neg (P : Fin 3 → R) : Fin 3 → R :=
  ![P x, W.negY P, P z]

@[simp]
lemma neg_zero : W.neg ![1, 1, 0] = ![1, -1, 0] := by
  erw [neg, negY, mul_zero, zero_pow three_pos, mul_zero, sub_zero, sub_zero]
  rfl

@[simp]
lemma neg_some (X Y : R) : W.neg ![X, Y, 1] = ![X, -Y - W.a₁ * X - W.a₃, 1] := by
  erw [neg, negY, mul_one, one_pow, mul_one]
  rfl

lemma neg_smul_equiv (P : Fin 3 → R) (u : Rˣ) : W.neg (u • P) ≈ W.neg P :=
  ⟨u, by simp_rw [neg, negY_smul, smul_fin3]; rfl⟩

lemma neg_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W.neg P ≈ W.neg Q := by
  rcases h with ⟨u, rfl⟩
  exact W.neg_smul_equiv Q u

/-- The negation of a point class. If `P` is a point representative,
then `W.neg_map ⟦P⟧` is definitionally equivalent to `W.neg P`. -/
@[pp_dot]
def neg_map (P : PointClass R) : PointClass R :=
  P.map W.neg fun _ _ => W.neg_equiv

lemma neg_map_eq {P : Fin 3 → R} : W.neg_map ⟦P⟧ = ⟦W.neg P⟧ :=
  rfl

@[simp]
lemma neg_map_zero : W.neg_map ⟦![1, 1, 0]⟧ = ⟦![1, 1, 0]⟧ := by
  simpa only [neg_map_eq, neg_zero, Quotient.eq] using ⟨-1, by norm_num [smul_fin3]⟩

@[simp]
lemma neg_map_some (X Y : R) : W.neg_map ⟦![X, Y, 1]⟧ = ⟦![X, -Y - W.a₁ * X - W.a₃, 1]⟧ := by
  rw [neg_map_eq, neg_some]

open scoped Classical

/-- The addition of two point representatives. -/
@[pp_dot]
noncomputable def add (P Q : Fin 3 → R) : Fin 3 → R :=
  if P z = 0 then Q else if Q z = 0 then P else if P x * Q z ^ 2 = P z ^ 2 * Q x then
    if P y * Q z ^ 3 = P z ^ 3 * W.negY Q then ![1, 1, 0] else
      ![W.addX_of_Yne P, W.addY_of_Yne P, W.addZ_of_Yne P]
  else ![W.addX_of_Xne P Q, W.addY_of_Xne P Q, addZ_of_Xne P Q]

@[simp]
lemma add_of_Zeq0_left {P Q : Fin 3 → R} (hPz : P z = 0) : W.add P Q = Q :=
  if_pos hPz

lemma add_zero_left (P : Fin 3 → R) : W.add ![1, 1, 0] P = P :=
  W.add_of_Zeq0_left rfl

@[simp]
lemma add_of_Zeq0_right {P Q : Fin 3 → R} (hPz : P z ≠ 0) (hQz : Q z = 0) : W.add P Q = P := by
  rw [add, if_neg hPz, if_pos hQz]

lemma add_zero_right {P : Fin 3 → R} (hPz : P z ≠ 0) : W.add P ![1, 1, 0] = P :=
  W.add_of_Zeq0_right hPz rfl

@[simp]
lemma add_of_Yeq {P Q : Fin 3 → R} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = P z ^ 2 * Q x) (hy : P y * Q z ^ 3 = P z ^ 3 * W.negY Q) :
    W.add P Q = ![1, 1, 0] := by
  rw [add, if_neg hPz, if_neg hQz, if_pos hx, if_pos hy]

@[simp]
lemma add_of_Yne {P Q : Fin 3 → R} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = P z ^ 2 * Q x) (hy : P y * Q z ^ 3 ≠ P z ^ 3 * W.negY Q) :
    W.add P Q = ![W.addX_of_Yne P, W.addY_of_Yne P, W.addZ_of_Yne P] := by
  rw [add, if_neg hPz, if_neg hQz, if_pos hx, if_neg hy]

@[simp]
lemma add_of_Xne {P Q : Fin 3 → R} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 ≠ P z ^ 2 * Q x) :
    W.add P Q = ![W.addX_of_Xne P Q, W.addY_of_Xne P Q, addZ_of_Xne P Q] := by
  rw [add, if_neg hPz, if_neg hQz, if_neg hx]

variable [IsDomain R]

lemma add_smul_equiv (P Q : Fin 3 → R) (u v : Rˣ) : W.add (u • P) (v • Q) ≈ W.add P Q := by
  have huv (n : ℕ) : (u ^ n * v ^ n : R) ≠ 0 :=
    mul_ne_zero (pow_ne_zero n u.ne_zero) (pow_ne_zero n v.ne_zero)
  by_cases hPz : P z = 0
  · exact ⟨v, by rw [W.add_of_Zeq0_left hPz,
      W.add_of_Zeq0_left <| by simp only [smul_fin3_ext, hPz, mul_zero]]⟩
  · have huz : u * P z ≠ 0 := mul_ne_zero u.ne_zero hPz
    by_cases hQz : Q z = 0
    · rw [W.add_of_Zeq0_right hPz hQz,
        W.add_of_Zeq0_right huz <| by simp only [smul_fin3_ext, hQz, mul_zero]]
      exact ⟨u, rfl⟩
    · have hvz : v * Q z ≠ 0 := mul_ne_zero v.ne_zero hQz
      by_cases hx : P x * Q z ^ 2 = P z ^ 2 * Q x
      · by_cases hy : P y * Q z ^ 3 = P z ^ 3 * W.negY Q
        · rw [W.add_of_Yeq huz hvz (by simp_rw [smul_fin3_ext, mul_pow, mul_mul_mul_comm, hx]) <| by
            simp_rw [smul_fin3_ext, mul_pow, negY_smul, mul_mul_mul_comm, hy],
            W.add_of_Yeq hPz hQz hx hy]
        · rw [W.add_of_Yne huz hvz (by simp_rw [smul_fin3_ext, mul_pow, mul_mul_mul_comm, hx]) <| by
            simp_rw [smul_fin3_ext, mul_pow, negY_smul, mul_mul_mul_comm]
            exact hy ∘ mul_left_cancel₀ (huv 3),
            addX_of_Yne_smul, addY_of_Yne_smul, addZ_of_Yne_smul, W.add_of_Yne hPz hQz hx hy]
          exact ⟨u ^ 4, by simp only [smul_fin3, ← Units.val_pow_eq_pow_val, ← pow_mul]; rfl⟩
      · rw [W.add_of_Xne huz hvz <| by
          simp_rw [smul_fin3_ext, mul_pow, mul_mul_mul_comm]; exact hx ∘ mul_left_cancel₀ (huv 2),
          addX_of_Xne_smul, addY_of_Xne_smul, addZ_of_Xne_smul, W.add_of_Xne hPz hQz hx]
        exact ⟨u ^ 3 * v ^ 3,
          by simp_rw [smul_fin3, ← Units.val_pow_eq_pow_val, mul_pow, ← pow_mul]; rfl⟩

lemma add_equiv {P P' Q Q' : Fin 3 → R} (hP : P ≈ P') (hQ : Q ≈ Q') : W.add P Q ≈ W.add P' Q' := by
  rcases hP, hQ with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  exact W.add_smul_equiv P' Q' u v

/-- The addition of two point classes. If `P` is a point representative,
then `W.add_map ⟦P⟧ ⟦Q⟧` is definitionally equivalent to `W.add P Q`. -/
@[pp_dot]
noncomputable def add_map (P Q : PointClass R) : PointClass R :=
  Quotient.map₂ W.add (fun _ _ hP _ _ hQ => W.add_equiv hP hQ) P Q

lemma add_map_eq (P Q : Fin 3 → R) : W.add_map ⟦P⟧ ⟦Q⟧ = ⟦W.add P Q⟧ :=
  rfl

@[simp]
lemma add_map_of_Zeq0_left {P : Fin 3 → R} {Q : PointClass R} (hPz : P z = 0) :
    W.add_map ⟦P⟧ Q = Q := by
  rcases Q with ⟨Q⟩
  erw [add_map_eq, W.add_of_Zeq0_left hPz]
  rfl

lemma add_map_zero_left (P : PointClass R) : W.add_map ⟦![1, 1, 0]⟧ P = P :=
  W.add_map_of_Zeq0_left rfl

@[simp]
lemma add_map_of_Zeq0_right {P Q : Fin 3 → R} (hPz : P z ≠ 0) (hQz : Q z = 0) :
    W.add_map ⟦P⟧ ⟦Q⟧ = ⟦P⟧ := by
  rw [add_map_eq, W.add_of_Zeq0_right hPz hQz]

lemma add_map_zero_right {P : Fin 3 → R} (hPz : P z ≠ 0) : W.add_map ⟦P⟧ ⟦![1, 1, 0]⟧ = ⟦P⟧ := by
  rw [add_map_eq, W.add_zero_right hPz]

@[simp]
lemma add_map_of_Yeq {P Q : Fin 3 → R} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = P z ^ 2 * Q x) (hy : P y * Q z ^ 3 = P z ^ 3 * W.negY Q) :
    W.add_map ⟦P⟧ ⟦Q⟧ = ⟦![1, 1, 0]⟧ := by
  rw [add_map_eq, W.add_of_Yeq hPz hQz hx hy]

@[simp]
lemma add_map_of_Yne {P Q : Fin 3 → R} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = P z ^ 2 * Q x) (hy : P y * Q z ^ 3 ≠ P z ^ 3 * W.negY Q) :
    W.add_map ⟦P⟧ ⟦Q⟧ = ⟦![W.addX_of_Yne P, W.addY_of_Yne P, W.addZ_of_Yne P]⟧ := by
  rw [add_map_eq, W.add_of_Yne hPz hQz hx hy]

@[simp]
lemma add_map_of_Xne {P Q : Fin 3 → R} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 ≠ P z ^ 2 * Q x) :
    W.add_map ⟦P⟧ ⟦Q⟧ = ⟦![W.addX_of_Xne P Q, W.addY_of_Xne P Q, addZ_of_Xne P Q]⟧ := by
  rw [add_map_eq, W.add_of_Xne hPz hQz hx]

variable {F : Type u} [Field F] {W : Jacobian F}

@[simp]
lemma add_map_of_Zeq0_right' {P : PointClass F} {Q : Fin 3 → F} (hP : W.nonsingular_lift P)
    (hQ : W.nonsingular Q) (hQz : Q z = 0) : W.add_map P ⟦Q⟧ = P := by
  rcases P with ⟨P⟩
  by_cases hPz : P z = 0
  · erw [W.add_map_of_Zeq0_left hPz, Quotient.eq]
    exact equiv_of_Zeq0 hQ hP hQz hPz
  · exact W.add_map_of_Zeq0_right hPz hQz

lemma add_map_zero_right' {P : PointClass F} (hP : W.nonsingular_lift P) :
    W.add_map P ⟦![1, 1, 0]⟧ = P :=
  add_map_of_Zeq0_right' hP W.nonsingular_zero rfl

variable {F : Type u} [Field F] {W : Jacobian F}

/-- The negation of a nonsingular point representative in `W` lies in `W`. -/
lemma nonsingular_neg {P : Fin 3 → F} (h : W.nonsingular P) : W.nonsingular <| W.neg P := by
  by_cases hPz : P z = 0
  · rw [W.nonsingular_of_equiv <| W.neg_equiv <| equiv_zero_of_Zeq0 h hPz, neg_zero]
    convert W.nonsingular_zero' <| neg_ne_zero.mpr one_ne_zero <;> norm_num1
  · rw [nonsingular_iff_affine_of_Zne0 <| by exact hPz] at h ⊢
    rwa [← Affine.nonsingular_neg_iff, ← negY_divZ hPz] at h

lemma nonsingular_lift_neg_map {P : PointClass F} (h : W.nonsingular_lift P) :
    W.nonsingular_lift <| W.neg_map P := by
  rcases P with ⟨_⟩
  exact nonsingular_neg h

/-- The addition of two nonsingular point representatives in `W` lies in `W`. -/
lemma nonsingular_add {P Q : Fin 3 → F} (hP : W.nonsingular P) (hQ : W.nonsingular Q) :
    W.nonsingular <| W.add P Q := by
  by_cases hPz : P z = 0
  · rwa [W.nonsingular_of_equiv <| W.add_equiv (equiv_zero_of_Zeq0 hP hPz) <| Setoid.refl Q,
      W.add_of_Zeq0_left <| by exact rfl]
  · by_cases hQz : Q z = 0
    · rwa [W.nonsingular_of_equiv <| W.add_equiv (Setoid.refl P) <| equiv_zero_of_Zeq0 hQ hQz,
        W.add_of_Zeq0_right hPz <| by exact rfl]
    · by_cases hx : P x * Q z ^ 2 = P z ^ 2 * Q x
      · by_cases hy : P y * Q z ^ 3 = P z ^ 3 * W.negY Q
        · simpa only [W.add_of_Yeq hPz hQz hx hy] using W.nonsingular_zero
        · erw [W.add_of_Yne hPz hQz hx hy,
            nonsingular_iff_affine_of_Zne0 <| addZ_ne_zero_of_Yne hP hQ hPz hQz hx hy,
            addX_div_addZ_of_Yne hP hQ hPz hQz hx hy, addY_div_addZ_of_Yne hP hQ hPz hQz hx hy]
          exact W.toAffine.nonsingular_add (nonsingular_affine_of_Zne0 hP hPz)
            (nonsingular_affine_of_Zne0 hQ hQz) fun _ => (negY_divZ hQz).symm ▸ Function.comp
            (mul_comm (P z ^ 3) _ ▸ hy) (div_eq_div_iff (pow_ne_zero 3 hPz) (pow_ne_zero 3 hQz)).mp
      · erw [W.add_of_Xne hPz hQz hx,
          nonsingular_iff_affine_of_Zne0 <| addZ_ne_zero_of_Xne hPz hQz hx,
          addX_div_addZ_of_Xne hPz hQz hx, addY_div_addZ_of_Xne hPz hQz hx]
        exact W.toAffine.nonsingular_add (nonsingular_affine_of_Zne0 hP hPz)
          (nonsingular_affine_of_Zne0 hQ hQz) fun h => False.elim <| hx <|
          mul_comm (Q x) _ ▸ (div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz)).mp h

lemma nonsingular_lift_add_map {P Q : PointClass F} (hP : W.nonsingular_lift P)
    (hQ : W.nonsingular_lift Q) : W.nonsingular_lift <| W.add_map P Q := by
  rcases P, Q with ⟨⟨_⟩, ⟨_⟩⟩
  exact nonsingular_add hP hQ

end Representative

section Point

/-! ### Group operations on nonsingular rational points -/

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
to the corresponding nonsingular rational point on `W` in Jacobian coordinates. -/
def fromAffine [Nontrivial R] : W.toAffine.Point → W.Point
  | 0 => 0
  | Affine.Point.some h => ⟨(W.nonsingular_lift_some ..).mpr h⟩

@[simp]
lemma fromAffine_zero [Nontrivial R] : fromAffine 0 = (0 : W.Point) :=
  rfl

@[simp]
lemma fromAffine_some [Nontrivial R] {X Y : R} (h : W.toAffine.nonsingular X Y) :
    fromAffine (Affine.Point.some h) = ⟨(W.nonsingular_lift_some ..).mpr h⟩ :=
  rfl

variable {F : Type u} [Field F] {W : Jacobian F}

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

noncomputable instance instAddZeroClassPoint : AddZeroClass W.Point :=
  ⟨zero_add, add_zero⟩

open scoped Classical

/-- The map from a point representative that is nonsingular on a Weierstrass curve `W` in Jacobian
coordinates to the corresponding nonsingular rational point on `W` in affine coordinates. -/
noncomputable def toAffine {P : Fin 3 → F} (h : W.nonsingular P) : W.toAffine.Point :=
  if hPz : P z = 0 then 0 else Affine.Point.some <| nonsingular_affine_of_Zne0 h hPz

lemma toAffine_of_Zeq0 {P : Fin 3 → F} {h : W.nonsingular P} (hPz : P z = 0) : toAffine h = 0 :=
  dif_pos hPz

lemma toAffine_zero : toAffine W.nonsingular_zero = 0 :=
  toAffine_of_Zeq0 rfl

lemma toAffine_of_Zne0 {P : Fin 3 → F} {h : W.nonsingular P} (hPz : P z ≠ 0) :
    toAffine h = Affine.Point.some (nonsingular_affine_of_Zne0 h hPz) :=
  dif_neg hPz

lemma toAffine_some {X Y : F} (h : W.nonsingular ![X, Y, 1]) :
    toAffine h = Affine.Point.some ((W.nonsingular_some X Y).mp h) := by
  rw [toAffine_of_Zne0 <| by exact one_ne_zero]
  matrix_simp
  simp only [one_pow, div_one]

lemma toAffine_neg {P : Fin 3 → F} (hP : W.nonsingular P) :
    toAffine (nonsingular_neg hP) = -toAffine hP := by
  by_cases hPz : P z = 0
  · rw [toAffine_of_Zeq0 <| by exact hPz, toAffine_of_Zeq0 hPz, Affine.Point.neg_zero]
  · rw [toAffine_of_Zne0 <| by exact hPz, toAffine_of_Zne0 hPz, Affine.Point.neg_some,
      Affine.Point.some.injEq]
    exact ⟨rfl, negY_divZ hPz⟩

lemma toAffine_add {P Q : Fin 3 → F} (hP : W.nonsingular P) (hQ : W.nonsingular Q) :
    toAffine (nonsingular_add hP hQ) = toAffine hP + toAffine hQ := by
  by_cases hPz : P z = 0
  · simp only [W.add_of_Zeq0_left (Q := Q) hPz, toAffine_of_Zeq0 hPz, _root_.zero_add]
  · by_cases hQz : Q z = 0
    · simp only [W.add_of_Zeq0_right hPz hQz, toAffine_of_Zeq0 hQz, _root_.add_zero]
    · by_cases hx : P x * Q z ^ 2 = P z ^ 2 * Q x
      · have hx' : P x / P z ^ 2 = Q x / Q z ^ 2 :=
          (div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz)).mpr <| mul_comm (P z ^ 2) _ ▸ hx
        rw [toAffine_of_Zne0 hPz, toAffine_of_Zne0 hQz]
        by_cases hy : P y * Q z ^ 3 = P z ^ 3 * W.negY Q
        · have hy' : P y / P z ^ 3 = W.negY Q / Q z ^ 3 := Iff.mpr
            (div_eq_div_iff (pow_ne_zero 3 hPz) (pow_ne_zero 3 hQz)) <| mul_comm (P z ^ 3) _ ▸ hy
          simp only [W.add_of_Yeq hPz hQz hx hy]
          rw [toAffine_zero, Affine.Point.some_add_some_of_Yeq hx' <| by rwa [← negY_divZ hQz]]
        · have hy' : P y / P z ^ 3 ≠ W.negY Q / Q z ^ 3 := Function.comp
            (mul_comm (P z ^ 3) _ ▸ hy) (div_eq_div_iff (pow_ne_zero 3 hPz) (pow_ne_zero 3 hQz)).mp
          simp only [W.add_of_Yne hPz hQz hx hy]
          rw [toAffine_of_Zne0 <| addZ_ne_zero_of_Yne hP hQ hPz hQz hx hy,
            Affine.Point.some_add_some_of_Yne hx' <| (negY_divZ hQz).symm ▸ hy',
            Affine.Point.some.injEq]
          exact ⟨addX_div_addZ_of_Yne hP hQ hPz hQz hx hy, addY_div_addZ_of_Yne hP hQ hPz hQz hx hy⟩
      · have hx' : P x / P z ^ 2 ≠ Q x / Q z ^ 2 :=
          (mul_comm (P z ^ 2) _ ▸ hx) ∘ (div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz)).mp
        simp only [W.add_of_Xne hPz hQz hx]
        rw [toAffine_of_Zne0 <| addZ_ne_zero_of_Xne hPz hQz hx, toAffine_of_Zne0 hPz,
          toAffine_of_Zne0 hQz, Affine.Point.some_add_some_of_Xne hx', Affine.Point.some.injEq]
        exact ⟨addX_div_addZ_of_Xne hPz hQz hx, addY_div_addZ_of_Xne hPz hQz hx⟩

lemma toAffine_of_equiv (P Q : Fin 3 → F) (h : P ≈ Q) :
    HEq (toAffine (W := W) (P := P)) (toAffine (W := W) (P := Q)) := by
  rcases h with ⟨u, rfl⟩
  refine Function.hfunext (propext <| W.nonsingular_smul_iff Q u) <| fun _ _ _ => ?_
  by_cases hPz : Q z = 0
  · rw [toAffine_of_Zeq0 <| by exact u.mul_right_eq_zero.mpr hPz, toAffine_of_Zeq0 hPz]
  · rw [toAffine_of_Zne0 <| by exact mul_ne_zero u.ne_zero hPz, toAffine_of_Zne0 hPz, heq_eq_eq]
    simp only [Affine.Point.some.injEq, smul_fin3_ext, mul_pow,
      mul_div_mul_left _ _ <| pow_ne_zero _ u.ne_zero, and_self]

/-- The map from a nonsingular rational point on a Weierstrass curve `W` in Jacobian coordinates
to the corresponding nonsingular rational point on `W` in affine coordinates. -/
noncomputable def toAffine_lift (P : W.Point) : W.toAffine.Point :=
  P.point.hrecOn (fun _ => toAffine) toAffine_of_equiv P.nonsingular

lemma toAffine_lift_eq {P : Fin 3 → F} (h : W.nonsingular_lift ⟦P⟧) :
    toAffine_lift ⟨h⟩ = toAffine h :=
  rfl

lemma toAffine_lift_of_Zeq0 {P : Fin 3 → F} {h : W.nonsingular_lift ⟦P⟧} (hPz : P z = 0) :
    toAffine_lift ⟨h⟩ = 0 :=
  toAffine_of_Zeq0 hPz (h := h)

lemma toAffine_lift_zero : toAffine_lift (0 : W.Point) = 0 :=
  toAffine_zero

lemma toAffine_lift_of_Zne0 {P : Fin 3 → F} {h : W.nonsingular_lift ⟦P⟧} (hPz : P z ≠ 0) :
    toAffine_lift ⟨h⟩ = Affine.Point.some (nonsingular_affine_of_Zne0 h hPz) :=
  toAffine_of_Zne0 hPz (h := h)

lemma toAffine_lift_some {X Y : F} (h : W.nonsingular_lift ⟦![X, Y, 1]⟧) :
    toAffine_lift ⟨h⟩ = Affine.Point.some ((W.nonsingular_some X Y).mp h) :=
  toAffine_some h

lemma toAffine_lift_neg {P : Fin 3 → F} (h : W.nonsingular_lift ⟦P⟧) :
    toAffine_lift (-⟨h⟩) = -toAffine_lift ⟨h⟩ :=
  toAffine_neg h

lemma toAffine_lift_add {P Q : Fin 3 → F} (hP : W.nonsingular_lift ⟦P⟧)
    (hQ : W.nonsingular_lift ⟦Q⟧) :
    toAffine_lift (⟨hP⟩ + ⟨hQ⟩) = toAffine_lift ⟨hP⟩ + toAffine_lift ⟨hQ⟩ :=
  toAffine_add hP hQ

/-- The equivalence between the nonsingular rational points on a Weierstrass curve `W` in Jacobian
coordinates with the nonsingular rational points on `W` in affine coordinates. -/
@[simps]
noncomputable def toAffine_addEquiv : W.Point ≃+ W.toAffine.Point where
  toFun := toAffine_lift
  invFun := fromAffine
  left_inv := by
    rintro @⟨⟨P⟩, h⟩
    by_cases hPz : P z = 0
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

end Point

end WeierstrassCurve.Jacobian
