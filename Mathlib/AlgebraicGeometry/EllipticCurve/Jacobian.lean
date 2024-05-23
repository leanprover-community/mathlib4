/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine

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
 * `WeierstrassCurve.Jacobian.Nonsingular`: the nonsingular condition on a point representative.
 * `WeierstrassCurve.Jacobian.NonsingularLift`: the nonsingular condition on a point class.
 * `WeierstrassCurve.Jacobian.neg`: the negation operation on a point representative.
 * `WeierstrassCurve.Jacobian.negMap`: the negation operation on a point class.
 * `WeierstrassCurve.Jacobian.add`: the addition operation on a point representative.
 * `WeierstrassCurve.Jacobian.addMap`: the addition operation on a point class.
 * `WeierstrassCurve.Jacobian.Point`: a nonsingular rational point.
 * `WeierstrassCurve.Jacobian.Point.neg`: the negation operation on a nonsingular rational point.
 * `WeierstrassCurve.Jacobian.Point.add`: the addition operation on a nonsingular rational point.
 * `WeierstrassCurve.Jacobian.Point.toAffine_addEquiv`: the equivalence between the nonsingular
    rational points on a Jacobian Weierstrass curve with those on an affine Weierstrass curve.

## Main statements

 * `WeierstrassCurve.Jacobian.NonsingularNeg`: negation preserves the nonsingular condition.
 * `WeierstrassCurve.Jacobian.NonsingularAdd`: addition preserves the nonsingular condition.

## Implementation notes

A point representative is implemented as a term `P` of type `Fin 3 → R`, which allows for the vector
notation `![x, y, z]`. However, `P` is not definitionally equivalent to the expanded vector
`![P x, P y, P z]`, so the lemmas `fin3_def` and `fin3_def_ext` can be used to convert between the
two forms. The equivalence of two point representatives `P` and `Q` is implemented as an equivalence
of orbits of the action of `Rˣ`, or equivalently that there is some unit `u` of `R` such that
`P = u • Q`. However, `u • Q` is not definitionally equal to `![u² * Q x, u³ * Q y, u * Q z]`, so
the auxiliary lemmas `smul_fin3` and `smul_fin3_ext` can be used to convert between the two forms.

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

/-! ## Weierstrass curves -/

/-- An abbreviation for a Weierstrass curve in Jacobian coordinates. -/
abbrev WeierstrassCurve.Jacobian :=
  WeierstrassCurve

namespace WeierstrassCurve.Jacobian

open MvPolynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow])

local macro "pderiv_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, pderiv_mul, pderiv_pow,
    pderiv_C, pderiv_X_self, pderiv_X_of_ne one_ne_zero, pderiv_X_of_ne one_ne_zero.symm,
    pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0), pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 2),
    pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 1), pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 2)])

variable {R : Type u} [CommRing R] {V : Jacobian R} {F : Type u} [Field F] {W : Jacobian F}

section Jacobian

/-! ### Jacobian coordinates -/

lemma fin3_def (P : Fin 3 → R) : ![P x, P y, P z] = P := by
  ext n; fin_cases n <;> rfl

lemma fin3_def_ext (X Y Z : R) : ![X, Y, Z] x = X ∧ ![X, Y, Z] y = Y ∧ ![X, Y, Z] z = Z :=
  ⟨rfl, rfl, rfl⟩

/-- The scalar multiplication on a point representative. -/
scoped instance instSMulPoint : SMul Rˣ <| Fin 3 → R :=
  ⟨fun u P => ![u ^ 2 * P x, u ^ 3 * P y, u * P z]⟩

lemma smul_fin3 (P : Fin 3 → R) (u : Rˣ) : u • P = ![u ^ 2 * P x, u ^ 3 * P y, u * P z] :=
  rfl

lemma smul_fin3_ext (P : Fin 3 → R) (u : Rˣ) :
    (u • P) x = u ^ 2 * P x ∧ (u • P) y = u ^ 3 * P y ∧ (u • P) z = u * P z :=
  ⟨rfl, rfl, rfl⟩

/-- The multiplicative action on a point representative. -/
scoped instance instMulActionPoint : MulAction Rˣ <| Fin 3 → R where
  one_smul _ := by simp only [smul_fin3, Units.val_one, one_pow, one_mul, fin3_def]
  mul_smul _ _ _ := by simp only [smul_fin3, Units.val_mul, mul_pow, mul_assoc, fin3_def_ext]

/-- The equivalence setoid for a point representative. -/
scoped instance instSetoidPoint : Setoid <| Fin 3 → R :=
  MulAction.orbitRel Rˣ <| Fin 3 → R

lemma smul_equiv (P : Fin 3 → R) (u : Rˣ) : u • P ≈ P :=
  ⟨u, rfl⟩

/-- The equivalence class of a point representative. -/
abbrev PointClass (R : Type u) [CommRing R] : Type u :=
  MulAction.orbitRel.Quotient Rˣ <| Fin 3 → R

@[simp]
lemma smul_eq (P : Fin 3 → R) (u : Rˣ) : (⟦u • P⟧ : PointClass R) = ⟦P⟧ :=
  Quotient.eq.mpr <| smul_equiv P u

variable (V) in
/-- The coercion to a Weierstrass curve in affine coordinates. -/
abbrev toAffine : Affine R :=
  V

lemma Z_eq_zero_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P z = 0 ↔ Q z = 0 := by
  rcases h with ⟨_, rfl⟩
  simp only [smul_fin3_ext, Units.mul_right_eq_zero]

lemma X_eq_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P x * Q z ^ 2 = Q x * P z ^ 2 := by
  rcases h with ⟨u, rfl⟩
  simp only [smul_fin3_ext]
  ring1

lemma Y_eq_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P y * Q z ^ 3 = Q y * P z ^ 3 := by
  rcases h with ⟨u, rfl⟩
  simp only [smul_fin3_ext]
  ring1

lemma not_equiv_of_Z_eq_zero_left {P Q : Fin 3 → R} (hPz : P z = 0) (hQz : Q z ≠ 0) : ¬P ≈ Q :=
  fun h => hQz <| (Z_eq_zero_of_equiv h).mp hPz

lemma not_equiv_of_Z_eq_zero_right {P Q : Fin 3 → R} (hPz : P z ≠ 0) (hQz : Q z = 0) : ¬P ≈ Q :=
  fun h => hPz <| (Z_eq_zero_of_equiv h).mpr hQz

lemma not_equiv_of_X_ne {P Q : Fin 3 → R} (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : ¬P ≈ Q :=
  hx.comp X_eq_of_equiv

lemma not_equiv_of_Y_ne {P Q : Fin 3 → R} (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) : ¬P ≈ Q :=
  hy.comp Y_eq_of_equiv

lemma equiv_of_X_eq_of_Y_eq {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3) : P ≈ Q := by
  use Units.mk0 _ hPz / Units.mk0 _ hQz
  simp only [smul_fin3, Units.val_div_eq_div_val, Units.val_mk0, div_pow, mul_comm, mul_div, ← hx,
    ← hy, mul_div_cancel_right₀ _ <| pow_ne_zero _ hQz, mul_div_cancel_right₀ _ hQz, fin3_def]

lemma equiv_some_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    P ≈ ![P x / P z ^ 2, P y / P z ^ 3, 1] :=
  equiv_of_X_eq_of_Y_eq hPz one_ne_zero
    (by linear_combination (norm := (matrix_simp; ring1)) -P x * div_self (pow_ne_zero 2 hPz))
    (by linear_combination (norm := (matrix_simp; ring1)) -P y * div_self (pow_ne_zero 3 hPz))

end Jacobian

section Equation

/-! ### Weierstrass equations -/

variable (V) in
/-- The polynomial $W(X, Y, Z) := Y^2 + a_1XYZ + a_3YZ^3 - (X^3 + a_2X^2Z^2 + a_4XZ^4 + a_6Z^6)$
associated to a Weierstrass curve `W` over `R`. This is represented as a term of type
`MvPolynomial (Fin 3) R`, where `X 0`, `X 1`, and `X 2` represent $X$, $Y$, and $Z$ respectively. -/
noncomputable def polynomial : MvPolynomial (Fin 3) R :=
  X 1 ^ 2 + C V.a₁ * X 0 * X 1 * X 2 + C V.a₃ * X 1 * X 2 ^ 3
    - (X 0 ^ 3 + C V.a₂ * X 0 ^ 2 * X 2 ^ 2 + C V.a₄ * X 0 * X 2 ^ 4 + C V.a₆ * X 2 ^ 6)

lemma eval_polynomial (P : Fin 3 → R) : eval P V.polynomial =
    P y ^ 2 + V.a₁ * P x * P y * P z + V.a₃ * P y * P z ^ 3
      - (P x ^ 3 + V.a₂ * P x ^ 2 * P z ^ 2 + V.a₄ * P x * P z ^ 4 + V.a₆ * P z ^ 6) := by
  rw [polynomial]
  eval_simp

lemma eval_polynomial_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) : eval P W.polynomial / P z ^ 6 =
    (W.toAffine.polynomial.eval <| Polynomial.C <| P y / P z ^ 3).eval (P x / P z ^ 2) := by
  linear_combination (norm := (rw [eval_polynomial, Affine.eval_polynomial]; ring1))
    W.a₁ * P x * P y / P z ^ 5 * div_self hPz + W.a₃ * P y / P z ^ 3 * div_self (pow_ne_zero 3 hPz)
      - W.a₂ * P x ^ 2 / P z ^ 4 * div_self (pow_ne_zero 2 hPz)
      - W.a₄ * P x / P z ^ 2 * div_self (pow_ne_zero 4 hPz) - W.a₆ * div_self (pow_ne_zero 6 hPz)

variable (V) in
/-- The proposition that a point representative $(x, y, z)$ lies in `W`.
In other words, $W(x, y, z) = 0$. -/
def Equation (P : Fin 3 → R) : Prop :=
  eval P V.polynomial = 0

lemma equation_iff (P : Fin 3 → R) : V.Equation P ↔
    P y ^ 2 + V.a₁ * P x * P y * P z + V.a₃ * P y * P z ^ 3
      - (P x ^ 3 + V.a₂ * P x ^ 2 * P z ^ 2 + V.a₄ * P x * P z ^ 4 + V.a₆ * P z ^ 6) = 0 := by
  rw [Equation, eval_polynomial]

lemma equation_smul_iff (P : Fin 3 → R) (u : Rˣ) : V.Equation (u • P) ↔ V.Equation P := by
  have (u : Rˣ) {P : Fin 3 → R} (hP : V.Equation P) : V.Equation <| u • P := by
    rw [equation_iff] at hP ⊢
    linear_combination (norm := (simp only [smul_fin3_ext]; ring1)) u ^ 6 * hP
  exact ⟨fun h => by convert this u⁻¹ h; rw [inv_smul_smul], this u⟩

lemma equation_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : V.Equation P ↔ V.Equation Q := by
  rcases h with ⟨u, rfl⟩
  exact equation_smul_iff Q u

lemma equation_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) :
    V.Equation P ↔ P y ^ 2 = P x ^ 3 := by
  simp only [equation_iff, hPz, add_zero, mul_zero, zero_pow <| OfNat.ofNat_ne_zero _, sub_eq_zero]

lemma equation_zero : V.Equation ![1, 1, 0] := by
  simp only [equation_of_Z_eq_zero, fin3_def_ext, one_pow]

lemma equation_some (X Y : R) : V.Equation ![X, Y, 1] ↔ V.toAffine.Equation X Y := by
  simp only [equation_iff, Affine.equation_iff', fin3_def_ext]
  congr! 1
  simp only [one_pow, mul_one]

lemma equation_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Equation P ↔ W.toAffine.Equation (P x / P z ^ 2) (P y / P z ^ 3) :=
  (equation_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| equation_some ..

end Equation

section Nonsingular

/-! ### Nonsingular Weierstrass equations -/

variable (V) in
/-- The partial derivative $W_X(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $X$. -/
noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  pderiv x V.polynomial

lemma polynomialX_eq : V.polynomialX =
    C V.a₁ * X 1 * X 2 - (C 3 * X 0 ^ 2 + C (2 * V.a₂) * X 0 * X 2 ^ 2 + C V.a₄ * X 2 ^ 4) := by
  rw [polynomialX, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialX (P : Fin 3 → R) : eval P V.polynomialX =
    V.a₁ * P y * P z - (3 * P x ^ 2 + 2 * V.a₂ * P x * P z ^ 2 + V.a₄ * P z ^ 4) := by
  rw [polynomialX_eq]
  eval_simp

lemma eval_polynomialX_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    eval P W.polynomialX / P z ^ 4 =
      (W.toAffine.polynomialX.eval <| Polynomial.C <| P y / P z ^ 3).eval (P x / P z ^ 2) := by
  linear_combination (norm := (rw [eval_polynomialX, Affine.eval_polynomialX]; ring1))
    W.a₁ * P y / P z ^ 3 * div_self hPz - 2 * W.a₂ * P x / P z ^ 2 * div_self (pow_ne_zero 2 hPz)
      - W.a₄ * div_self (pow_ne_zero 4 hPz)

variable (V) in
/-- The partial derivative $W_Y(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $Y$. -/
noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  pderiv y V.polynomial

lemma polynomialY_eq : V.polynomialY = C 2 * X 1 + C V.a₁ * X 0 * X 2 + C V.a₃ * X 2 ^ 3 := by
  rw [polynomialY, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialY (P : Fin 3 → R) :
    eval P V.polynomialY = 2 * P y + V.a₁ * P x * P z + V.a₃ * P z ^ 3 := by
  rw [polynomialY_eq]
  eval_simp

lemma eval_polynomialY_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    eval P W.polynomialY / P z ^ 3 =
      (W.toAffine.polynomialY.eval <| Polynomial.C <| P y / P z ^ 3).eval (P x / P z ^ 2) := by
  linear_combination (norm := (rw [eval_polynomialY, Affine.eval_polynomialY]; ring1))
    W.a₁ * P x / P z ^ 2 * div_self hPz + W.a₃ * div_self (pow_ne_zero 3 hPz)

variable (V) in
/-- The partial derivative $W_Z(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $Z$. -/
noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  pderiv z V.polynomial

lemma polynomialZ_eq : V.polynomialZ =
    C V.a₁ * X 0 * X 1 + C (3 * V.a₃) * X 1 * X 2 ^ 2
      - (C (2 * V.a₂) * X 0 ^ 2 * X 2 + C (4 * V.a₄) * X 0 * X 2 ^ 3 + C (6 * V.a₆) * X 2 ^ 5) := by
  rw [polynomialZ, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialZ (P : Fin 3 → R) : eval P V.polynomialZ =
    V.a₁ * P x * P y + 3 * V.a₃ * P y * P z ^ 2
      - (2 * V.a₂ * P x ^ 2 * P z + 4 * V.a₄ * P x * P z ^ 3 + 6 * V.a₆ * P z ^ 5) := by
  rw [polynomialZ_eq]
  eval_simp

variable (V) in
/-- The proposition that a point representative $(x, y, z)$ in `W` is nonsingular.
In other words, either $W_X(x, y, z) \ne 0$, $W_Y(x, y, z) \ne 0$, or $W_Z(x, y, z) \ne 0$. -/
def Nonsingular (P : Fin 3 → R) : Prop :=
  V.Equation P ∧ (eval P V.polynomialX ≠ 0 ∨ eval P V.polynomialY ≠ 0 ∨ eval P V.polynomialZ ≠ 0)

lemma nonsingular_iff (P : Fin 3 → R) : V.Nonsingular P ↔ V.Equation P ∧
    (V.a₁ * P y * P z - (3 * P x ^ 2 + 2 * V.a₂ * P x * P z ^ 2 + V.a₄ * P z ^ 4) ≠ 0 ∨
      2 * P y + V.a₁ * P x * P z + V.a₃ * P z ^ 3 ≠ 0 ∨
      V.a₁ * P x * P y + 3 * V.a₃ * P y * P z ^ 2
        - (2 * V.a₂ * P x ^ 2 * P z + 4 * V.a₄ * P x * P z ^ 3 + 6 * V.a₆ * P z ^ 5) ≠ 0) := by
  rw [Nonsingular, eval_polynomialX, eval_polynomialY, eval_polynomialZ]

lemma nonsingular_smul (P : Fin 3 → R) (u : Rˣ) : V.Nonsingular (u • P) ↔ V.Nonsingular P :=
  have (u : Rˣ) {P : Fin 3 → R} (hP : V.Nonsingular <| u • P) : V.Nonsingular P := by
    rcases (nonsingular_iff _).mp hP with ⟨h, h'⟩
    refine (nonsingular_iff P).mpr ⟨(equation_smul_iff P u).mp h, ?_⟩
    contrapose! h'
    simp only [smul_fin3_ext]
    exact ⟨by linear_combination (norm := ring1) u ^ 4 * h'.left,
      by linear_combination (norm := ring1) u ^ 3 * h'.right.left,
      by linear_combination (norm := ring1) u ^ 5 * h'.right.right⟩
  ⟨this u, fun h => this u⁻¹ <| by rwa [inv_smul_smul]⟩

lemma nonsingular_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : V.Nonsingular P ↔ V.Nonsingular Q := by
  rcases h with ⟨u, rfl⟩
  exact nonsingular_smul Q u

lemma nonsingular_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) :
    V.Nonsingular P ↔ V.Equation P ∧ (3 * P x ^ 2 ≠ 0 ∨ 2 * P y ≠ 0 ∨ V.a₁ * P x * P y ≠ 0) := by
  simp only [nonsingular_iff, hPz, add_zero, sub_zero, zero_sub, mul_zero,
    zero_pow <| OfNat.ofNat_ne_zero _, neg_ne_zero]

lemma nonsingular_zero [Nontrivial R] : V.Nonsingular ![1, 1, 0] := by
  simp only [nonsingular_of_Z_eq_zero, equation_zero, true_and, fin3_def_ext, ← not_and_or]
  exact fun h => one_ne_zero <| by linear_combination (norm := ring1) h.1 - h.2.1

lemma nonsingular_some (X Y : R) : V.Nonsingular ![X, Y, 1] ↔ V.toAffine.Nonsingular X Y := by
  simp_rw [nonsingular_iff, equation_some, fin3_def_ext, Affine.nonsingular_iff',
    Affine.equation_iff', and_congr_right_iff, ← not_and_or, not_iff_not, one_pow, mul_one,
    and_congr_right_iff, Iff.comm, iff_self_and]
  intro h hX hY
  linear_combination (norm := ring1) 6 * h - 2 * X * hX - 3 * Y * hY

lemma nonsingular_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.toAffine.Nonsingular (P x / P z ^ 2) (P y / P z ^ 3) :=
  (nonsingular_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| nonsingular_some ..

lemma nonsingular_iff_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.Equation P ∧ (eval P W.polynomialX ≠ 0 ∨ eval P W.polynomialY ≠ 0) := by
  rw [nonsingular_of_Z_ne_zero hPz, Affine.Nonsingular, ← equation_of_Z_ne_zero hPz,
    ← eval_polynomialX_of_Z_ne_zero hPz, div_ne_zero_iff, and_iff_left <| pow_ne_zero 4 hPz,
    ← eval_polynomialY_of_Z_ne_zero hPz, div_ne_zero_iff, and_iff_left <| pow_ne_zero 3 hPz]

lemma X_ne_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : V.Nonsingular P)
    (hPz : P z = 0) : P x ≠ 0 := by
  intro hPx
  simp only [nonsingular_of_Z_eq_zero hPz, equation_of_Z_eq_zero hPz, hPx, mul_zero, zero_mul,
    zero_pow <| OfNat.ofNat_ne_zero _, ne_self_iff_false, or_false, false_or] at hP
  rwa [pow_eq_zero_iff two_ne_zero, hP.left, eq_self, true_and, mul_zero, ne_self_iff_false] at hP

lemma Y_ne_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : V.Nonsingular P)
    (hPz : P z = 0) : P y ≠ 0 := by
  have hPx : P x ≠ 0 := X_ne_zero_of_Z_eq_zero hP hPz
  intro hPy
  rw [nonsingular_of_Z_eq_zero hPz, equation_of_Z_eq_zero hPz, hPy, zero_pow two_ne_zero] at hP
  exact hPx <| pow_eq_zero hP.left.symm

lemma equiv_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : P ≈ Q := by
  have hPx : P x ≠ 0 := X_ne_zero_of_Z_eq_zero hP hPz
  have hPy : P y ≠ 0 := Y_ne_zero_of_Z_eq_zero hP hPz
  have hQx : Q x ≠ 0 := X_ne_zero_of_Z_eq_zero hQ hQz
  have hQy : Q y ≠ 0 := Y_ne_zero_of_Z_eq_zero hQ hQz
  simp only [nonsingular_of_Z_eq_zero, equation_of_Z_eq_zero, hPz, hQz] at hP hQ
  use (Units.mk0 _ hPy / Units.mk0 _ hPx) * (Units.mk0 _ hQx / Units.mk0 _ hQy)
  simp only [smul_fin3, Units.val_mul, Units.val_div_eq_div_val, Units.val_mk0, mul_pow, hQz,
    mul_zero]
  conv_rhs => rw [← fin3_def P, hPz]
  congr! 2
  · rw [div_pow, hP.left, pow_succ, mul_div_cancel_left₀ _ <| pow_ne_zero 2 hPx, div_pow, hQ.left,
      pow_succ _ 2, div_mul_cancel_left₀ <| pow_ne_zero 2 hQx, inv_mul_cancel_right₀ hQx]
  · rw [div_pow, ← hP.left, pow_succ, mul_div_cancel_left₀ _ <| pow_ne_zero 2 hPy, div_pow,
      ← hQ.left, pow_succ _ 2, div_mul_cancel_left₀ <| pow_ne_zero 2 hQy, inv_mul_cancel_right₀ hQy]

lemma equiv_zero_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    P ≈ ![1, 1, 0] :=
  equiv_of_Z_eq_zero hP nonsingular_zero hPz rfl

variable (V) in
/-- The proposition that a point class on `W` is nonsingular. If `P` is a point representative,
then `V.NonsingularLift ⟦P⟧` is definitionally equivalent to `V.Nonsingular P`. -/
def NonsingularLift (P : PointClass R) : Prop :=
  P.lift V.Nonsingular fun _ _ => propext ∘ nonsingular_of_equiv

lemma nonsingularLift_iff (P : Fin 3 → R) : V.NonsingularLift ⟦P⟧ ↔ V.Nonsingular P :=
  Iff.rfl

lemma nonsingularLift_zero [Nontrivial R] : V.NonsingularLift ⟦![1, 1, 0]⟧ :=
  nonsingular_zero

lemma nonsingularLift_some (X Y : R) :
    V.NonsingularLift ⟦![X, Y, 1]⟧ ↔ V.toAffine.Nonsingular X Y :=
  nonsingular_some X Y

end Nonsingular

section Negation

/-! ### Negation formulae -/

variable (V) in
/-- The $Y$-coordinate of the negation of a point representative. -/
def negY (P : Fin 3 → R) : R :=
  -P y - V.a₁ * P x * P z - V.a₃ * P z ^ 3

lemma negY_smul (P : Fin 3 → R) (u : Rˣ) : V.negY (u • P) = u ^ 3 * V.negY P := by
  simp only [negY, smul_fin3_ext]
  ring1

lemma negY_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) : V.negY P = -P y := by
  simp only [negY, hPz, sub_zero, mul_zero, zero_pow three_ne_zero]

lemma negY_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.negY P / P z ^ 3 = W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3) := by
  linear_combination (norm := (rw [negY, Affine.negY]; ring1))
    -W.a₁ * P x / P z ^ 2 * div_self hPz - W.a₃ * div_self (pow_ne_zero 3 hPz)

lemma Y_sub_Y_mul_Y_sub_negY {P Q : Fin 3 → R} (hP : V.Equation P) (hQ : V.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    (P y * Q z ^ 3 - Q y * P z ^ 3) * (P y * Q z ^ 3 - V.negY Q * P z ^ 3) = 0 := by
  linear_combination (norm := (rw [negY]; ring1)) Q z ^ 6 * (equation_iff P).mp hP
    - P z ^ 6 * (equation_iff Q).mp hQ + hx * hx * hx + V.a₂ * P z ^ 2 * Q z ^ 2 * hx * hx
    + (V.a₄ * P z ^ 4 * Q z ^ 4 - V.a₁ * P y * P z * Q z ^ 4) * hx

lemma Y_eq_of_Y_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) :
    P y * Q z ^ 3 = W.negY Q * P z ^ 3 :=
  eq_of_sub_eq_zero <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_left <|
    sub_ne_zero_of_ne hy

lemma Y_eq_of_Y_ne' {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    P y * Q z ^ 3 = Q y * P z ^ 3 :=
  eq_of_sub_eq_zero <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_right <|
    sub_ne_zero_of_ne hy

lemma Y_sub_Y_add_Y_sub_negY (P Q : Fin 3 → R) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    (P y * Q z ^ 3 - Q y * P z ^ 3) + (P y * Q z ^ 3 - V.negY Q * P z ^ 3) =
      (P y - V.negY P) * Q z ^ 3 := by
  linear_combination (norm := (rw [negY, negY]; ring1)) -V.a₁ * P z * Q z * hx

lemma Y_ne_negY_iff (P : Fin 3 → R) : P y ≠ V.negY P ↔ eval P V.polynomialY ≠ 0 := by
  rw [← sub_ne_zero, negY, eval_polynomialY]
  congr! 1
  ring1

lemma Y_ne_negY_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : V.Equation P) (hQ : V.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) : P y ≠ V.negY P := by
  have hy' : P y * Q z ^ 3 - V.negY Q * P z ^ 3 = 0 :=
    (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_left <| sub_ne_zero_of_ne hy
  contrapose! hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY P Q hx + Q z ^ 3 * hy - hy'

lemma Y_ne_negY_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : V.Equation P)
    (hQ : V.Equation Q) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 ≠ V.negY Q * P z ^ 3) : P y ≠ V.negY P := by
  have hy' : P y * Q z ^ 3 - Q y * P z ^ 3 = 0 :=
    (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_right <| sub_ne_zero_of_ne hy
  contrapose! hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY P Q hx + Q z ^ 3 * hy - hy'

lemma Y_eq_negY_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = V.negY Q * P z ^ 3) : P y = V.negY P :=
  mul_left_injective₀ (pow_ne_zero 3 hQz) <| by
    linear_combination (norm := ring1) -Y_sub_Y_add_Y_sub_negY P Q hx + hy + hy'

lemma nonsingular_iff_of_Y_eq_negY {P : Fin 3 → F} (hPy : P y = W.negY P) (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.Equation P ∧ eval P W.polynomialX ≠ 0 := by
  rw [nonsingular_iff_of_Z_ne_zero hPz, ← Y_ne_negY_iff, hPy, ne_self_iff_false, or_false]

end Negation

section Doubling

/-! ### Doubling formulae -/

variable (V) in
/-- The $Z$-coordinate of the doubling of a point representative. -/
def dblZ (P : Fin 3 → R) : R :=
  P z * (P y - V.negY P)

lemma dblZ_smul (P : Fin 3 → R) (u : Rˣ) : V.dblZ (u • P) = u ^ 4 * V.dblZ P := by
  simp only [dblZ, negY_smul, smul_fin3_ext]
  ring1

lemma dblZ_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) : V.dblZ P = 0 := by
  rw [dblZ, hPz, zero_mul]

lemma dblZ_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = V.negY Q * P z ^ 3) : V.dblZ P = 0 := by
  rw [dblZ, Y_eq_negY_of_Y_eq hQz hx hy hy', sub_self, mul_zero]

lemma dblZ_ne_zero_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : V.Equation P)
    (hQ : V.Equation Q) (hPz : P z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) : V.dblZ P ≠ 0 :=
  mul_ne_zero hPz <| sub_ne_zero_of_ne <| Y_ne_negY_of_Y_ne hP hQ hx hy

lemma dblZ_ne_zero_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : V.Equation P)
    (hQ : V.Equation Q) (hPz : P z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 ≠ V.negY Q * P z ^ 3) : V.dblZ P ≠ 0 :=
  mul_ne_zero hPz <| sub_ne_zero_of_ne <| Y_ne_negY_of_Y_ne' hP hQ hx hy

private lemma toAffine_slope_of_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3) =
      (3 * P x ^ 2 + 2 * W.a₂ * P x * P z ^ 2 + W.a₄ * P z ^ 4 - W.a₁ * P y * P z) / W.dblZ P := by
  have hPy : P y - W.negY P ≠ 0 := sub_ne_zero_of_ne <| Y_ne_negY_of_Y_ne' hP hQ hx hy
  simp only [mul_comm <| P z ^ _, ne_eq, ← div_eq_div_iff (pow_ne_zero _ hPz) (pow_ne_zero _ hQz)]
    at hx hy
  rw [Affine.slope_of_Yne hx <| negY_of_Z_ne_zero hQz ▸ hy, ← negY_of_Z_ne_zero hPz, dblZ]
  field_simp [pow_ne_zero 2 hPz]
  ring1

variable (V) in
/-- The $X$-coordinate of the doubling of a point representative. -/
def dblX (P : Fin 3 → R) : R :=
  (3 * P x ^ 2 + 2 * V.a₂ * P x * P z ^ 2 + V.a₄ * P z ^ 4 - V.a₁ * P y * P z) ^ 2
    + V.a₁ * (3 * P x ^ 2 + 2 * V.a₂ * P x * P z ^ 2 + V.a₄ * P z ^ 4 - V.a₁ * P y * P z) * P z
      * (P y - V.negY P) - V.a₂ * P z ^ 2 * (P y - V.negY P) ^ 2 - 2 * P x * (P y - V.negY P) ^ 2

lemma dblX_smul (P : Fin 3 → R) (u : Rˣ) : V.dblX (u • P) = (u ^ 4) ^ 2 * V.dblX P := by
  simp only [dblX, negY_smul, smul_fin3_ext]
  ring1

lemma dblX_of_Z_eq_zero {P : Fin 3 → R} (hP : V.Equation P) (hPz : P z = 0) :
    V.dblX P = (P x ^ 2) ^ 2 := by
  linear_combination (norm := (rw [dblX, negY_of_Z_eq_zero hPz, hPz]; ring1))
    -8 * P x * (equation_of_Z_eq_zero hPz).mp hP

lemma dblX_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = V.negY Q * P z ^ 3) : V.dblX P = eval P V.polynomialX ^ 2 := by
  rw [dblX, eval_polynomialX, Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

private lemma toAffine_addX_of_eq {P : Fin 3 → F} {n d : F} (hPz : P z ≠ 0) (hd : d ≠ 0) :
    W.toAffine.addX (P x / P z ^ 2) (P x / P z ^ 2) (n / (P z * d)) =
      (n ^ 2 + W.a₁ * n * P z * d - W.a₂ * P z ^ 2 * d ^ 2 - 2 * P x * d ^ 2) / (P z * d) ^ 2 := by
  field_simp [mul_ne_zero hPz hd]
  ring1

lemma dblX_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.dblX P / W.dblZ P ^ 2 = W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [dblX, toAffine_slope_of_eq hP hQ hPz hQz hx hy, dblZ,
    ← (div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz)).mpr hx,
    toAffine_addX_of_eq hPz <| sub_ne_zero_of_ne <| Y_ne_negY_of_Y_ne' hP hQ hx hy]

variable (V) in
/-- The $Y$-coordinate of the doubling of a point representative, before applying the final negation
that maps $Y$ to $-Y - a_1XZ - a_3Z^3$. -/
def dblY' (P : Fin 3 → R) : R :=
  (3 * P x ^ 2 + 2 * V.a₂ * P x * P z ^ 2 + V.a₄ * P z ^ 4 - V.a₁ * P y * P z)
      * (V.dblX P - P x * (P y - V.negY P) ^ 2) + P y * (P y - V.negY P) ^ 3

lemma dblY'_smul (P : Fin 3 → R) (u : Rˣ) : V.dblY' (u • P) = (u ^ 4) ^ 3 * V.dblY' P := by
  simp only [dblY', dblX_smul, negY_smul, smul_fin3_ext]
  ring1

lemma dblY'_of_Z_eq_zero {P : Fin 3 → R} (hP : V.Equation P) (hPz : P z = 0) :
    V.dblY' P = -(P x ^ 2) ^ 3 := by
  linear_combination
    (norm := (rw [dblY', dblX_of_Z_eq_zero hP hPz, negY_of_Z_eq_zero hPz, hPz]; ring1))
    (8 * (equation_of_Z_eq_zero hPz).mp hP - 12 * P x ^ 3) * (equation_of_Z_eq_zero hPz).mp hP

lemma dblY'_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = V.negY Q * P z ^ 3) : V.dblY' P = (-eval P V.polynomialX) ^ 3 := by
  rw [dblY', dblX_of_Y_eq hQz hx hy hy', eval_polynomialX, Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

private lemma toAffine_addY'_of_eq {P : Fin 3 → F} {n d : F} (hPz : P z ≠ 0) (hd : d ≠ 0) :
    W.toAffine.addY' (P x / P z ^ 2) (P x / P z ^ 2) (P y / P z ^ 3) (n / (P z * d)) =
      (n * (n ^ 2 + W.a₁ * n * P z * d - W.a₂ * P z ^ 2 * d ^ 2 - 2 * P x * d ^ 2 - P x * d ^ 2)
        + P y * d ^ 3) / (P z * d) ^ 3 := by
  linear_combination (norm := (rw [Affine.addY', toAffine_addX_of_eq hPz hd]; ring1))
    n * P x / (P z ^ 3 * d) * div_self (pow_ne_zero 2 hd)
      - P y / P z ^ 3 * div_self (pow_ne_zero 3 hd)

lemma dblY'_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) : W.dblY' P / W.dblZ P ^ 3 =
    W.toAffine.addY' (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [dblY', dblX, toAffine_slope_of_eq hP hQ hPz hQz hx hy, dblZ,
    ← (div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz)).mpr hx,
    toAffine_addY'_of_eq hPz <| sub_ne_zero_of_ne <| Y_ne_negY_of_Y_ne' hP hQ hx hy]

variable (V) in
/-- The $Y$-coordinate of the doubling of a point representative. -/
def dblY (P : Fin 3 → R) : R :=
  V.negY ![V.dblX P, V.dblY' P, V.dblZ P]

lemma dblY_smul (P : Fin 3 → R) (u : Rˣ) : V.dblY (u • P) = (u ^ 4) ^ 3 * V.dblY P := by
  simp only [dblY, negY, dblX_smul, dblY'_smul, dblZ_smul, fin3_def_ext]
  ring1

lemma dblY_of_Z_eq_zero {P : Fin 3 → R} (hP : V.Equation P) (hPz : P z = 0) :
    V.dblY P = (P x ^ 2) ^ 3 := by
  erw [dblY, dblY'_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz, negY_of_Z_eq_zero rfl, neg_neg]

lemma dblY_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = V.negY Q * P z ^ 3) : V.dblY P = eval P V.polynomialX ^ 3 := by
  erw [dblY, dblZ_of_Y_eq hQz hx hy hy', negY_of_Z_eq_zero rfl, dblY'_of_Y_eq hQz hx hy hy',
    ← Odd.neg_pow <| by decide, neg_neg]

lemma dblY_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.dblY P / W.dblZ P ^ 3 = W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  erw [dblY, negY_of_Z_ne_zero <| dblZ_ne_zero_of_Y_ne' hP hQ hPz hx hy,
    dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, dblY'_of_Z_ne_zero hP hQ hPz hQz hx hy, Affine.addY]

end Doubling

section Addition

/-! ### Addition formulae -/

/-- The $Z$-coordinate of the addition of two distinct point representatives. -/
def addZ (P Q : Fin 3 → R) : R :=
  P x * Q z ^ 2 - Q x * P z ^ 2

lemma addZ_smul (P Q : Fin 3 → R) (u v : Rˣ) : addZ (u • P) (v • Q) = (u * v) ^ 2 * addZ P Q := by
  simp only [addZ, smul_fin3_ext]
  ring1

lemma addZ_of_Z_eq_zero_left {P Q : Fin 3 → R} (hPz : P z = 0) : addZ P Q = P x * Q z * Q z := by
  rw [addZ, hPz]
  ring1

lemma addZ_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQz : Q z = 0) :
    addZ P Q = -(Q x * P z) * P z := by
  rw [addZ, hQz]
  ring1

lemma addZ_of_X_eq {P Q : Fin 3 → R} (hx : P x * Q z ^ 2 = Q x * P z ^ 2) : addZ P Q = 0 := by
  rw [addZ, hx, sub_self]

lemma addZ_ne_zero_of_X_ne {P Q : Fin 3 → R} (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : addZ P Q ≠ 0 :=
  sub_ne_zero_of_ne hx

private lemma toAffine_slope_of_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) :
    W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3) =
      (P y * Q z ^ 3 - Q y * P z ^ 3) / (P z * Q z * addZ P Q) := by
  rw [Affine.slope_of_Xne <| by rwa [ne_eq, div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz)],
    div_sub_div _ _ (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz), mul_comm <| _ ^ 2, addZ]
  field_simp [mul_ne_zero (mul_ne_zero hPz hQz) <| sub_ne_zero_of_ne hx,
    mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hPz) (pow_ne_zero 3 hQz)) <| sub_ne_zero_of_ne hx]
  ring1

variable (V) in
/-- The $X$-coordinate of the addition of two distinct point representatives. -/
def addX (P Q : Fin 3 → R) : R :=
  P x * Q x ^ 2 * P z ^ 2 - 2 * P y * Q y * P z * Q z + P x ^ 2 * Q x * Q z ^ 2
    - V.a₁ * P x * Q y * P z ^ 2 * Q z - V.a₁ * P y * Q x * P z * Q z ^ 2
    + 2 * V.a₂ * P x * Q x * P z ^ 2 * Q z ^ 2 - V.a₃ * Q y * P z ^ 4 * Q z
    - V.a₃ * P y * P z * Q z ^ 4 + V.a₄ * Q x * P z ^ 4 * Q z ^ 2 + V.a₄ * P x * P z ^ 2 * Q z ^ 4
    + 2 * V.a₆ * P z ^ 4 * Q z ^ 4

lemma addX_eq' {P Q : Fin 3 → R} (hP : V.Equation P) (hQ : V.Equation Q) :
    V.addX P Q * (P z * Q z) ^ 2 =
      (P y * Q z ^ 3 - Q y * P z ^ 3) ^ 2
        + V.a₁ * (P y * Q z ^ 3 - Q y * P z ^ 3) * P z * Q z * addZ P Q
        - V.a₂ * P z ^ 2 * Q z ^ 2 * addZ P Q ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2
        - Q x * P z ^ 2 * addZ P Q ^ 2 := by
  linear_combination (norm := (rw [addX, addZ]; ring1)) -Q z ^ 6 * (equation_iff P).mp hP
    - P z ^ 6 * (equation_iff Q).mp hQ

lemma addX_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) : W.addX P Q =
      ((P y * Q z ^ 3 - Q y * P z ^ 3) ^ 2
        + W.a₁ * (P y * Q z ^ 3 - Q y * P z ^ 3) * P z * Q z * addZ P Q
        - W.a₂ * P z ^ 2 * Q z ^ 2 * addZ P Q ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2
        - Q x * P z ^ 2 * addZ P Q ^ 2) / (P z * Q z) ^ 2 := by
  rw [← addX_eq' hP hQ, mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

lemma addX_smul (P Q : Fin 3 → R) (u v : Rˣ) :
    V.addX (u • P) (v • Q) = ((u * v) ^ 2) ^ 2 * V.addX P Q := by
  simp only [addX, smul_fin3_ext]
  ring1

lemma addX_of_Z_eq_zero_left {P Q : Fin 3 → R} (hPz : P z = 0) :
    V.addX P Q = (P x * Q z) ^ 2 * Q x := by
  rw [addX, hPz]
  ring1

lemma addX_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQz : Q z = 0) :
    V.addX P Q = (-(Q x * P z)) ^ 2 * P x := by
  rw [addX, hQz]
  ring1

lemma addX_of_X_eq' {P Q : Fin 3 → R} (hP : V.Equation P) (hQ : V.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    V.addX P Q * (P z * Q z) ^ 2 = (P y * Q z ^ 3 - Q y * P z ^ 3) ^ 2 := by
  simp only [addX_eq' hP hQ, addZ_of_X_eq hx, add_zero, sub_zero, mul_zero, zero_pow two_ne_zero]

lemma addX_of_X_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W.addX P Q = (-((P y * Q z ^ 3 - Q y * P z ^ 3) / (P z * Q z))) ^ 2 := by
  rw [neg_sq, div_pow, ← addX_of_X_eq' hP hQ hx,
    mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

private lemma toAffine_addX_of_ne {P Q : Fin 3 → F} {n d : F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hd : d ≠ 0) : W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2) (n / (P z * Q z * d)) =
      (n ^ 2 + W.a₁ * n * P z * Q z * d - W.a₂ * P z ^ 2 * Q z ^ 2 * d ^ 2 - P x * Q z ^ 2 * d ^ 2
        - Q x * P z ^ 2 * d ^ 2) / (P z * Q z * d) ^ 2 := by
  field_simp [mul_ne_zero (mul_ne_zero hPz hQz) hd]
  ring1

lemma addX_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) :
    W.addX P Q / addZ P Q ^ 2 = W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [addX_eq hP hQ hPz hQz, div_div, ← mul_pow, toAffine_slope_of_ne hPz hQz hx,
    toAffine_addX_of_ne hPz hQz <| addZ_ne_zero_of_X_ne hx]

variable (V) in
/-- The $Y$-coordinate of the addition of two distinct point representatives, before applying the
final negation that maps $Y$ to $-Y - a_1XZ - a_3Z^3$. -/
def addY' (P Q : Fin 3 → R) : R :=
  -P y * Q x ^ 3 * P z ^ 3 + 2 * P y * Q y ^ 2 * P z ^ 3 - 3 * P x ^ 2 * Q x * Q y * P z ^ 2 * Q z
    + 3 * P x * P y * Q x ^ 2 * P z * Q z ^ 2 + P x ^ 3 * Q y * Q z ^ 3
    - 2 * P y ^ 2 * Q y * Q z ^ 3 + V.a₁ * P x * Q y ^ 2 * P z ^ 4
    + V.a₁ * P y * Q x * Q y * P z ^ 3 * Q z - V.a₁ * P x * P y * Q y * P z * Q z ^ 3
    - V.a₁ * P y ^ 2 * Q x * Q z ^ 4 - 2 * V.a₂ * P x * Q x * Q y * P z ^ 4 * Q z
    + 2 * V.a₂ * P x * P y * Q x * P z * Q z ^ 4 + V.a₃ * Q y ^ 2 * P z ^ 6
    - V.a₃ * P y ^ 2 * Q z ^ 6 - V.a₄ * Q x * Q y * P z ^ 6 * Q z
    - V.a₄ * P x * Q y * P z ^ 4 * Q z ^ 3 + V.a₄ * P y * Q x * P z ^ 3 * Q z ^ 4
    + V.a₄ * P x * P y * P z * Q z ^ 6 - 2 * V.a₆ * Q y * P z ^ 6 * Q z ^ 3
    + 2 * V.a₆ * P y * P z ^ 3 * Q z ^ 6

lemma addY'_eq' {P Q : Fin 3 → R} : V.addY' P Q * (P z * Q z) ^ 3 =
    (P y * Q z ^ 3 - Q y * P z ^ 3) * (V.addX P Q * (P z * Q z) ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2)
      + P y * Q z ^ 3 * addZ P Q ^ 3 := by
  rw [addY', addX, addZ]
  ring1

lemma addY'_eq {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) : W.addY' P Q =
    ((P y * Q z ^ 3 - Q y * P z ^ 3) * (W.addX P Q * (P z * Q z) ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2)
      + P y * Q z ^ 3 * addZ P Q ^ 3) / (P z * Q z) ^ 3 := by
  rw [← addY'_eq', mul_div_cancel_right₀ _ <| pow_ne_zero 3 <| mul_ne_zero hPz hQz]

lemma addY'_smul (P Q : Fin 3 → R) (u v : Rˣ) :
    V.addY' (u • P) (v • Q) = ((u * v) ^ 2) ^ 3 * V.addY' P Q := by
  simp only [addY', smul_fin3_ext]
  ring1

lemma addY'_of_Z_eq_zero_left {P Q : Fin 3 → R} (hP : V.Equation P) (hPz : P z = 0) :
    V.addY' P Q = (P x * Q z) ^ 3 * V.negY Q := by
  linear_combination (norm := (rw [addY', negY, hPz]; ring1))
    (V.negY Q - Q y) * Q z ^ 3 * (equation_of_Z_eq_zero hPz).mp hP

lemma addY'_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQ : V.Equation Q) (hQz : Q z = 0) :
    V.addY' P Q = (-(Q x * P z)) ^ 3 * V.negY P := by
  linear_combination (norm := (rw [addY', negY, hQz]; ring1))
    (P y - V.negY P) * P z ^ 3 * (equation_of_Z_eq_zero hQz).mp hQ

lemma addY'_of_X_eq' {P Q : Fin 3 → R} (hP : V.Equation P) (hQ : V.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    V.addY' P Q * (P z * Q z) ^ 3 = (P y * Q z ^ 3 - Q y * P z ^ 3) ^ 3 := by
  simp only [addY'_eq', addX_eq' hP hQ, addZ_of_X_eq hx, add_zero, sub_zero, mul_zero,
    zero_pow <| OfNat.ofNat_ne_zero _, ← pow_succ']

lemma addY'_of_X_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W.addY' P Q = ((P y * Q z ^ 3 - Q y * P z ^ 3) / (P z * Q z)) ^ 3 := by
  rw [div_pow, ← addY'_of_X_eq' hP hQ hx,
    mul_div_cancel_right₀ _ <| pow_ne_zero 3 <| mul_ne_zero hPz hQz]

private lemma toAffine_addY'_of_ne {P Q : Fin 3 → F} {n d : F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hd : d ≠ 0) :
    W.toAffine.addY' (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (n / (P z * Q z * d)) =
      (n * (n ^ 2 + W.a₁ * n * P z * Q z * d - W.a₂ * P z ^ 2 * Q z ^ 2 * d ^ 2
          - P x * Q z ^ 2 * d ^ 2 - Q x * P z ^ 2 * d ^ 2 - P x * Q z ^ 2 * d ^ 2)
        + P y * Q z ^ 3 * d ^ 3) / (P z * Q z * d) ^ 3 := by
  linear_combination (norm := (rw [Affine.addY', toAffine_addX_of_ne hPz hQz hd]; ring1))
    n * P x / (P z ^ 3 * Q z * d) * div_self (pow_ne_zero 2 <| mul_ne_zero hQz hd)
      - P y / P z ^ 3 * div_self (pow_ne_zero 3 <| mul_ne_zero hQz hd)

lemma addY'_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) :
    W.addY' P Q / addZ P Q ^ 3 = W.toAffine.addY' (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [addY'_eq hPz hQz, addX_eq' hP hQ, div_div, ← mul_pow _ _ 3, toAffine_slope_of_ne hPz hQz hx,
    toAffine_addY'_of_ne hPz hQz <| addZ_ne_zero_of_X_ne hx]

variable (V) in
/-- The $Y$-coordinate of the addition of two distinct point representatives. -/
def addY (P Q : Fin 3 → R) : R :=
  V.negY ![V.addX P Q, V.addY' P Q, addZ P Q]

lemma addY_smul (P Q : Fin 3 → R) (u v : Rˣ) :
    V.addY (u • P) (v • Q) = ((u * v) ^ 2) ^ 3 * V.addY P Q := by
  simp only [addY, negY, addX_smul, addY'_smul, addZ_smul, fin3_def_ext]
  ring1

lemma addY_of_Z_eq_zero_left {P Q : Fin 3 → R} (hP : V.Equation P) (hPz : P z = 0) :
    V.addY P Q = (P x * Q z) ^ 3 * Q y := by
  simp only [addY, addX_of_Z_eq_zero_left hPz, addY'_of_Z_eq_zero_left hP hPz,
    addZ_of_Z_eq_zero_left hPz, negY, fin3_def_ext]
  ring1

lemma addY_of_Z_eq_zero_right {P Q : Fin 3 → R} (hQ : V.Equation Q) (hQz : Q z = 0) :
    V.addY P Q = (-(Q x * P z)) ^ 3 * P y := by
  simp only [addY, addX_of_Z_eq_zero_right hQz, addY'_of_Z_eq_zero_right hQ hQz,
    addZ_of_Z_eq_zero_right hQz, negY, fin3_def_ext]
  ring1

lemma addY_of_X_eq' {P Q : Fin 3 → R} (hP : V.Equation P) (hQ : V.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    V.addY P Q * (P z * Q z) ^ 3 = -(P y * Q z ^ 3 - Q y * P z ^ 3) ^ 3 := by
  erw [addY, negY, addZ_of_X_eq hx, mul_zero, sub_zero, zero_pow three_ne_zero, mul_zero, sub_zero,
    neg_mul, addY'_of_X_eq' hP hQ hx]

lemma addY_of_X_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W.addY P Q = (-((P y * Q z ^ 3 - Q y * P z ^ 3) / (P z * Q z))) ^ 3 := by
  erw [addY, addZ_of_X_eq hx, negY_of_Z_eq_zero rfl, addY'_of_X_eq hP hQ hPz hQz hx,
    ← Odd.neg_pow <| by decide]

lemma addY_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) :
    W.addY P Q / addZ P Q ^ 3 = W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  erw [addY, negY_of_Z_ne_zero <| addZ_ne_zero_of_X_ne hx, addX_of_Z_ne_zero hP hQ hPz hQz hx,
    addY'_of_Z_ne_zero hP hQ hPz hQz hx, Affine.addY]

end Addition

section Negation

/-! ### Negation on point representatives -/

variable (V) in
/-- The negation of a point representative. -/
def neg (P : Fin 3 → R) : Fin 3 → R :=
  ![P x, V.negY P, P z]

lemma neg_smul_equiv (P : Fin 3 → R) (u : Rˣ) : V.neg (u • P) ≈ V.neg P :=
  ⟨u, by simp only [neg, negY_smul, smul_fin3_ext]; rfl⟩

lemma neg_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : V.neg P ≈ V.neg Q := by
  rcases h with ⟨u, rfl⟩
  exact neg_smul_equiv Q u

lemma neg_of_Z_eq_zero' {P : Fin 3 → R} (hPz : P z = 0) : V.neg P = ![P x, -P y, 0] := by
  rw [neg, negY_of_Z_eq_zero hPz, hPz]

lemma neg_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) : W.neg P =
    -(Units.mk0 _ (Y_ne_zero_of_Z_eq_zero hP hPz) / Units.mk0 _ (X_ne_zero_of_Z_eq_zero hP hPz))
      • ![1, 1, 0] := by
  have hX {n : ℕ} : P x ^ n ≠ 0 := pow_ne_zero n <| X_ne_zero_of_Z_eq_zero hP hPz
  erw [neg_of_Z_eq_zero' hPz, smul_fin3, Units.val_neg, Units.val_div_eq_div_val, neg_sq, div_pow,
    (equation_of_Z_eq_zero hPz).mp hP.left, pow_succ, mul_div_cancel_left₀ _ hX, mul_one,
    Odd.neg_pow <| by decide, div_pow, pow_succ, (equation_of_Z_eq_zero hPz).mp hP.left,
    mul_div_cancel_left₀ _ hX, Units.val_mk0, mul_one, mul_zero]

lemma neg_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) : W.neg P =
    Units.mk0 _ hPz • ![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1] := by
  erw [neg, smul_fin3, mul_div_cancel₀ _ <| pow_ne_zero 2 hPz, ← negY_of_Z_ne_zero hPz,
    mul_div_cancel₀ _ <| pow_ne_zero 3 hPz, Units.val_mk0, mul_one]

private lemma nonsingular_neg_of_Z_ne_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) :
    W.Nonsingular ![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1] := by
  exact (nonsingular_some ..).mpr <| Affine.nonsingular_neg <| (nonsingular_of_Z_ne_zero hPz).mp hP

lemma nonsingular_neg {P : Fin 3 → F} (hP : W.Nonsingular P) : W.Nonsingular <| W.neg P := by
  by_cases hPz : P z = 0
  · simp only [neg_of_Z_eq_zero hP hPz, nonsingular_smul, nonsingular_zero]
  · simp only [neg_of_Z_ne_zero hPz, nonsingular_smul, nonsingular_neg_of_Z_ne_zero hP hPz]

variable (V) in
/-- The negation of a point class. If `P` is a point representative,
then `V.negMap ⟦P⟧` is definitionally equivalent to `V.neg P`. -/
def negMap (P : PointClass R) : PointClass R :=
  P.map V.neg fun _ _ => neg_equiv

lemma negMap_eq {P : Fin 3 → R} : V.negMap ⟦P⟧ = ⟦V.neg P⟧ :=
  rfl

lemma negMap_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.negMap ⟦P⟧ = ⟦![1, 1, 0]⟧ := by
  rw [negMap_eq, neg_of_Z_eq_zero hP hPz, smul_eq]

lemma negMap_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.negMap ⟦P⟧ = ⟦![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1]⟧ := by
  rw [negMap_eq, neg_of_Z_ne_zero hPz, smul_eq]

lemma nonsingularLift_negMap {P : PointClass F} (hP : W.NonsingularLift P) :
    W.NonsingularLift <| W.negMap P := by
  rcases P with ⟨_⟩
  exact nonsingular_neg hP

end Negation

section Addition

/-! ### Addition on point representatives -/

open scoped Classical

variable (V) in
/-- The addition of two point representatives. -/
noncomputable def add (P Q : Fin 3 → R) : Fin 3 → R :=
  if P ≈ Q then ![V.dblX P, V.dblY P, V.dblZ P] else ![V.addX P Q, V.addY P Q, addZ P Q]

lemma add_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : V.add P Q = ![V.dblX P, V.dblY P, V.dblZ P] :=
  if_pos h

lemma add_self (P : Fin 3 → R) : V.add P P = ![V.dblX P, V.dblY P, V.dblZ P] :=
  add_of_equiv <| Setoid.refl _

lemma add_of_eq {P Q : Fin 3 → R} (h : P = Q) : V.add P Q = ![V.dblX P, V.dblY P, V.dblZ P] :=
  h ▸ add_self P

lemma add_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) :
    V.add P Q = ![V.addX P Q, V.addY P Q, addZ P Q] :=
  if_neg h

lemma add_smul_equiv (P Q : Fin 3 → R) (u v : Rˣ) : V.add (u • P) (v • Q) ≈ V.add P Q := by
  have smul : P ≈ Q ↔ u • P ≈ v • Q := by erw [← Quotient.eq, ← Quotient.eq, smul_eq, smul_eq]; rfl
  by_cases h : P ≈ Q
  · exact ⟨u ^ 4, by simp only [add_of_equiv <| smul.mp h, dblX_smul, dblY_smul, dblZ_smul,
      add_of_equiv h]; rfl⟩
  · exact ⟨(u * v) ^ 2, by simp only [add_of_not_equiv <| h.comp smul.mpr, addX_smul, addY_smul,
      addZ_smul, add_of_not_equiv h]; rfl⟩

lemma add_equiv {P P' Q Q' : Fin 3 → R} (hP : P ≈ P') (hQ : Q ≈ Q') : V.add P Q ≈ V.add P' Q' := by
  rcases hP, hQ with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  exact add_smul_equiv P' Q' u v

lemma add_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) :
    W.add P Q = Units.mk0 _ (X_ne_zero_of_Z_eq_zero hP hPz) ^ 2 • ![1, 1, 0] := by
  erw [add, if_pos <| equiv_of_Z_eq_zero hP hQ hPz hQz, dblX_of_Z_eq_zero hP.left hPz,
    dblY_of_Z_eq_zero hP.left hPz, dblZ_of_Z_eq_zero hPz, smul_fin3, Units.val_pow_eq_pow_val,
    Units.val_mk0, mul_one, mul_one, mul_zero]

lemma add_of_Z_eq_zero_left' {P Q : Fin 3 → R} (hP : V.Equation P) (hPz : P z = 0) (hQz : Q z ≠ 0) :
    V.add P Q = ![(P x * Q z) ^ 2 * Q x, (P x * Q z) ^ 3 * Q y, P x * Q z * Q z] := by
  rw [add, if_neg <| not_equiv_of_Z_eq_zero_left hPz hQz, addX_of_Z_eq_zero_left hPz,
    addY_of_Z_eq_zero_left hP hPz, addZ_of_Z_eq_zero_left hPz]

lemma add_of_Z_eq_zero_left {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0)
    (hQz : Q z ≠ 0) :
    W.add P Q = (Units.mk0 _ (X_ne_zero_of_Z_eq_zero hP hPz) * Units.mk0 _ hQz) • Q :=
  add_of_Z_eq_zero_left' hP.left hPz hQz

lemma add_of_Z_eq_zero_right' {P Q : Fin 3 → R} (hQ : V.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z = 0) :
    V.add P Q = ![(-(Q x * P z)) ^ 2 * P x, (-(Q x * P z)) ^ 3 * P y, -(Q x * P z) * P z] := by
  rw [add, if_neg <| not_equiv_of_Z_eq_zero_right hPz hQz, addX_of_Z_eq_zero_right hQz,
    addY_of_Z_eq_zero_right hQ hQz, addZ_of_Z_eq_zero_right hQz]

lemma add_of_Z_eq_zero_right {P Q : Fin 3 → F} (hQ : W.Nonsingular Q) (hPz : P z ≠ 0)
    (hQz : Q z = 0) :
    W.add P Q = -(Units.mk0 _ (X_ne_zero_of_Z_eq_zero hQ hQz) * Units.mk0 _ hPz) • P :=
  add_of_Z_eq_zero_right' hQ.left hPz hQz

lemma add_of_Y_eq {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3) : W.add P Q =
      Units.mk0 _ ((nonsingular_iff_of_Y_eq_negY (Y_eq_negY_of_Y_eq hQz hx hy hy') hPz).mp hP).right
        • ![1, 1, 0] := by
  erw [add, if_pos <| equiv_of_X_eq_of_Y_eq hPz hQz hx hy, dblX_of_Y_eq hQz hx hy hy',
    dblY_of_Y_eq hQz hx hy hy', dblZ_of_Y_eq hQz hx hy hy', smul_fin3, Units.val_mk0, mul_one,
    mul_one, mul_zero]

lemma add_of_Y_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) :
    W.add P Q =
      -(Units.mk0 _ (sub_ne_zero_of_ne hy) / (Units.mk0 _ hPz * Units.mk0 _ hQz)) • ![1, 1, 0] := by
  erw [add, if_neg <| not_equiv_of_Y_ne hy, addX_of_X_eq hP hQ hPz hQz hx,
    addY_of_X_eq hP hQ hPz hQz hx, addZ_of_X_eq hx, smul_fin3, Units.val_neg,
    Units.val_div_eq_div_val, Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_mk0, mul_one,
    mul_one, mul_zero]

lemma add_of_Y_ne' {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.add P Q = Units.mk0 _ (dblZ_ne_zero_of_Y_ne' hP hQ hPz hx hy) •
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] := by
  have hZ {n : ℕ} : W.dblZ P ^ n ≠ 0 := pow_ne_zero n <| dblZ_ne_zero_of_Y_ne' hP hQ hPz hx hy
  erw [add, if_pos <| equiv_of_X_eq_of_Y_eq hPz hQz hx <| Y_eq_of_Y_ne' hP hQ hx hy, smul_fin3,
    Units.val_mk0, ← dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, mul_div_cancel₀ _ hZ,
    ← dblY_of_Z_ne_zero hP hQ hPz hQz hx hy, mul_div_cancel₀ _ hZ, mul_one]

lemma add_of_X_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) :
    W.add P Q = Units.mk0 _ (addZ_ne_zero_of_X_ne hx) •
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] := by
  have hZ {n : ℕ} : addZ P Q ^ n ≠ 0 := pow_ne_zero n <| addZ_ne_zero_of_X_ne hx
  erw [add, if_neg <| not_equiv_of_X_ne hx, smul_fin3, Units.val_mk0,
    ← addX_of_Z_ne_zero hP hQ hPz hQz hx, mul_div_cancel₀ _ hZ,
    ← addY_of_Z_ne_zero hP hQ hPz hQz hx, mul_div_cancel₀ _ hZ, mul_one]

private lemma nonsingular_add_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hxy : P x * Q z ^ 2 = Q x * P z ^ 2 → P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) : W.Nonsingular
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)), 1] :=
  (nonsingular_some ..).mpr <| Affine.nonsingular_add ((nonsingular_of_Z_ne_zero hPz).mp hP)
    ((nonsingular_of_Z_ne_zero hQz).mp hQ) <| by
      simpa only [div_eq_div_iff (pow_ne_zero _ hPz) (pow_ne_zero _ hQz), ne_eq,
        ← negY_of_Z_ne_zero hQz]

lemma nonsingular_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.Nonsingular <| W.add P Q := by
  by_cases hPz : P z = 0
  · by_cases hQz : Q z = 0
    · simp only [add_of_Z_eq_zero hP hQ hPz hQz, nonsingular_smul, nonsingular_zero]
    · simp only [add_of_Z_eq_zero_left hP hPz hQz, nonsingular_smul, hQ]
  · by_cases hQz : Q z = 0
    · simp only [add_of_Z_eq_zero_right hQ hPz hQz, nonsingular_smul, hP]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 → P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3
      · by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · simp only [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| hxy hx, nonsingular_smul,
            nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy]
        · simp only [add_of_X_ne hP.left hQ.left hPz hQz hx, nonsingular_smul,
            nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy]
      · rw [_root_.not_imp, not_ne_iff] at hxy
        by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · simp only [add_of_Y_eq hP hPz hQz hxy.left hy hxy.right, nonsingular_smul,
            nonsingular_zero]
        · simp only [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy, nonsingular_smul,
            nonsingular_zero]

variable (V) in
/-- The addition of two point classes. If `P` is a point representative,
then `W.addMap ⟦P⟧ ⟦Q⟧` is definitionally equivalent to `W.add P Q`. -/
noncomputable def addMap (P Q : PointClass R) : PointClass R :=
  Quotient.map₂ V.add (fun _ _ hP _ _ hQ => add_equiv hP hQ) P Q

lemma addMap_eq (P Q : Fin 3 → R) : V.addMap ⟦P⟧ ⟦Q⟧ = ⟦V.add P Q⟧ :=
  rfl

lemma addMap_of_Z_eq_zero_left {P : Fin 3 → F} {Q : PointClass F} (hP : W.Nonsingular P)
    (hQ : W.NonsingularLift Q) (hPz : P z = 0) : W.addMap ⟦P⟧ Q = Q := by
  rcases Q with ⟨Q⟩
  by_cases hQz : Q z = 0
  · erw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz, smul_eq, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hQ hQz
  · erw [addMap_eq, add_of_Z_eq_zero_left hP hPz hQz, smul_eq]
    rfl

lemma addMap_of_Z_eq_zero_right {P : PointClass F} {Q : Fin 3 → F} (hP : W.NonsingularLift P)
    (hQ : W.Nonsingular Q) (hQz : Q z = 0) : W.addMap P ⟦Q⟧ = P := by
  rcases P with ⟨P⟩
  by_cases hPz : P z = 0
  · erw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz, smul_eq, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
  · erw [addMap_eq, add_of_Z_eq_zero_right hQ hPz hQz, smul_eq]
    rfl

lemma addMap_of_Y_eq {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3) : W.addMap ⟦P⟧ ⟦Q⟧ = ⟦![1, 1, 0]⟧ := by
  by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
  · rw [addMap_eq, add_of_Y_eq hP hPz hQz hx hy hy', smul_eq]
  · rw [addMap_eq, add_of_Y_ne hP.left hQ hPz hQz hx hy, smul_eq]

lemma addMap_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hxy : P x * Q z ^ 2 = Q x * P z ^ 2 → P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.addMap ⟦P⟧ ⟦Q⟧ =
      ⟦![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1]⟧ := by
  by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
  · rw [addMap_eq, add_of_Y_ne' hP hQ hPz hQz hx <| hxy hx, smul_eq]
  · rw [addMap_eq, add_of_X_ne hP hQ hPz hQz hx, smul_eq]

lemma nonsingularLift_addMap {P Q : PointClass F} (hP : W.NonsingularLift P)
    (hQ : W.NonsingularLift Q) : W.NonsingularLift <| W.addMap P Q := by
  rcases P, Q with ⟨⟨_⟩, ⟨_⟩⟩
  exact nonsingular_add hP hQ

end Addition

section Point

/-! ### Nonsingular rational points -/

/-- A nonsingular rational point on `W`. -/
structure Point where
  {point : PointClass R}
  (nonsingular : V.NonsingularLift point)

/-- The point class underlying a nonsingular rational point on `W`. -/
add_decl_doc Point.point

/-- The nonsingular condition underlying a nonsingular rational point on `W`. -/
add_decl_doc Point.nonsingular

namespace Point

instance instZeroPoint [Nontrivial R] : Zero V.Point :=
  ⟨⟨nonsingularLift_zero⟩⟩

lemma zero_def [Nontrivial R] : (⟨nonsingularLift_zero⟩ : V.Point) = 0 :=
  rfl

/-- The map from a nonsingular rational point on a Weierstrass curve `W` in affine coordinates
to the corresponding nonsingular rational point on `W` in Jacobian coordinates. -/
def fromAffine [Nontrivial R] : V.toAffine.Point → V.Point
  | 0 => 0
  | Affine.Point.some h => ⟨(nonsingularLift_some ..).mpr h⟩

lemma fromAffine_zero [Nontrivial R] : fromAffine 0 = (0 : V.Point) :=
  rfl

lemma fromAffine_some [Nontrivial R] {X Y : R} (h : V.toAffine.Nonsingular X Y) :
    fromAffine (Affine.Point.some h) = ⟨(nonsingularLift_some ..).mpr h⟩ :=
  rfl

/-- The negation of a nonsingular rational point on `W`.
Given a nonsingular rational point `P` on `W`, use `-P` instead of `neg P`. -/
def neg (P : W.Point) : W.Point :=
  ⟨nonsingularLift_negMap P.nonsingular⟩

instance instNegPoint : Neg W.Point :=
  ⟨neg⟩

lemma neg_def (P : W.Point) : P.neg = -P :=
  rfl

/-- The addition of two nonsingular rational points on `W`.
Given two nonsingular rational points `P` and `Q` on `W`, use `P + Q` instead of `add P Q`. -/
noncomputable def add (P Q : W.Point) : W.Point :=
  ⟨nonsingularLift_addMap P.nonsingular Q.nonsingular⟩

noncomputable instance instAddPoint : Add W.Point :=
  ⟨add⟩

lemma add_def (P Q : W.Point) : P.add Q = P + Q :=
  rfl

end Point

end Point

section Affine

/-! ### Equivalence with affine coordinates -/

open scoped Classical

namespace Point

variable (W) in
/-- The map from a point representative that is nonsingular on a Weierstrass curve `W` in Jacobian
coordinates to the corresponding nonsingular rational point on `W` in affine coordinates. -/
noncomputable def toAffine (P : Fin 3 → F) : W.toAffine.Point :=
  if hP : W.Nonsingular P then if hPz : P z = 0 then 0 else
    Affine.Point.some <| (nonsingular_of_Z_ne_zero hPz).mp hP else 0

lemma toAffine_of_singular {P : Fin 3 → F} (hP : ¬W.Nonsingular P) : toAffine W P = 0 := by
  rw [toAffine, dif_neg hP]

lemma toAffine_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    toAffine W P = 0 := by
  rw [toAffine, dif_pos hP, dif_pos hPz]

lemma toAffine_zero : toAffine W ![1, 1, 0] = 0 :=
  toAffine_of_Z_eq_zero nonsingular_zero rfl

lemma toAffine_of_Z_ne_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) :
    toAffine W P = Affine.Point.some ((nonsingular_of_Z_ne_zero hPz).mp hP) := by
  rw [toAffine, dif_pos hP, dif_neg hPz]

lemma toAffine_some {X Y : F} (h : W.Nonsingular ![X, Y, 1]) :
    toAffine W ![X, Y, 1] = Affine.Point.some ((nonsingular_some ..).mp h) := by
  simp only [toAffine_of_Z_ne_zero h one_ne_zero, fin3_def_ext, one_pow, div_one]

lemma toAffine_smul {P : Fin 3 → F} (u : Fˣ) : toAffine W (u • P) = toAffine W P := by
  by_cases hP : W.Nonsingular P
  · by_cases hPz : P z = 0
    · rw [toAffine_of_Z_eq_zero ((nonsingular_smul ..).mpr hP) <| u.mul_right_eq_zero.mpr hPz,
        toAffine_of_Z_eq_zero hP hPz]
    · rw [toAffine_of_Z_ne_zero ((nonsingular_smul ..).mpr hP) <| mul_ne_zero u.ne_zero hPz,
        toAffine_of_Z_ne_zero hP hPz, Affine.Point.some.injEq]
      simp only [smul_fin3_ext, mul_pow, mul_div_mul_left _ _ <| pow_ne_zero _ u.ne_zero, and_self]
  · rw [toAffine_of_singular <| hP.comp (W.nonsingular_smul P u).mp, toAffine_of_singular hP]

lemma toAffine_of_equiv {P Q : Fin 3 → F} (h : P ≈ Q) : toAffine W P = toAffine W Q := by
  rcases h with ⟨u, rfl⟩
  exact toAffine_smul u

lemma toAffine_neg {P : Fin 3 → F} (hP : W.Nonsingular P) :
    toAffine W (W.neg P) = -toAffine W P := by
  by_cases hPz : P z = 0
  · rw [neg_of_Z_eq_zero hP hPz, toAffine_smul, toAffine_zero, toAffine_of_Z_eq_zero hP hPz,
      Affine.Point.neg_zero]
  · rw [neg_of_Z_ne_zero hPz, toAffine_smul, toAffine_some <| (nonsingular_smul ..).mp <|
      neg_of_Z_ne_zero hPz ▸ nonsingular_neg hP, toAffine_of_Z_ne_zero hP hPz,
      Affine.Point.neg_some]

lemma toAffine_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    toAffine W (W.add P Q) = toAffine W P + toAffine W Q := by
  by_cases hPz : P z = 0
  · rw [toAffine_of_Z_eq_zero hP hPz, _root_.zero_add]
    by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero hP hQ hPz hQz, toAffine_smul, toAffine_zero,
        toAffine_of_Z_eq_zero hQ hQz]
    · rw [add_of_Z_eq_zero_left hP hPz hQz, toAffine_smul]
  · by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero_right hQ hPz hQz, toAffine_smul, toAffine_of_Z_eq_zero hQ hQz,
        _root_.add_zero]
    · rw [toAffine_of_Z_ne_zero hP hPz, toAffine_of_Z_ne_zero hQ hQz]
      by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 → P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3
      · by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · rw [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| hxy hx, toAffine_smul,
            toAffine_some <| nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy,
            Affine.Point.some_add_some_of_Yne
              ((div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz)).mpr hx) <|
                negY_of_Z_ne_zero hQz ▸
                  (hxy hx).comp (div_eq_div_iff (pow_ne_zero 3 hPz) (pow_ne_zero 3 hQz)).mp]
        · rw [add_of_X_ne hP.left hQ.left hPz hQz hx, toAffine_smul,
            toAffine_some <| nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy,
            Affine.Point.some_add_some_of_Xne <|
              hx.comp (div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz)).mp]
      · rw [_root_.not_imp, not_ne_iff] at hxy
        rw [Affine.Point.some_add_some_of_Yeq
          ((div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz)).mpr hxy.left) <|
            negY_of_Z_ne_zero hQz ▸
              (div_eq_div_iff (pow_ne_zero 3 hPz) (pow_ne_zero 3 hQz)).mpr hxy.right]
        by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · rw [add_of_Y_eq hP hPz hQz hxy.left hy hxy.right, toAffine_smul, toAffine_zero]
        · rw [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy, toAffine_smul, toAffine_zero]

/-- The map from a nonsingular rational point on a Weierstrass curve `W` in Jacobian coordinates
to the corresponding nonsingular rational point on `W` in affine coordinates. -/
noncomputable def toAffineLift (P : W.Point) : W.toAffine.Point :=
  P.point.lift _ fun _ _ => toAffine_of_equiv

lemma toAffineLift_eq {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) :
    toAffineLift ⟨hP⟩ = toAffine W P :=
  rfl

lemma toAffineLift_of_Z_eq_zero {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) (hPz : P z = 0) :
    toAffineLift ⟨hP⟩ = 0 :=
  toAffine_of_Z_eq_zero hP hPz

lemma toAffineLift_zero : toAffineLift (0 : W.Point) = 0 :=
  toAffine_zero

lemma toAffineLift_of_Z_ne_zero {P : Fin 3 → F} {hP : W.NonsingularLift ⟦P⟧} (hPz : P z ≠ 0) :
    toAffineLift ⟨hP⟩ = Affine.Point.some ((nonsingular_of_Z_ne_zero hPz).mp hP) :=
  toAffine_of_Z_ne_zero hP hPz

lemma toAffineLift_some {X Y : F} (h : W.NonsingularLift ⟦![X, Y, 1]⟧) :
    toAffineLift ⟨h⟩ = Affine.Point.some ((nonsingular_some ..).mp h) :=
  toAffine_some h

lemma toAffineLift_neg {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) :
    toAffineLift (-⟨hP⟩) = -toAffineLift ⟨hP⟩ :=
  toAffine_neg hP

lemma toAffineLift_add {P Q : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) (hQ : W.NonsingularLift ⟦Q⟧) :
    toAffineLift (⟨hP⟩ + ⟨hQ⟩) = toAffineLift ⟨hP⟩ + toAffineLift ⟨hQ⟩ :=
  toAffine_add hP hQ

/-- The equivalence between the nonsingular rational points on a Weierstrass curve `W` in Jacobian
coordinates with the nonsingular rational points on `W` in affine coordinates. -/
@[simps]
noncomputable def toAffine_addEquiv : W.Point ≃+ W.toAffine.Point where
  toFun := toAffineLift
  invFun := fromAffine
  left_inv := by
    rintro @⟨⟨P⟩, hP⟩
    by_cases hPz : P z = 0
    · erw [toAffineLift_eq, toAffine_of_Z_eq_zero hP hPz, fromAffine_zero, mk.injEq, Quotient.eq]
      exact Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
    · erw [toAffineLift_eq, toAffine_of_Z_ne_zero hP hPz, fromAffine_some, mk.injEq, Quotient.eq]
      exact Setoid.symm <| equiv_some_of_Z_ne_zero hPz
  right_inv := by
    rintro (_ | _)
    · erw [fromAffine_zero, toAffineLift_zero, Affine.Point.zero_def]
    · rw [fromAffine_some, toAffineLift_some]
  map_add' := by
    rintro @⟨⟨_⟩, _⟩ @⟨⟨_⟩, _⟩
    simpa only using toAffineLift_add ..

end Point

end Affine

section map

lemma comp_fin3 {S} (f : R → S) (X Y Z : R) : f ∘ ![X, Y, Z] = ![f X, f Y, f Z] := by
  ext i; fin_cases i <;> rfl

variable {S : Type*} [CommRing S] (f : R →+* S) (P Q : Fin 3 → R)

@[simp] lemma map_addZ : addZ (f ∘ P) (f ∘ Q) = f (addZ P Q) := by simp [addZ]
@[simp] lemma map_addX : addX (V.map f) (f ∘ P) (f ∘ Q) = f (V.addX P Q) := by simp [addX]
@[simp] lemma map_addY' : addY' (V.map f) (f ∘ P) (f ∘ Q) = f (V.addY' P Q) := by simp [addY']
@[simp] lemma map_negY : negY (V.map f) (f ∘ P) = f (V.negY P) := by simp [negY]

@[simp] lemma map_neg : neg (V.map f) (f ∘ P) = f ∘ V.neg P := by
  ext i; fin_cases i <;> simp [neg]

@[simp] lemma map_addY : addY (V.map f) (f ∘ P) (f ∘ Q) = f (V.addY P Q) := by
  simp [addY, ← comp_fin3]

@[simp] lemma map_dblZ : dblZ (V.map f) (f ∘ P) = f (V.dblZ P) := by simp [dblZ]
@[simp] lemma map_dblX : dblX (V.map f) (f ∘ P) = f (V.dblX P) := by simp [dblX]
@[simp] lemma map_dblY' : dblY' (V.map f) (f ∘ P) = f (V.dblY' P) := by simp [dblY']
@[simp] lemma map_dblY : dblY (V.map f) (f ∘ P) = f (V.dblY P) := by simp [dblY, ← comp_fin3]

end map

end WeierstrassCurve.Jacobian
