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
condition.

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

## Main definitions

 * `WeierstrassCurve.Jacobian.PointClass`: the equivalence class of a point representative.
 * `WeierstrassCurve.Jacobian.toAffine`: the Weierstrass curve in affine coordinates.
 * `WeierstrassCurve.Jacobian.Nonsingular`: the nonsingular condition on a point representative.
 * `WeierstrassCurve.Jacobian.NonsingularLift`: the nonsingular condition on a point class.

## Implementation notes

A point representative is implemented as a term `P` of type `Fin 3 → R`, which allows for the vector
notation `![x, y, z]`. However, `P` is not syntactically equivalent to the expanded vector
`![P x, P y, P z]`, so the lemmas `fin3_def` and `fin3_def_ext` can be used to convert between the
two forms. The equivalence of two point representatives `P` and `Q` is implemented as an equivalence
of orbits of the action of `Rˣ`, or equivalently that there is some unit `u` of `R` such that
`P = u • Q`. However, `u • Q` is not syntactically equal to `![u² * Q x, u³ * Q y, u * Q z]`, so
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

universe u v

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

variable {R : Type u} [CommRing R] {V : Jacobian R} {F : Type v} [Field F] {W : Jacobian F}

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

variable (R) in
/-- The equivalence class of a point representative. -/
abbrev PointClass : Type u :=
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
  simp only [equation_iff, Affine.equation_iff', fin3_def_ext, one_pow, mul_one]

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

end WeierstrassCurve.Jacobian
