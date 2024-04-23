/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.PDeriv

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

variable {R : Type u} [CommRing R] (W : Jacobian R)

lemma fin3_def (P : Fin 3 → R) : P = ![P x, P y, P z] := by
  ext n; fin_cases n <;> rfl

/-- The scalar multiplication on a point representative. -/
scoped instance instSMulPoint : SMul Rˣ <| Fin 3 → R :=
  ⟨fun u P => ![u ^ 2 * P x, u ^ 3 * P y, u * P z]⟩

lemma smul_fin3 (P : Fin 3 → R) (u : Rˣ) :
    u • P = ![u ^ 2 * P x, u ^ 3 * P y, u * P z] :=
  rfl

lemma smul_fin3_ext (P : Fin 3 → R) (u : Rˣ) :
    (u • P) x = u ^ 2 * P x ∧ (u • P) y = u ^ 3 * P y ∧ (u • P) z = u * P z := by
  simp [smul_fin3]

/-- The multiplicative action on a point representative. -/
scoped instance instMulActionPoint : MulAction Rˣ <| Fin 3 → R where
  one_smul _ := by simp only [smul_fin3, Units.val_one, one_pow, one_mul, ← fin3_def]
  mul_smul _ _ _ := by simp only [smul_fin3, Units.val_mul, mul_pow, mul_assoc]; matrix_simp

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
def Equation (P : Fin 3 → R) : Prop :=
  eval P W.polynomial = 0

lemma equation_iff (P : Fin 3 → R) : W.Equation P ↔
    P y ^ 2 + W.a₁ * P x * P y * P z + W.a₃ * P y * P z ^ 3
      = P x ^ 3 + W.a₂ * P x ^ 2 * P z ^ 2 + W.a₄ * P x * P z ^ 4 + W.a₆ * P z ^ 6 := by
  rw [Equation, eval_polynomial, sub_eq_zero]

lemma equation_zero : W.Equation ![1, 1, 0] :=
  (W.equation_iff ![1, 1, 0]).mpr <| by matrix_simp; ring1

lemma equation_zero' (Y : R) : W.Equation ![Y ^ 2, Y ^ 3, 0] :=
  (W.equation_iff ![Y ^ 2, Y ^ 3, 0]).mpr <| by matrix_simp; ring1

lemma equation_some (X Y : R) : W.Equation ![X, Y, 1] ↔ W.toAffine.equation X Y := by
  rw [equation_iff, W.toAffine.equation_iff]
  congr! 1 <;> matrix_simp <;> ring1

lemma equation_smul_iff (P : Fin 3 → R) (u : Rˣ) : W.Equation (u • P) ↔ W.Equation P :=
  have (u : Rˣ) {P : Fin 3 → R} (h : W.Equation P) : W.Equation <| u • P := by
    rw [equation_iff] at h ⊢
    linear_combination (norm := (simp only [smul_fin3_ext]; ring1)) (u : R) ^ 6 * h
  ⟨fun h => by convert this u⁻¹ h; rw [inv_smul_smul], this u⟩

/-- The partial derivative $W_X(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $X$. -/
@[pp_dot]
noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  pderiv x W.polynomial

lemma polynomialX_eq : W.polynomialX =
    C W.a₁ * X 1 * X 2 - (C 3 * X 0 ^ 2 + C (2 * W.a₂) * X 0 * X 2 ^ 2 + C W.a₄ * X 2 ^ 4) := by
  rw [polynomialX, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialX (P : Fin 3 → R) : eval P W.polynomialX =
    W.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W.a₂ * P x * P z ^ 2 + W.a₄ * P z ^ 4) := by
  rw [polynomialX_eq]
  eval_simp

/-- The partial derivative $W_Y(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $Y$. -/
@[pp_dot]
noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  pderiv y W.polynomial

lemma polynomialY_eq : W.polynomialY =
    C 2 * X 1 + C W.a₁ * X 0 * X 2 + C W.a₃ * X 2 ^ 3 := by
  rw [polynomialY, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialY (P : Fin 3 → R) :
    eval P W.polynomialY = 2 * P y + W.a₁ * P x * P z + W.a₃ * P z ^ 3 := by
  rw [polynomialY_eq]
  eval_simp

/-- The partial derivative $W_Z(X, Y, Z)$ of $W(X, Y, Z)$ with respect to $Z$. -/
@[pp_dot]
noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  pderiv z W.polynomial

lemma polynomialZ_eq : W.polynomialZ =
    C W.a₁ * X 0 * X 1 + C (3 * W.a₃) * X 1 * X 2 ^ 2
      - (C (2 * W.a₂) * X 0 ^ 2 * X 2 + C (4 * W.a₄) * X 0 * X 2 ^ 3 + C (6 * W.a₆) * X 2 ^ 5) := by
  rw [polynomialZ, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialZ (P : Fin 3 → R) : eval P W.polynomialZ =
    W.a₁ * P x * P y + 3 * W.a₃ * P y * P z ^ 2
      - (2 * W.a₂ * P x ^ 2 * P z + 4 * W.a₄ * P x * P z ^ 3 + 6 * W.a₆ * P z ^ 5) := by
  rw [polynomialZ_eq]
  eval_simp

/-- The proposition that a point representative $(x, y, z)$ in `W` is nonsingular.
In other words, either $W_X(x, y, z) \ne 0$, $W_Y(x, y, z) \ne 0$, or $W_Z(x, y, z) \ne 0$. -/
@[pp_dot]
def Nonsingular (P : Fin 3 → R) : Prop :=
  W.Equation P ∧ (eval P W.polynomialX ≠ 0 ∨ eval P W.polynomialY ≠ 0 ∨ eval P W.polynomialZ ≠ 0)

lemma nonsingular_iff (P : Fin 3 → R) : W.Nonsingular P ↔ W.Equation P ∧
    (W.a₁ * P y * P z ≠ 3 * P x ^ 2 + 2 * W.a₂ * P x * P z ^ 2 + W.a₄ * P z ^ 4 ∨
      P y ≠ -P y - W.a₁ * P x * P z - W.a₃ * P z ^ 3 ∨
      W.a₁ * P x * P y + 3 * W.a₃ * P y * P z ^ 2
        ≠ 2 * W.a₂ * P x ^ 2 * P z + 4 * W.a₄ * P x * P z ^ 3 + 6 * W.a₆ * P z ^ 5) := by
  rw [Nonsingular, eval_polynomialX, eval_polynomialY, eval_polynomialZ, sub_ne_zero, sub_ne_zero,
    ← sub_ne_zero (a := P y)]
  congr! 4
  ring1

lemma nonsingular_zero [Nontrivial R] : W.Nonsingular ![1, 1, 0] :=
  (W.nonsingular_iff ![1, 1, 0]).mpr ⟨W.equation_zero,
    by simp; by_contra! h; exact one_ne_zero <| by linear_combination -h.1 - h.2.1⟩

lemma nonsingular_zero' [NoZeroDivisors R] {Y : R} (hy : Y ≠ 0) :
    W.Nonsingular ![Y ^ 2, Y ^ 3, 0] :=
  (W.nonsingular_iff ![Y ^ 2, Y ^ 3, 0]).mpr ⟨W.equation_zero' Y,
    by simp [hy]; by_contra! h; exact pow_ne_zero 3 hy <| by linear_combination Y ^ 3 * h.1 - h.2.1⟩

lemma nonsingular_some (X Y : R) : W.Nonsingular ![X, Y, 1] ↔ W.toAffine.nonsingular X Y := by
  rw [nonsingular_iff]
  matrix_simp
  simp only [W.toAffine.nonsingular_iff, equation_some, and_congr_right_iff,
    W.toAffine.equation_iff, ← not_and_or, not_iff_not, one_pow, mul_one, Iff.comm, iff_self_and]
  intro h hX hY
  linear_combination (norm := ring1) 6 * h - 2 * X * hX - 3 * Y * hY

lemma nonsingular_smul_iff (P : Fin 3 → R) (u : Rˣ) : W.Nonsingular (u • P) ↔ W.Nonsingular P :=
  have (u : Rˣ) {P : Fin 3 → R} (h : W.Nonsingular <| u • P) : W.Nonsingular P := by
    rcases (W.nonsingular_iff _).mp h with ⟨h, h'⟩
    refine (W.nonsingular_iff P).mpr ⟨(W.equation_smul_iff P u).mp h, ?_⟩
    contrapose! h'
    simp only [smul_fin3_ext]
    exact ⟨by linear_combination (norm := ring1) (u : R) ^ 4 * h'.left,
      by linear_combination (norm := ring1) (u : R) ^ 3 * h'.right.left,
      by linear_combination (norm := ring1) (u : R) ^ 5 * h'.right.right⟩
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

lemma nonsingularLift_zero [Nontrivial R] : W.NonsingularLift ⟦![1, 1, 0]⟧ :=
  W.nonsingular_zero

lemma nonsingularLift_zero' [NoZeroDivisors R] {Y : R} (hy : Y ≠ 0) :
    W.NonsingularLift ⟦![Y ^ 2, Y ^ 3, 0]⟧ :=
  W.nonsingular_zero' hy

lemma nonsingularLift_some (X Y : R) :
    W.NonsingularLift ⟦![X, Y, 1]⟧ ↔ W.toAffine.nonsingular X Y :=
  W.nonsingular_some X Y

variable {F : Type u} [Field F] {W : Jacobian F}

lemma equiv_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : P ≈ Q := by
  rw [fin3_def P, hPz] at hP ⊢
  rw [fin3_def Q, hQz] at hQ ⊢
  simp [nonsingular_iff, equation_iff] at hP hQ
  have hPx : P x ≠ 0 := fun h => by simp [h] at hP; simp [hP] at hP
  have hQx : Q x ≠ 0 := fun h => by simp [h] at hQ; simp [hQ] at hQ
  have hPy : P y ≠ 0 := fun h => by simp [h] at hP; exact hPx <| pow_eq_zero hP.left.symm
  have hQy : Q y ≠ 0 := fun h => by simp [h] at hQ; exact hQx <| pow_eq_zero hQ.left.symm
  use Units.mk0 _ <| mul_ne_zero (div_ne_zero hPy hPx) (div_ne_zero hQx hQy)
  simp? [smul_fin3, mul_pow, div_pow] says
    simp only [Fin.isValue, Units.mk0_mul, smul_fin3, Units.val_mul, Units.val_mk0, mul_pow,
      div_pow, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, mul_zero]
  congr! 2
  · field_simp [hP.left, hQ.left]
    ring1
  · field_simp [← hP.left, ← hQ.left]
    ring1

lemma equiv_zero_of_Z_eq_zero {P : Fin 3 → F} (h : W.Nonsingular P) (hPz : P z = 0) :
    P ≈ ![1, 1, 0] :=
  equiv_of_Z_eq_zero h W.nonsingular_zero hPz rfl

lemma equiv_some_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    P ≈ ![P x / P z ^ 2, P y / P z ^ 3, 1] :=
  ⟨Units.mk0 _ hPz, by simp [smul_fin3, ← fin3_def P, mul_div_cancel₀ _ <| pow_ne_zero _ hPz]⟩

lemma nonsingular_iff_affine_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.toAffine.nonsingular (P x / P z ^ 2) (P y / P z ^ 3) :=
  (W.nonsingular_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| W.nonsingular_some ..

lemma nonsingular_of_affine_of_Z_ne_zero {P : Fin 3 → F}
    (h : W.toAffine.nonsingular (P x / P z ^ 2) (P y / P z ^ 3)) (hPz : P z ≠ 0) :
    W.Nonsingular P :=
  (nonsingular_iff_affine_of_Z_ne_zero hPz).mpr h

lemma nonsingular_affine_of_Z_ne_zero {P : Fin 3 → F} (h : W.Nonsingular P) (hPz : P z ≠ 0) :
    W.toAffine.nonsingular (P x / P z ^ 2) (P y / P z ^ 3) :=
  (nonsingular_iff_affine_of_Z_ne_zero hPz).mp h

end Equation

end WeierstrassCurve.Jacobian
