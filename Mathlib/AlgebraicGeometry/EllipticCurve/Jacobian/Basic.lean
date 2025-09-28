/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Tactic.Ring.NamePolyVars

/-!
# Weierstrass equations and the nonsingular condition in Jacobian coordinates

A point on the projective plane over a commutative ring `R` with weights `(2, 3, 1)` is an
equivalence class `[x : y : z]` of triples `(x, y, z) ≠ (0, 0, 0)` of elements in `R` such that
`(x, y, z) ∼ (x', y', z')` if there is some unit `u` in `Rˣ` with `(x, y, z) = (u²x', u³y', uz')`.

Let `W` be a Weierstrass curve over a commutative ring `R` with coefficients `aᵢ`. A
*Jacobian point* is a point on the projective plane over `R` with weights `(2, 3, 1)` satisfying the
*`(2, 3, 1)`-homogeneous Weierstrass equation* `W(X, Y, Z) = 0` in *Jacobian coordinates*, where
`W(X, Y, Z) := Y² + a₁XYZ + a₃YZ³ - (X³ + a₂X²Z² + a₄XZ⁴ + a₆Z⁶)`. It is *nonsingular* if its
partial derivatives `W_X(x, y, z)`, `W_Y(x, y, z)`, and `W_Z(x, y, z)` do not vanish simultaneously.

This file gives an explicit implementation of equivalence classes of triples up to scaling by
weights, and defines polynomials associated to Weierstrass equations and the nonsingular condition
in Jacobian coordinates. The group law on the actual type of nonsingular Jacobian points will be
defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean`, based on the formulae for
group operations in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean`.

## Main definitions

* `WeierstrassCurve.Jacobian.PointClass`: the equivalence class of a point representative.
* `WeierstrassCurve.Jacobian.Nonsingular`: the nonsingular condition on a point representative.
* `WeierstrassCurve.Jacobian.NonsingularLift`: the nonsingular condition on a point class.

## Main statements

* `WeierstrassCurve.Jacobian.polynomial_relation`: Euler's homogeneous function theorem.

## Implementation notes

All definitions and lemmas for Weierstrass curves in Jacobian coordinates live in the namespace
`WeierstrassCurve.Jacobian` to distinguish them from those in other coordinates. This is simply an
abbreviation for `WeierstrassCurve` that can be converted using `WeierstrassCurve.toJacobian`. This
can be converted into `WeierstrassCurve.Affine` using `WeierstrassCurve.Jacobian.toAffine`.

A point representative is implemented as a term `P` of type `Fin 3 → R`, which allows for the vector
notation `![x, y, z]`. However, `P` is not syntactically equivalent to the expanded vector
`![P x, P y, P z]`, so the lemmas `fin3_def` and `fin3_def_ext` can be used to convert between the
two forms. The equivalence of two point representatives `P` and `Q` is implemented as an equivalence
of orbits of the action of `Rˣ`, or equivalently that there is some unit `u` of `R` such that
`P = u • Q`. However, `u • Q` is not syntactically equal to `![u² * Q x, u³ * Q y, u * Q z]`, so the
lemmas `smul_fin3` and `smul_fin3_ext` can be used to convert between the two forms. Files in
`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian` make extensive use of `erw` to get around this.
While `erw` is often an indication of a problem, in this case it is self-contained and should not
cause any issues. It would alternatively be possible to add some automation to assist here.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Basic.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, Jacobian, Weierstrass equation, nonsingular
-/

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

open MvPolynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_C, map_X, map_neg, map_add, map_sub, map_mul, map_pow,
    map_div₀, WeierstrassCurve.map, Function.comp_apply])

local macro "matrix_simp" : tactic =>
  `(tactic| simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])

local macro "pderiv_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, pderiv_mul, pderiv_pow,
    pderiv_C, pderiv_X_self, pderiv_X_of_ne one_ne_zero, pderiv_X_of_ne one_ne_zero.symm,
    pderiv_X_of_ne (by decide : z ≠ x), pderiv_X_of_ne (by decide : x ≠ z),
    pderiv_X_of_ne (by decide : z ≠ y), pderiv_X_of_ne (by decide : y ≠ z)])

universe r s u v

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v}

name_poly_vars X, Y, Z over R

namespace WeierstrassCurve

/-! ## Jacobian coordinates -/

variable (R) in
/-- An abbreviation for a Weierstrass curve in Jacobian coordinates. -/
abbrev Jacobian : Type r :=
  WeierstrassCurve R

/-- The conversion from a Weierstrass curve to Jacobian coordinates. -/
abbrev toJacobian (W : WeierstrassCurve R) : Jacobian R :=
  W

namespace Jacobian

/-- The conversion from a Weierstrass curve in Jacobian coordinates to affine coordinates. -/
abbrev toAffine (W' : Jacobian R) : Affine R :=
  W'

lemma fin3_def (P : Fin 3 → R) : ![P x, P y, P z] = P := by
  ext n; fin_cases n <;> rfl

lemma fin3_def_ext (a b c : R) : ![a, b, c] x = a ∧ ![a, b, c] y = b ∧ ![a, b, c] z = c :=
  ⟨rfl, rfl, rfl⟩

lemma comp_fin3 (f : R → S) (a b c : R) : f ∘ ![a, b, c] = ![f a, f b, f c] :=
  (FinVec.map_eq ..).symm

variable [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Field F] [Field K] {W' : Jacobian R}
  {W : Jacobian F}

/-- The scalar multiplication for a Jacobian point representative on a Weierstrass curve. -/
scoped instance : SMul R <| Fin 3 → R :=
  ⟨fun u P => ![u ^ 2 * P x, u ^ 3 * P y, u * P z]⟩

lemma smul_fin3 (P : Fin 3 → R) (u : R) : u • P = ![u ^ 2 * P x, u ^ 3 * P y, u * P z] :=
  rfl

lemma smul_fin3_ext (P : Fin 3 → R) (u : R) :
    (u • P) x = u ^ 2 * P x ∧ (u • P) y = u ^ 3 * P y ∧ (u • P) z = u * P z :=
  ⟨rfl, rfl, rfl⟩

lemma comp_smul (f : R →+* S) (P : Fin 3 → R) (u : R) : f ∘ (u • P) = f u • f ∘ P := by
  ext n; fin_cases n <;> simp only [smul_fin3, comp_fin3] <;> map_simp

/-- The multiplicative action for a Jacobian point representative on a Weierstrass curve. -/
scoped instance : MulAction R <| Fin 3 → R where
  one_smul _ := by simp only [smul_fin3, one_pow, one_mul, fin3_def]
  mul_smul _ _ _ := by simp only [smul_fin3, mul_pow, mul_assoc, fin3_def_ext]

/-- The equivalence setoid for a Jacobian point representative on a Weierstrass curve. -/
@[reducible]
scoped instance : Setoid <| Fin 3 → R :=
  MulAction.orbitRel Rˣ <| Fin 3 → R

variable (R) in
/-- The equivalence class of a Jacobian point representative on a Weierstrass curve. -/
abbrev PointClass : Type r :=
  MulAction.orbitRel.Quotient Rˣ <| Fin 3 → R

lemma smul_equiv (P : Fin 3 → R) {u : R} (hu : IsUnit u) : u • P ≈ P :=
  ⟨hu.unit, rfl⟩

@[simp]
lemma smul_eq (P : Fin 3 → R) {u : R} (hu : IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧ :=
  Quotient.eq.mpr <| smul_equiv P hu

lemma smul_equiv_smul (P Q : Fin 3 → R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    u • P ≈ v • Q ↔ P ≈ Q := by
  rw [← Quotient.eq_iff_equiv, ← Quotient.eq_iff_equiv, smul_eq P hu, smul_eq Q hv]

lemma equiv_iff_eq_of_Z_eq' {P Q : Fin 3 → R} (hz : P z = Q z) (hQz : Q z ∈ nonZeroDivisors R) :
    P ≈ Q ↔ P = Q := by
  refine ⟨?_, Quotient.exact.comp <| congrArg _⟩
  rintro ⟨u, rfl⟩
  simp only [Units.smul_def, (mul_cancel_right_mem_nonZeroDivisors hQz).mp <| one_mul (Q z) ▸ hz]
  rw [one_smul]

lemma equiv_iff_eq_of_Z_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hz : P z = Q z) (hQz : Q z ≠ 0) :
    P ≈ Q ↔ P = Q :=
  equiv_iff_eq_of_Z_eq' hz <| mem_nonZeroDivisors_of_ne_zero hQz

lemma Z_eq_zero_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P z = 0 ↔ Q z = 0 := by
  rcases h with ⟨_, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext, Units.mul_right_eq_zero]

lemma X_eq_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P x * Q z ^ 2 = Q x * P z ^ 2 := by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

lemma Y_eq_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P y * Q z ^ 3 = Q y * P z ^ 3 := by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
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
  simp only [Units.smul_def, smul_fin3, Units.val_div_eq_div_val, Units.val_mk0, div_pow, mul_comm,
    mul_div, ← hx, ← hy, mul_div_cancel_right₀ _ <| pow_ne_zero _ hQz, mul_div_cancel_right₀ _ hQz,
    fin3_def]

lemma equiv_some_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    P ≈ ![P x / P z ^ 2, P y / P z ^ 3, 1] :=
  equiv_of_X_eq_of_Y_eq hPz one_ne_zero
    (by linear_combination (norm := (matrix_simp; ring1)) -P x * div_self (pow_ne_zero 2 hPz))
    (by linear_combination (norm := (matrix_simp; ring1)) -P y * div_self (pow_ne_zero 3 hPz))

lemma X_eq_iff {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P x * Q z ^ 2 = Q x * P z ^ 2 ↔ P x / P z ^ 2 = Q x / Q z ^ 2 :=
  (div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz)).symm

lemma Y_eq_iff {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P y * Q z ^ 3 = Q y * P z ^ 3 ↔ P y / P z ^ 3 = Q y / Q z ^ 3 :=
  (div_eq_div_iff (pow_ne_zero 3 hPz) (pow_ne_zero 3 hQz)).symm

/-! ## Weierstrass equations in Jacobian coordinates -/

variable (W') in
/-- The polynomial `W(X, Y, Z) := Y² + a₁XYZ + a₃YZ³ - (X³ + a₂X²Z² + a₄XZ⁴ + a₆Z⁶)` associated to a
Weierstrass curve `W` over a ring `R` in Jacobian coordinates.

This is represented as a term of type `MvPolynomial (Fin 3) R`, where `X`, `Y`, and `Z`
represent `X`, `Y`, and `Z` respectively. -/
noncomputable def polynomial : MvPolynomial (Fin 3) R :=
  Y ^ 2 + C W'.a₁ * X * Y * Z + C W'.a₃ * Y * Z ^ 3
    - (X ^ 3 + C W'.a₂ * X ^ 2 * Z ^ 2 + C W'.a₄ * X * Z ^ 4 + C W'.a₆ * Z ^ 6)

lemma eval_polynomial (P : Fin 3 → R) : eval P W'.polynomial =
    P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 3
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z ^ 2 + W'.a₄ * P x * P z ^ 4 + W'.a₆ * P z ^ 6) := by
  rw [polynomial]
  simp

lemma eval_polynomial_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) : eval P W.polynomial / P z ^ 6 =
    W.toAffine.polynomial.evalEval (P x / P z ^ 2) (P y / P z ^ 3) := by
  linear_combination (norm := (rw [eval_polynomial, Affine.evalEval_polynomial]; ring1))
    W.a₁ * P x * P y / P z ^ 5 * div_self hPz + W.a₃ * P y / P z ^ 3 * div_self (pow_ne_zero 3 hPz)
      - W.a₂ * P x ^ 2 / P z ^ 4 * div_self (pow_ne_zero 2 hPz)
      - W.a₄ * P x / P z ^ 2 * div_self (pow_ne_zero 4 hPz) - W.a₆ * div_self (pow_ne_zero 6 hPz)

variable (W') in
/-- The proposition that a Jacobian point representative `(x, y, z)` lies in a Weierstrass curve
`W`.

In other words, it satisfies the `(2, 3, 1)`-homogeneous Weierstrass equation `W(X, Y, Z) = 0`. -/
def Equation (P : Fin 3 → R) : Prop :=
  eval P W'.polynomial = 0

lemma equation_iff (P : Fin 3 → R) : W'.Equation P ↔
    P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 3
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z ^ 2 + W'.a₄ * P x * P z ^ 4 + W'.a₆ * P z ^ 6) = 0 := by
  rw [Equation, eval_polynomial]

lemma equation_smul (P : Fin 3 → R) {u : R} (hu : IsUnit u) : W'.Equation (u • P) ↔ W'.Equation P :=
  have hP (u : R) {P : Fin 3 → R} (hP : W'.Equation P) : W'.Equation <| u • P := by
    rw [equation_iff] at hP ⊢
    linear_combination (norm := (simp only [smul_fin3_ext]; ring1)) u ^ 6 * hP
  ⟨fun h => by convert hP ↑hu.unit⁻¹ h; rw [smul_smul, hu.val_inv_mul, one_smul], hP u⟩

lemma equation_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.Equation P ↔ W'.Equation Q := by
  rcases h with ⟨u, rfl⟩
  exact equation_smul Q u.isUnit

lemma equation_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) :
    W'.Equation P ↔ P y ^ 2 = P x ^ 3 := by
  simp only [equation_iff, hPz, add_zero, mul_zero, zero_pow <| OfNat.ofNat_ne_zero _, sub_eq_zero]

lemma equation_zero : W'.Equation ![1, 1, 0] := by
  simp only [equation_of_Z_eq_zero, fin3_def_ext, one_pow]

lemma equation_some (a b : R) : W'.Equation ![a, b, 1] ↔ W'.toAffine.Equation a b := by
  simp only [equation_iff, Affine.equation_iff', fin3_def_ext, one_pow, mul_one]

lemma equation_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Equation P ↔ W.toAffine.Equation (P x / P z ^ 2) (P y / P z ^ 3) :=
  (equation_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| equation_some ..

/-! ## The nonsingular condition in Jacobian coordinates -/

variable (W') in
/-- The partial derivative `W_X(X, Y, Z)` with respect to `X` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates. -/
noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  pderiv x W'.polynomial

lemma polynomialX_eq : W'.polynomialX =
    C W'.a₁ * Y * Z - (C 3 * X ^ 2 + C (2 * W'.a₂) * X * Z ^ 2 + C W'.a₄ * Z ^ 4) := by
  rw [polynomialX, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialX (P : Fin 3 → R) : eval P W'.polynomialX =
    W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z ^ 2 + W'.a₄ * P z ^ 4) := by
  rw [polynomialX_eq]
  simp

lemma eval_polynomialX_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    eval P W.polynomialX / P z ^ 4 =
      W.toAffine.polynomialX.evalEval (P x / P z ^ 2) (P y / P z ^ 3) := by
  linear_combination (norm := (rw [eval_polynomialX, Affine.evalEval_polynomialX]; ring1))
    W.a₁ * P y / P z ^ 3 * div_self hPz - 2 * W.a₂ * P x / P z ^ 2 * div_self (pow_ne_zero 2 hPz)
      - W.a₄ * div_self (pow_ne_zero 4 hPz)

variable (W') in
/-- The partial derivative `W_Y(X, Y, Z)` with respect to `Y` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates. -/
noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  pderiv y W'.polynomial

lemma polynomialY_eq : W'.polynomialY = C 2 * Y + C W'.a₁ * X * Z + C W'.a₃ * Z ^ 3 := by
  rw [polynomialY, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialY (P : Fin 3 → R) :
    eval P W'.polynomialY = 2 * P y + W'.a₁ * P x * P z + W'.a₃ * P z ^ 3 := by
  rw [polynomialY_eq]
  simp

lemma eval_polynomialY_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    eval P W.polynomialY / P z ^ 3 =
      W.toAffine.polynomialY.evalEval (P x / P z ^ 2) (P y / P z ^ 3) := by
  linear_combination (norm := (rw [eval_polynomialY, Affine.evalEval_polynomialY]; ring1))
    W.a₁ * P x / P z ^ 2 * div_self hPz + W.a₃ * div_self (pow_ne_zero 3 hPz)

variable (W') in
/-- The partial derivative `W_Z(X, Y, Z)` with respect to `Z` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates. -/
noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  pderiv z W'.polynomial

lemma polynomialZ_eq : W'.polynomialZ = C W'.a₁ * X * Y + C (3 * W'.a₃) * Y * Z ^ 2 -
    (C (2 * W'.a₂) * X ^ 2 * Z + C (4 * W'.a₄) * X * Z ^ 3 + C (6 * W'.a₆) * Z ^ 5) := by
  rw [polynomialZ, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialZ (P : Fin 3 → R) : eval P W'.polynomialZ =
    W'.a₁ * P x * P y + 3 * W'.a₃ * P y * P z ^ 2 -
      (2 * W'.a₂ * P x ^ 2 * P z + 4 * W'.a₄ * P x * P z ^ 3 + 6 * W'.a₆ * P z ^ 5) := by
  rw [polynomialZ_eq]
  simp

/-- Euler's homogeneous function theorem in Jacobian coordinates. -/
theorem polynomial_relation (P : Fin 3 → R) : 6 * eval P W'.polynomial =
    2 * P x * eval P W'.polynomialX + 3 * P y * eval P W'.polynomialY +
      P z * eval P W'.polynomialZ := by
  rw [eval_polynomial, eval_polynomialX, eval_polynomialY, eval_polynomialZ]
  ring1

variable (W') in
/-- The proposition that a Jacobian point representative `(x, y, z)` on a Weierstrass curve `W` is
nonsingular.

In other words, either `W_X(x, y, z) ≠ 0`, `W_Y(x, y, z) ≠ 0`, or `W_Z(x, y, z) ≠ 0`.

Note that this definition is only mathematically accurate for fields. -/
-- TODO: generalise this definition to be mathematically accurate for a larger class of rings.
def Nonsingular (P : Fin 3 → R) : Prop :=
  W'.Equation P ∧
    (eval P W'.polynomialX ≠ 0 ∨ eval P W'.polynomialY ≠ 0 ∨ eval P W'.polynomialZ ≠ 0)

lemma nonsingular_iff (P : Fin 3 → R) : W'.Nonsingular P ↔ W'.Equation P ∧
    (W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z ^ 2 + W'.a₄ * P z ^ 4) ≠ 0 ∨
      2 * P y + W'.a₁ * P x * P z + W'.a₃ * P z ^ 3 ≠ 0 ∨
      W'.a₁ * P x * P y + 3 * W'.a₃ * P y * P z ^ 2
        - (2 * W'.a₂ * P x ^ 2 * P z + 4 * W'.a₄ * P x * P z ^ 3 + 6 * W'.a₆ * P z ^ 5) ≠ 0) := by
  rw [Nonsingular, eval_polynomialX, eval_polynomialY, eval_polynomialZ]

lemma nonsingular_smul (P : Fin 3 → R) {u : R} (hu : IsUnit u) :
    W'.Nonsingular (u • P) ↔ W'.Nonsingular P :=
  have hP {u : R} (hu : IsUnit u) {P : Fin 3 → R} (hP : W'.Nonsingular <| u • P) :
      W'.Nonsingular P := by
    rcases (nonsingular_iff _).mp hP with ⟨hP, hP'⟩
    refine (nonsingular_iff P).mpr ⟨(equation_smul P hu).mp hP, ?_⟩
    contrapose! hP'
    simp only [smul_fin3_ext]
    exact ⟨by linear_combination (norm := ring1) u ^ 4 * hP'.left,
      by linear_combination (norm := ring1) u ^ 3 * hP'.right.left,
      by linear_combination (norm := ring1) u ^ 5 * hP'.right.right⟩
  ⟨hP hu, fun h => hP hu.unit⁻¹.isUnit <| by rwa [smul_smul, hu.val_inv_mul, one_smul]⟩

lemma nonsingular_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.Nonsingular P ↔ W'.Nonsingular Q := by
  rcases h with ⟨u, rfl⟩
  exact nonsingular_smul Q u.isUnit

lemma nonsingular_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) :
    W'.Nonsingular P ↔ W'.Equation P ∧ (3 * P x ^ 2 ≠ 0 ∨ 2 * P y ≠ 0 ∨ W'.a₁ * P x * P y ≠ 0) := by
  simp only [nonsingular_iff, hPz, add_zero, sub_zero, zero_sub, mul_zero,
    zero_pow <| OfNat.ofNat_ne_zero _, neg_ne_zero]

lemma nonsingular_zero [Nontrivial R] : W'.Nonsingular ![1, 1, 0] := by
  simp only [nonsingular_of_Z_eq_zero, equation_zero, true_and, fin3_def_ext, ← not_and_or]
  exact fun h => one_ne_zero <| by linear_combination (norm := ring1) h.1 - h.2.1

lemma nonsingular_some (a b : R) : W'.Nonsingular ![a, b, 1] ↔ W'.toAffine.Nonsingular a b := by
  simp_rw [nonsingular_iff, equation_some, fin3_def_ext, Affine.nonsingular_iff',
    Affine.equation_iff', and_congr_right_iff, ← not_and_or, not_iff_not, one_pow, mul_one,
    and_congr_right_iff, Iff.comm, iff_self_and]
  intro h ha hb
  linear_combination (norm := ring1) 6 * h - 2 * a * ha - 3 * b * hb

lemma nonsingular_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.toAffine.Nonsingular (P x / P z ^ 2) (P y / P z ^ 3) :=
  (nonsingular_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| nonsingular_some ..

lemma nonsingular_iff_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.Equation P ∧ (eval P W.polynomialX ≠ 0 ∨ eval P W.polynomialY ≠ 0) := by
  rw [nonsingular_of_Z_ne_zero hPz, Affine.Nonsingular, ← equation_of_Z_ne_zero hPz,
    ← eval_polynomialX_of_Z_ne_zero hPz, div_ne_zero_iff, and_iff_left <| pow_ne_zero 4 hPz,
    ← eval_polynomialY_of_Z_ne_zero hPz, div_ne_zero_iff, and_iff_left <| pow_ne_zero 3 hPz]

lemma X_ne_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Nonsingular P)
    (hPz : P z = 0) : P x ≠ 0 := by
  intro hPx
  simp only [nonsingular_of_Z_eq_zero hPz, equation_of_Z_eq_zero hPz, hPx, mul_zero, zero_mul,
    zero_pow <| OfNat.ofNat_ne_zero _, ne_self_iff_false, or_false, false_or] at hP
  rwa [pow_eq_zero_iff two_ne_zero, hP.left, eq_self, true_and, mul_zero, ne_self_iff_false] at hP

lemma isUnit_X_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P x) :=
  (X_ne_zero_of_Z_eq_zero hP hPz).isUnit

lemma Y_ne_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Nonsingular P)
    (hPz : P z = 0) : P y ≠ 0 := by
  have hPx : P x ≠ 0 := X_ne_zero_of_Z_eq_zero hP hPz
  intro hPy
  rw [nonsingular_of_Z_eq_zero hPz, equation_of_Z_eq_zero hPz, hPy, zero_pow two_ne_zero] at hP
  exact hPx <| pow_eq_zero hP.left.symm

lemma isUnit_Y_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P y) :=
  (Y_ne_zero_of_Z_eq_zero hP hPz).isUnit

lemma equiv_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : P ≈ Q := by
  have hPx : IsUnit <| P x := isUnit_X_of_Z_eq_zero hP hPz
  have hPy : IsUnit <| P y := isUnit_Y_of_Z_eq_zero hP hPz
  have hQx : IsUnit <| Q x := isUnit_X_of_Z_eq_zero hQ hQz
  have hQy : IsUnit <| Q y := isUnit_Y_of_Z_eq_zero hQ hQz
  simp only [nonsingular_of_Z_eq_zero, equation_of_Z_eq_zero, hPz, hQz] at hP hQ
  use (hPy.unit / hPx.unit) * (hQx.unit / hQy.unit)
  simp only [Units.smul_def, smul_fin3, Units.val_mul, Units.val_div_eq_div_val, IsUnit.unit_spec,
    mul_pow, div_pow, hQz, mul_zero]
  conv_rhs => rw [← fin3_def P, hPz]
  congr! 2
  · rw [hP.left, pow_succ, (hPx.pow 2).mul_div_cancel_left, hQ.left, pow_succ _ 2,
      (hQx.pow 2).div_mul_cancel_left, hQx.inv_mul_cancel_right]
  · rw [← hP.left, pow_succ, (hPy.pow 2).mul_div_cancel_left, ← hQ.left, pow_succ _ 2,
      (hQy.pow 2).div_mul_cancel_left, hQy.inv_mul_cancel_right]

lemma equiv_zero_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    P ≈ ![1, 1, 0] :=
  equiv_of_Z_eq_zero hP nonsingular_zero hPz rfl

lemma comp_equiv_comp (f : F →+* K) {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : f ∘ P ≈ f ∘ Q ↔ P ≈ Q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hz : f (P z) = 0
    · exact equiv_of_Z_eq_zero hP hQ ((map_eq_zero_iff f f.injective).mp hz) <|
        (map_eq_zero_iff f f.injective).mp <| (Z_eq_zero_of_equiv h).mp hz
    · refine equiv_of_X_eq_of_Y_eq ((map_ne_zero_iff f f.injective).mp hz)
        ((map_ne_zero_iff f f.injective).mp <| hz.comp (Z_eq_zero_of_equiv h).mpr) ?_ ?_
      all_goals apply f.injective; map_simp
      exacts [X_eq_of_equiv h, Y_eq_of_equiv h]
  · rcases h with ⟨u, rfl⟩
    exact ⟨Units.map f u, (comp_smul ..).symm⟩

variable (W') in
/-- The proposition that a Jacobian point class on a Weierstrass curve `W` is nonsingular.

If `P` is a Jacobian point representative on `W`, then `W.NonsingularLift ⟦P⟧` is definitionally
equivalent to `W.Nonsingular P`.

Note that this definition is only mathematically accurate for fields. -/
def NonsingularLift (P : PointClass R) : Prop :=
  P.lift W'.Nonsingular fun _ _ => propext ∘ nonsingular_of_equiv

lemma nonsingularLift_iff (P : Fin 3 → R) : W'.NonsingularLift ⟦P⟧ ↔ W'.Nonsingular P :=
  Iff.rfl

lemma nonsingularLift_zero [Nontrivial R] : W'.NonsingularLift ⟦![1, 1, 0]⟧ :=
  nonsingular_zero

lemma nonsingularLift_some (a b : R) :
    W'.NonsingularLift ⟦![a, b, 1]⟧ ↔ W'.toAffine.Nonsingular a b :=
  nonsingular_some a b

/-! ## Maps and base changes -/

variable (f : R →+* S) (P : Fin 3 → R)

@[simp]
lemma map_polynomial : (W'.map f).toJacobian.polynomial = MvPolynomial.map f W'.polynomial := by
  simp only [polynomial]
  map_simp

variable {P} in
lemma Equation.map (h : W'.Equation P) : (W'.map f).toJacobian.Equation (f ∘ P) := by
  rw [Equation, map_polynomial, eval_map, ← eval₂_comp, h, map_zero]

variable {f} in
@[simp]
lemma map_equation (hf : Function.Injective f) :
    (W'.map f).toJacobian.Equation (f ∘ P) ↔ W'.Equation P := by
  simp only [Equation, map_polynomial, eval_map, ← eval₂_comp, map_eq_zero_iff f hf]

@[simp]
lemma map_polynomialX : (W'.map f).toJacobian.polynomialX = MvPolynomial.map f W'.polynomialX := by
  simp only [polynomialX, map_polynomial, pderiv_map]

@[simp]
lemma map_polynomialY : (W'.map f).toJacobian.polynomialY = MvPolynomial.map f W'.polynomialY := by
  simp only [polynomialY, map_polynomial, pderiv_map]

@[simp]
lemma map_polynomialZ : (W'.map f).toJacobian.polynomialZ = MvPolynomial.map f W'.polynomialZ := by
  simp only [polynomialZ, map_polynomial, pderiv_map]

variable {f} in
@[simp]
lemma map_nonsingular (hf : Function.Injective f) :
    (W'.map f).toJacobian.Nonsingular (f ∘ P) ↔ W'.Nonsingular P := by
  simp only [Nonsingular, map_equation P hf, map_polynomialX, map_polynomialY, map_polynomialZ,
    eval_map, ← eval₂_comp, map_ne_zero_iff f hf]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A →ₐ[S] B) (P : Fin 3 → A)

lemma baseChange_polynomial : (W'.baseChange B).toJacobian.polynomial =
    MvPolynomial.map f (W'.baseChange A).toJacobian.polynomial := by
  rw [← map_polynomial, map_baseChange]

variable {P} in
lemma Equation.baseChange (h : (W'.baseChange A).toJacobian.Equation P) :
    (W'.baseChange B).toJacobian.Equation (f ∘ P) := by
  convert Equation.map f.toRingHom h using 1
  rw [AlgHom.toRingHom_eq_coe, map_baseChange]

variable {f} in
lemma baseChange_equation (hf : Function.Injective f) :
    (W'.baseChange B).toJacobian.Equation (f ∘ P) ↔ (W'.baseChange A).toJacobian.Equation P := by
  rw [← RingHom.coe_coe, ← map_equation P hf, AlgHom.toRingHom_eq_coe, map_baseChange]

lemma baseChange_polynomialX : (W'.baseChange B).toJacobian.polynomialX =
    MvPolynomial.map f (W'.baseChange A).toJacobian.polynomialX := by
  rw [← map_polynomialX, map_baseChange]

lemma baseChange_polynomialY : (W'.baseChange B).toJacobian.polynomialY =
    MvPolynomial.map f (W'.baseChange A).toJacobian.polynomialY := by
  rw [← map_polynomialY, map_baseChange]

lemma baseChange_polynomialZ : (W'.baseChange B).toJacobian.polynomialZ =
    MvPolynomial.map f (W'.baseChange A).toJacobian.polynomialZ := by
  rw [← map_polynomialZ, map_baseChange]

variable {f} in
lemma baseChange_nonsingular (hf : Function.Injective f) :
    (W'.baseChange B).toJacobian.Nonsingular (f ∘ P) ↔
      (W'.baseChange A).toJacobian.Nonsingular P := by
  rw [← RingHom.coe_coe, ← map_nonsingular P hf, AlgHom.toRingHom_eq_coe, map_baseChange]

end Jacobian

end WeierstrassCurve
