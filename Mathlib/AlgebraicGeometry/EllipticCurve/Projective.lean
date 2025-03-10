/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Tactic.LinearCombination'

/-!
# Projective coordinates for Weierstrass curves

This file defines the type of points on a Weierstrass curve as a tuple, consisting of an equivalence
class of triples up to scaling by a unit, satisfying a Weierstrass equation with a nonsingular
condition. This file also defines the negation and addition operations of the group law for this
type, and proves that they respect the Weierstrass equation and the nonsingular condition. The fact
that they form an abelian group is proven in `Mathlib/AlgebraicGeometry/EllipticCurve/Group.lean`.

## Mathematical background

A point on the unweighted projective plane over a commutative ring `R` is an equivalence class
`[x : y : z]` of triples `(x, y, z) ≠ (0, 0, 0)` of elements in `R` such that
`(x, y, z) ∼ (x', y', z')` if there is some unit `u` in `Rˣ` with `(x, y, z) = (ux', uy', uz')`.

Let `W` be a Weierstrass curve over a field `F` with coefficients `aᵢ`. A *projective point* is a
point on the unweighted projective plane over `F` satisfying the *homogeneous Weierstrass equation*
`W(X, Y, Z) = 0` in *projective coordinates*, where
`W(X, Y, Z) := Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)`. It is *nonsingular* if its
partial derivatives `W_X(x, y, z)`, `W_Y(x, y, z)`, and `W_Z(x, y, z)` do not vanish simultaneously.

The nonsingular projective points on `W` can be given negation and addition operations defined by an
analogue of the secant-and-tangent process in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine.lean`,
but the polynomials involved are homogeneous, so any instances of division become multiplication in
the `Z`-coordinate. Most computational proofs are immediate from their analogous proofs for affine
coordinates. They can be endowed with an group law, which is uniquely determined by these formulae
and follows from an equivalence with the nonsingular points `W⟮F⟯` in affine coordinates.

## Main definitions

 * `WeierstrassCurve.Projective.PointClass`: the equivalence class of a point representative.
 * `WeierstrassCurve.Projective.Nonsingular`: the nonsingular condition on a point representative.
 * `WeierstrassCurve.Projective.NonsingularLift`: the nonsingular condition on a point class.

 * `WeierstrassCurve.Projective.negY`: the `Y`-coordinate of `-P`.
 * `WeierstrassCurve.Projective.dblZ`: the `Z`-coordinate of `2 • P`.
 * `WeierstrassCurve.Projective.dblX`: the `X`-coordinate of `2 • P`.
 * `WeierstrassCurve.Projective.negDblY`: the `Y`-coordinate of `-(2 • P)`.
 * `WeierstrassCurve.Projective.dblY`: the `Y`-coordinate of `2 • P`.
 * `WeierstrassCurve.Projective.addZ`: the `Z`-coordinate of `P + Q`.
 * `WeierstrassCurve.Projective.addX`: the `X`-coordinate of `P + Q`.
 * `WeierstrassCurve.Projective.negAddY`: the `Y`-coordinate of `-(P + Q)`.
 * `WeierstrassCurve.Projective.addY`: the `Y`-coordinate of `P + Q`.

 * `WeierstrassCurve.Projective.neg`: the negation of a point representative.
 * `WeierstrassCurve.Projective.negMap`: the negation of a point class.
 * `WeierstrassCurve.Projective.add`: the addition of two point representatives.
 * `WeierstrassCurve.Projective.addMap`: the addition of two point classes.
 * `WeierstrassCurve.Projective.Point`: a nonsingular projective point.
 * `WeierstrassCurve.Projective.Point.neg`: the negation of a nonsingular projective point.
 * `WeierstrassCurve.Projective.Point.add`: the addition of two nonsingular projective points.
 * `WeierstrassCurve.Projective.Point.toAffineAddEquiv`: the equivalence between the type of
    nonsingular projective points with the type of nonsingular points `W⟮F⟯` in affine coordinates.

## Main statements

 * `WeierstrassCurve.Projective.polynomial_relation`: Euler's homogeneous function theorem.

 * `WeierstrassCurve.Projective.nonsingular_neg`: negation preserves the nonsingular condition.
 * `WeierstrassCurve.Projective.nonsingular_add`: addition preserves the nonsingular condition.

## Implementation notes

All definitions and lemmas for Weierstrass curves in projective coordinates live in the namespace
`WeierstrassCurve.Projective` to distinguish them from those in other coordinates. This is simply an
abbreviation for `WeierstrassCurve` that can be converted using `WeierstrassCurve.toProjective`.
This can be converted into `WeierstrassCurve.Affine` using `WeierstrassCurve.Projective.toAffine`.
A nonsingular projective point representative can be converted to a nonsingular point in affine
coordinates using `WeiestrassCurve.Projective.Point.toAffine`, which lifts to a map on nonsingular
projective points using `WeiestrassCurve.Projective.Point.toAffineLift`. Conversely, a nonsingular
point in affine coordinates can be converted to a nonsingular projective point using
`WeierstrassCurve.Projective.Point.fromAffine` or `WeierstrassCurve.Affine.Point.toProjective`.

A point representative is implemented as a term `P` of type `Fin 3 → R`, which allows for the vector
notation `![x, y, z]`. However, `P` is not definitionally equivalent to the expanded vector
`![P x, P y, P z]`, so the lemmas `fin3_def` and `fin3_def_ext` can be used to convert between the
two forms. The equivalence of two point representatives `P` and `Q` is implemented as an equivalence
of orbits of the action of `Rˣ`, or equivalently that there is some unit `u` of `R` such that
`P = u • Q`. However, `u • Q` is not definitionally equal to `![u * Q x, u * Q y, u * Q z]`, so the
lemmas `smul_fin3` and `smul_fin3_ext` can be used to convert between the two forms.
This file makes extensive use of `erw` to get around this problem.
While `erw` is often an indication of a problem, in this case it is self-contained and should not
cause any issues. It would alternatively be possible to add some automation to assist here.
Note that `W(X, Y, Z)` and its partial derivatives are independent of the point representative, and
the nonsingularity condition already implies `(x, y, z) ≠ (0, 0, 0)`, so a nonsingular projective
point on `W` can be given by `[x : y : z]` and the nonsingular condition on any representative.

The definitions of `WeierstrassCurve.Projective.dblX`, `WeierstrassCurve.Projective.negDblY`,
`WeierstrassCurve.Projective.addZ`, `WeierstrassCurve.Projective.addX`, and
`WeierstrassCurve.Projective.negAddY` are given explicitly by large polynomials that are homogeneous
of degree `4`. Clearing the denominators of their corresponding affine rational functions in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine.lean` would give polynomials that are
homogeneous of degrees `5`, `6`, `6`, `8`, and `8` respectively, so their actual definitions are off
by powers of certain polynomial factors that are homogeneous of degree `1` or `2`. These factors
divide their corresponding affine polynomials only modulo the homogeneous Weierstrass equation, so
their large quotient polynomials are calculated explicitly in a computer algebra system. All of this
is done to ensure that the definitions of both `WeierstrassCurve.Projective.dblXYZ` and
`WeierstrassCurve.Projective.addXYZ` are homogeneous of degree `4`.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, rational point, projective coordinates
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

/-! ## Weierstrass curves -/

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v}

variable (R) in
/-- An abbreviation for a Weierstrass curve in projective coordinates. -/
abbrev Projective : Type r :=
  WeierstrassCurve R

/-- The conversion from a Weierstrass curve to projective coordinates. -/
abbrev toProjective (W : WeierstrassCurve R) : Projective R :=
  W

namespace Projective

variable (W') in
/-- The conversion from a Weierstrass curve in projective coordinates to affine coordinates. -/
abbrev toAffine : Affine R :=
  W'

lemma fin3_def (P : Fin 3 → R) : ![P x, P y, P z] = P := by
  ext n; fin_cases n <;> rfl

lemma fin3_def_ext (X Y Z : R) : ![X, Y, Z] x = X ∧ ![X, Y, Z] y = Y ∧ ![X, Y, Z] z = Z :=
  ⟨rfl, rfl, rfl⟩

lemma comp_fin3 (f : R → S) (X Y Z : R) : f ∘ ![X, Y, Z] = ![f X, f Y, f Z] :=
  (FinVec.map_eq ..).symm

variable [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Field F] [Field K] {W' : Projective R}
  {W : Projective F}

section Projective

/-! ### Projective coordinates -/

lemma smul_fin3 (P : Fin 3 → R) (u : R) : u • P = ![u * P x, u * P y, u * P z] := by
  simp [← List.ofFn_inj]

lemma smul_fin3_ext (P : Fin 3 → R) (u : R) :
    (u • P) x = u * P x ∧ (u • P) y = u * P y ∧ (u • P) z = u * P z :=
  ⟨rfl, rfl, rfl⟩

lemma comp_smul (f : R →+* S) (P : Fin 3 → R) (u : R) : f ∘ (u • P) = f u • f ∘ P := by
  ext n; fin_cases n <;> simp only [smul_fin3, comp_fin3] <;> map_simp

/-- The equivalence setoid for a projective point representative on a Weierstrass curve. -/
scoped instance instSetoidPoint : Setoid <| Fin 3 → R :=
  MulAction.orbitRel Rˣ <| Fin 3 → R

variable (R) in
/-- The equivalence class of a projective point representative on a Weierstrass curve. -/
abbrev PointClass : Type r :=
  MulAction.orbitRel.Quotient Rˣ <| Fin 3 → R

lemma smul_equiv (P : Fin 3 → R) {u : R} (hu : IsUnit u) : u • P ≈ P :=
  ⟨hu.unit, rfl⟩

@[simp]
lemma smul_eq (P : Fin 3 → R) {u : R} (hu : IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧ :=
  Quotient.eq.mpr <| smul_equiv P hu

lemma smul_equiv_smul (P Q : Fin 3 → R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    u • P ≈ v • Q ↔ P ≈ Q := by
  erw [← Quotient.eq_iff_equiv, ← Quotient.eq_iff_equiv, smul_eq P hu, smul_eq Q hv]
  rfl

lemma equiv_iff_eq_of_Z_eq' {P Q : Fin 3 → R} (hz : P z = Q z) (mem : Q z ∈ nonZeroDivisors R) :
    P ≈ Q ↔ P = Q := by
  refine ⟨?_, by rintro rfl; exact Setoid.refl _⟩
  rintro ⟨u, rfl⟩
  rw [← one_mul (Q z)] at hz
  simp_rw [Units.smul_def, (mul_cancel_right_mem_nonZeroDivisors mem).mp hz, one_smul]

lemma equiv_iff_eq_of_Z_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hz : P z = Q z) (hQz : Q z ≠ 0) :
    P ≈ Q ↔ P = Q :=
  equiv_iff_eq_of_Z_eq' hz (mem_nonZeroDivisors_of_ne_zero hQz)

lemma Z_eq_zero_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P z = 0 ↔ Q z = 0 := by
  rcases h with ⟨_, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext, Units.mul_right_eq_zero]

lemma X_eq_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P x * Q z = Q x * P z := by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

lemma Y_eq_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : P y * Q z = Q y * P z := by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

lemma not_equiv_of_Z_eq_zero_left {P Q : Fin 3 → R} (hPz : P z = 0) (hQz : Q z ≠ 0) : ¬P ≈ Q :=
  fun h => hQz <| (Z_eq_zero_of_equiv h).mp hPz

lemma not_equiv_of_Z_eq_zero_right {P Q : Fin 3 → R} (hPz : P z ≠ 0) (hQz : Q z = 0) : ¬P ≈ Q :=
  fun h => hPz <| (Z_eq_zero_of_equiv h).mpr hQz

lemma not_equiv_of_X_ne {P Q : Fin 3 → R} (hx : P x * Q z ≠ Q x * P z) : ¬P ≈ Q :=
  hx.comp X_eq_of_equiv

lemma not_equiv_of_Y_ne {P Q : Fin 3 → R} (hy : P y * Q z ≠ Q y * P z) : ¬P ≈ Q :=
  hy.comp Y_eq_of_equiv

lemma equiv_of_X_eq_of_Y_eq {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) : P ≈ Q := by
  use Units.mk0 _ hPz / Units.mk0 _ hQz
  simp only [Units.smul_def, smul_fin3, Units.val_div_eq_div_val, Units.val_mk0, mul_comm, mul_div,
    ← hx, ← hy, mul_div_cancel_right₀ _ hQz, fin3_def]

lemma equiv_some_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) : P ≈ ![P x / P z, P y / P z, 1] :=
  equiv_of_X_eq_of_Y_eq hPz one_ne_zero
    (by linear_combination (norm := (matrix_simp; ring1)) -P x * div_self hPz)
    (by linear_combination (norm := (matrix_simp; ring1)) -P y * div_self hPz)

lemma X_eq_iff {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P x * Q z = Q x * P z ↔ P x / P z = Q x / Q z :=
  (div_eq_div_iff hPz hQz).symm

lemma Y_eq_iff {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P y * Q z = Q y * P z ↔ P y / P z = Q y / Q z :=
  (div_eq_div_iff hPz hQz).symm

end Projective

section Equation

/-! ### Weierstrass equations -/

variable (W') in
/-- The polynomial `W(X, Y, Z) := Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)` associated to a
Weierstrass curve `W` over a ring `R` in projective coordinates.

This is represented as a term of type `MvPolynomial (Fin 3) R`, where `X 0`, `X 1`, and `X 2`
represent `X`, `Y`, and `Z` respectively. -/
noncomputable def polynomial : MvPolynomial (Fin 3) R :=
  X 1 ^ 2 * X 2 + C W'.a₁ * X 0 * X 1 * X 2 + C W'.a₃ * X 1 * X 2 ^ 2
    - (X 0 ^ 3 + C W'.a₂ * X 0 ^ 2 * X 2 + C W'.a₄ * X 0 * X 2 ^ 2 + C W'.a₆ * X 2 ^ 3)

lemma eval_polynomial (P : Fin 3 → R) : eval P W'.polynomial =
    P y ^ 2 * P z + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 2
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z + W'.a₄ * P x * P z ^ 2 + W'.a₆ * P z ^ 3) := by
  rw [polynomial]
  eval_simp

lemma eval_polynomial_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) : eval P W.polynomial / P z ^ 3 =
    W.toAffine.polynomial.evalEval (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [eval_polynomial, Affine.evalEval_polynomial]; ring1))
    P y ^ 2 / P z ^ 2 * div_self hPz + W.a₁ * P x * P y / P z ^ 2 * div_self hPz
      + W.a₃ * P y / P z * div_self (pow_ne_zero 2 hPz) - W.a₂ * P x ^ 2 / P z ^ 2 * div_self hPz
      - W.a₄ * P x / P z * div_self (pow_ne_zero 2 hPz) - W.a₆ * div_self (pow_ne_zero 3 hPz)

variable (W') in
/-- The proposition that a projective point representative `(x, y, z)` lies in a Weierstrass curve
`W`.

In other words, it satisfies the homogeneous Weierstrass equation `W(X, Y, Z) = 0`. -/
def Equation (P : Fin 3 → R) : Prop :=
  eval P W'.polynomial = 0

lemma equation_iff (P : Fin 3 → R) : W'.Equation P ↔
    P y ^ 2 * P z + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 2
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z + W'.a₄ * P x * P z ^ 2 + W'.a₆ * P z ^ 3) = 0 := by
  rw [Equation, eval_polynomial, sub_eq_zero]

lemma equation_smul (P : Fin 3 → R) {u : R} (hu : IsUnit u) : W'.Equation (u • P) ↔ W'.Equation P :=
  have hP (u : R) {P : Fin 3 → R} (hP : W'.Equation P) : W'.Equation <| u • P := by
    rw [equation_iff] at hP ⊢
    linear_combination (norm := (simp only [smul_fin3_ext]; ring1)) u ^ 3 * hP
  ⟨fun h => by convert hP ↑hu.unit⁻¹ h; rw [smul_smul, hu.val_inv_mul, one_smul], hP u⟩

lemma equation_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.Equation P ↔ W'.Equation Q := by
  rcases h with ⟨u, rfl⟩
  exact equation_smul Q u.isUnit

lemma equation_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) : W'.Equation P ↔ P x ^ 3 = 0 := by
  simp only [equation_iff, hPz, add_zero, zero_sub, mul_zero, zero_pow <| OfNat.ofNat_ne_zero _,
    neg_eq_zero]

lemma equation_zero : W'.Equation ![0, 1, 0] := by
  simp only [equation_of_Z_eq_zero, fin3_def_ext, zero_pow three_ne_zero]

lemma equation_some (X Y : R) : W'.Equation ![X, Y, 1] ↔ W'.toAffine.Equation X Y := by
  simp only [equation_iff, Affine.equation_iff', fin3_def_ext, one_pow, mul_one]

lemma equation_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Equation P ↔ W.toAffine.Equation (P x / P z) (P y / P z) :=
  (equation_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| equation_some ..

lemma X_eq_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : P x = 0 :=
  pow_eq_zero <| (equation_of_Z_eq_zero hPz).mp hP

end Equation

section Nonsingular

/-! ### Nonsingular Weierstrass equations -/

variable (W') in
/-- The partial derivative `W_X(X, Y, Z)` with respect to `X` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in projective coordinates. -/
noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  pderiv x W'.polynomial

lemma polynomialX_eq : W'.polynomialX =
    C W'.a₁ * X 1 * X 2 - (C 3 * X 0 ^ 2 + C (2 * W'.a₂) * X 0 * X 2 + C W'.a₄ * X 2 ^ 2) := by
  rw [polynomialX, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialX (P : Fin 3 → R) : eval P W'.polynomialX =
    W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z + W'.a₄ * P z ^ 2) := by
  rw [polynomialX_eq]
  eval_simp

lemma eval_polynomialX_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    eval P W.polynomialX / P z ^ 2 = W.toAffine.polynomialX.evalEval (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [eval_polynomialX, Affine.evalEval_polynomialX]; ring1))
    W.a₁ * P y / P z * div_self hPz - 2 * W.a₂ * P x / P z * div_self hPz
      - W.a₄ * div_self (pow_ne_zero 2 hPz)

variable (W') in
/-- The partial derivative `W_Y(X, Y, Z)` with respect to `Y` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in projective coordinates. -/
noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  pderiv y W'.polynomial

lemma polynomialY_eq : W'.polynomialY =
    C 2 * X 1 * X 2 + C W'.a₁ * X 0 * X 2 + C W'.a₃ * X 2 ^ 2 := by
  rw [polynomialY, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialY (P : Fin 3 → R) :
    eval P W'.polynomialY = 2 * P y * P z + W'.a₁ * P x * P z + W'.a₃ * P z ^ 2 := by
  rw [polynomialY_eq]
  eval_simp

lemma eval_polynomialY_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    eval P W.polynomialY / P z ^ 2 = W.toAffine.polynomialY.evalEval (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [eval_polynomialY, Affine.evalEval_polynomialY]; ring1))
    2 * P y / P z * div_self hPz + W.a₁ * P x / P z * div_self hPz
      + W.a₃ * div_self (pow_ne_zero 2 hPz)

variable (W') in
/-- The partial derivative `W_Z(X, Y, Z)` with respect to `Z` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in projective coordinates. -/
noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  pderiv z W'.polynomial

lemma polynomialZ_eq : W'.polynomialZ =
    X 1 ^ 2 + C W'.a₁ * X 0 * X 1 + C (2 * W'.a₃) * X 1 * X 2
      - (C W'.a₂ * X 0 ^ 2 + C (2 * W'.a₄) * X 0 * X 2 + C (3 * W'.a₆) * X 2 ^ 2) := by
  rw [polynomialZ, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialZ (P : Fin 3 → R) : eval P W'.polynomialZ =
    P y ^ 2 + W'.a₁ * P x * P y + 2 * W'.a₃ * P y * P z
      - (W'.a₂ * P x ^ 2 + 2 * W'.a₄ * P x * P z + 3 * W'.a₆ * P z ^ 2) := by
  rw [polynomialZ_eq]
  eval_simp

/-- Euler's homogeneous function theorem in projective coordinates. -/
theorem polynomial_relation (P : Fin 3 → R) : 3 * eval P W'.polynomial =
    P x * eval P W'.polynomialX + P y * eval P W'.polynomialY + P z * eval P W'.polynomialZ := by
  rw [eval_polynomial, eval_polynomialX, eval_polynomialY, eval_polynomialZ]
  ring1

variable (W') in
/-- The proposition that a projective point representative `(x, y, z)` on a Weierstrass curve `W` is
nonsingular.

In other words, either `W_X(x, y, z) ≠ 0`, `W_Y(x, y, z) ≠ 0`, or `W_Z(x, y, z) ≠ 0`.

Note that this definition is only mathematically accurate for fields. -/
-- TODO: generalise this definition to be mathematically accurate for a larger class of rings.
def Nonsingular (P : Fin 3 → R) : Prop :=
  W'.Equation P ∧
    (eval P W'.polynomialX ≠ 0 ∨ eval P W'.polynomialY ≠ 0 ∨ eval P W'.polynomialZ ≠ 0)

lemma nonsingular_iff (P : Fin 3 → R) : W'.Nonsingular P ↔ W'.Equation P ∧
    (W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z + W'.a₄ * P z ^ 2) ≠ 0 ∨
      2 * P y * P z + W'.a₁ * P x * P z + W'.a₃ * P z ^ 2 ≠ 0 ∨
      P y ^ 2 + W'.a₁ * P x * P y + 2 * W'.a₃ * P y * P z
        - (W'.a₂ * P x ^ 2 + 2 * W'.a₄ * P x * P z + 3 * W'.a₆ * P z ^ 2) ≠ 0) := by
  rw [Nonsingular, eval_polynomialX, eval_polynomialY, eval_polynomialZ]

lemma nonsingular_smul (P : Fin 3 → R) {u : R} (hu : IsUnit u) :
    W'.Nonsingular (u • P) ↔ W'.Nonsingular P :=
  have hP {u : R} (hu : IsUnit u) {P : Fin 3 → R} (hP : W'.Nonsingular <| u • P) :
      W'.Nonsingular P := by
    rcases (nonsingular_iff _).mp hP with ⟨hP, hP'⟩
    refine (nonsingular_iff P).mpr ⟨(equation_smul P hu).mp hP, ?_⟩
    contrapose! hP'
    simp only [smul_fin3_ext]
    exact ⟨by linear_combination (norm := ring1) u ^ 2 * hP'.left,
      by linear_combination (norm := ring1) u ^ 2 * hP'.right.left,
      by linear_combination (norm := ring1) u ^ 2 * hP'.right.right⟩
  ⟨hP hu, fun h => hP hu.unit⁻¹.isUnit <| by rwa [smul_smul, hu.val_inv_mul, one_smul]⟩

lemma nonsingular_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.Nonsingular P ↔ W'.Nonsingular Q := by
  rcases h with ⟨u, rfl⟩
  exact nonsingular_smul Q u.isUnit

lemma nonsingular_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) :
    W'.Nonsingular P ↔
      W'.Equation P ∧ (3 * P x ^ 2 ≠ 0 ∨ P y ^ 2 + W'.a₁ * P x * P y - W'.a₂ * P x ^ 2 ≠ 0) := by
  simp only [nonsingular_iff, hPz, add_zero, sub_zero, zero_sub, mul_zero,
    zero_pow <| OfNat.ofNat_ne_zero _, neg_ne_zero, ne_self_iff_false, false_or]

lemma nonsingular_zero [Nontrivial R] : W'.Nonsingular ![0, 1, 0] := by
  simp only [nonsingular_of_Z_eq_zero, equation_zero, true_and, fin3_def_ext, ← not_and_or]
  exact fun h => one_ne_zero <| by linear_combination (norm := ring1) h.right

lemma nonsingular_some (X Y : R) : W'.Nonsingular ![X, Y, 1] ↔ W'.toAffine.Nonsingular X Y := by
  simp_rw [nonsingular_iff, equation_some, fin3_def_ext, Affine.nonsingular_iff',
    Affine.equation_iff', and_congr_right_iff, ← not_and_or, not_iff_not, one_pow, mul_one,
    and_congr_right_iff, Iff.comm, iff_self_and]
  intro h hX hY
  linear_combination (norm := ring1) 3 * h - X * hX - Y * hY

lemma nonsingular_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.toAffine.Nonsingular (P x / P z) (P y / P z) :=
  (nonsingular_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| nonsingular_some ..

lemma nonsingular_iff_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.Equation P ∧ (eval P W.polynomialX ≠ 0 ∨ eval P W.polynomialY ≠ 0) := by
  rw [nonsingular_of_Z_ne_zero hPz, Affine.Nonsingular, ← equation_of_Z_ne_zero hPz,
    ← eval_polynomialX_of_Z_ne_zero hPz, div_ne_zero_iff, and_iff_left <| pow_ne_zero 2 hPz,
    ← eval_polynomialY_of_Z_ne_zero hPz, div_ne_zero_iff, and_iff_left <| pow_ne_zero 2 hPz]

lemma Y_ne_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Nonsingular P)
    (hPz : P z = 0) : P y ≠ 0 := by
  intro hPy
  simp only [nonsingular_of_Z_eq_zero hPz, X_eq_zero_of_Z_eq_zero hP.left hPz, hPy, add_zero,
    sub_zero, mul_zero, zero_pow two_ne_zero, or_self, ne_self_iff_false, and_false] at hP

lemma isUnit_Y_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P y) :=
  (Y_ne_zero_of_Z_eq_zero hP hPz).isUnit

lemma equiv_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : P ≈ Q := by
  use (isUnit_Y_of_Z_eq_zero hP hPz).unit / (isUnit_Y_of_Z_eq_zero hQ hQz).unit
  simp only [Units.smul_def, smul_fin3, X_eq_zero_of_Z_eq_zero hQ.left hQz, hQz, mul_zero,
    Units.val_div_eq_div_val, IsUnit.unit_spec, (isUnit_Y_of_Z_eq_zero hQ hQz).div_mul_cancel]
  conv_rhs => rw [← fin3_def P, X_eq_zero_of_Z_eq_zero hP.left hPz, hPz]

lemma equiv_zero_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    P ≈ ![0, 1, 0] :=
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
/-- The proposition that a projective point class on a Weierstrass curve `W` is nonsingular.

If `P` is a projective point representative on `W`, then `W.NonsingularLift ⟦P⟧` is definitionally
equivalent to `W.Nonsingular P`.

Note that this definition is only mathematically accurate for fields. -/
def NonsingularLift (P : PointClass R) : Prop :=
  P.lift W'.Nonsingular fun _ _ => propext ∘ nonsingular_of_equiv

lemma nonsingularLift_iff (P : Fin 3 → R) : W'.NonsingularLift ⟦P⟧ ↔ W'.Nonsingular P :=
  Iff.rfl

lemma nonsingularLift_zero [Nontrivial R] : W'.NonsingularLift ⟦![0, 1, 0]⟧ :=
  nonsingular_zero

lemma nonsingularLift_some (X Y : R) :
    W'.NonsingularLift ⟦![X, Y, 1]⟧ ↔ W'.toAffine.Nonsingular X Y :=
  nonsingular_some X Y

end Nonsingular

@[deprecated (since := "2024-08-27")] alias equation_smul_iff := equation_smul
@[deprecated (since := "2024-08-27")] alias nonsingularLift_zero' := nonsingularLift_zero
@[deprecated (since := "2024-08-27")]
alias nonsingular_affine_of_Z_ne_zero := nonsingular_of_Z_ne_zero
@[deprecated (since := "2024-08-27")]
alias nonsingular_iff_affine_of_Z_ne_zero := nonsingular_of_Z_ne_zero
@[deprecated (since := "2024-08-27")]
alias nonsingular_of_affine_of_Z_ne_zero := nonsingular_of_Z_ne_zero
@[deprecated (since := "2024-08-27")] alias nonsingular_smul_iff := nonsingular_smul
@[deprecated (since := "2024-08-27")] alias nonsingular_zero' := nonsingular_zero

section Negation

/-! ### Negation formulae -/

variable (W') in
/-- The `Y`-coordinate of a representative of `-P` for a projective point representative `P` on a
Weierstrass curve. -/
def negY (P : Fin 3 → R) : R :=
  -P y - W'.a₁ * P x - W'.a₃ * P z

lemma negY_eq (X Y Z : R) : W'.negY ![X, Y, Z] = -Y - W'.a₁ * X - W'.a₃ * Z :=
  rfl

lemma negY_smul (P : Fin 3 → R) (u : R) : W'.negY (u • P) = u * W'.negY P := by
  simp only [negY, smul_fin3_ext]
  ring1

lemma negY_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.negY P = -P y := by
  rw [negY, hPz, X_eq_zero_of_Z_eq_zero hP hPz, mul_zero, sub_zero, mul_zero, sub_zero]

lemma negY_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.negY P / P z = W.toAffine.negY (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [negY, Affine.negY]; ring1)) -W.a₃ * div_self hPz

lemma Y_sub_Y_mul_Y_sub_negY {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z = Q x * P z) :
    P z * Q z * (P y * Q z - Q y * P z) * (P y * Q z - W'.negY Q * P z) = 0 := by
  linear_combination' (norm := (rw [negY]; ring1)) Q z ^ 3 * (equation_iff P).mp hP
    - P z ^ 3 * (equation_iff Q).mp hQ + hx * hx * hx + W'.a₂ * P z * Q z * hx * hx
    + (W'.a₄ * P z ^ 2 * Q z ^ 2 - W'.a₁ * P y * P z * Q z ^ 2) * hx

lemma Y_eq_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ Q y * P z) :
    P y * Q z = W'.negY Q * P z :=
  sub_eq_zero.mp <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_left <|
    mul_ne_zero (mul_ne_zero hPz hQz) <| sub_ne_zero.mpr hy

lemma Y_eq_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z ≠ W'.negY Q * P z) : P y * Q z = Q y * P z :=
  sub_eq_zero.mp <| (mul_eq_zero.mp <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx
    ).resolve_right <| sub_ne_zero.mpr hy).resolve_left <| mul_ne_zero hPz hQz

lemma Y_eq_iff' {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P y * Q z = W.negY Q * P z ↔ P y / P z = W.toAffine.negY (Q x / Q z) (Q y / Q z) :=
  negY_of_Z_ne_zero hQz ▸ (div_eq_div_iff hPz hQz).symm

lemma Y_sub_Y_add_Y_sub_negY {P Q : Fin 3 → R} (hx : P x * Q z = Q x * P z) :
    (P y * Q z - Q y * P z) + (P y * Q z - W'.negY Q * P z) = (P y - W'.negY P) * Q z := by
  linear_combination (norm := (rw [negY, negY]; ring1)) -W'.a₁ * hx

lemma Y_ne_negY_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z ≠ Q y * P z) : P y ≠ W'.negY P := by
  have hy' : P y * Q z - W'.negY Q * P z = 0 := sub_eq_zero.mpr <| Y_eq_of_Y_ne hP hQ hPz hQz hx hy
  contrapose! hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY hx + Q z * hy - hy'

lemma Y_ne_negY_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z ≠ W'.negY Q * P z) : P y ≠ W'.negY P := by
  have hy' : P y * Q z - Q y * P z = 0 := sub_eq_zero.mpr <| Y_eq_of_Y_ne' hP hQ hPz hQz hx hy
  contrapose! hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY hx + Q z * hy - hy'

lemma Y_eq_negY_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W'.negY Q * P z) :
    P y = W'.negY P :=
  mul_left_injective₀ hQz <| by
    linear_combination (norm := ring1) -Y_sub_Y_add_Y_sub_negY hx + hy + hy'

lemma nonsingular_iff_of_Y_eq_negY {P : Fin 3 → F} (hPz : P z ≠ 0) (hy : P y = W.negY P) :
    W.Nonsingular P ↔ W.Equation P ∧ eval P W.polynomialX ≠ 0 := by
  have hy' : eval P W.polynomialY = (P y - W.negY P) * P z := by rw [negY, eval_polynomialY]; ring1
  rw [nonsingular_iff_of_Z_ne_zero hPz, hy', hy, sub_self, zero_mul, ne_self_iff_false, or_false]

end Negation

section Doubling

/-! ### Doubling formulae -/

variable (W) in
/-- The unit associated to a representative of `2 • P` for a projective point representative `P` on
a Weierstrass curve `W` that is `2`-torsion.

More specifically, the unit `u` such that `W.add P P = u • ![0, 1, 0]` where `P = W.neg P`. -/
noncomputable def dblU (P : Fin 3 → F) : F :=
  eval P W.polynomialX ^ 3 / P z ^ 2

lemma dblU_eq (P : Fin 3 → F) : W.dblU P =
    (W.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W.a₂ * P x * P z + W.a₄ * P z ^ 2)) ^ 3 / P z ^ 2 := by
  rw [dblU, eval_polynomialX]

lemma dblU_smul {P : Fin 3 → F} (hPz : P z ≠ 0) {u : F} (hu : u ≠ 0) :
    W.dblU (u • P) = u ^ 4 * W.dblU P := by
  field_simp [dblU_eq, smul_fin3_ext]
  ring1

lemma dblU_of_Z_eq_zero {P : Fin 3 → F} (hPz : P z = 0) : W.dblU P = 0 := by
  rw [dblU_eq, hPz, zero_pow two_ne_zero, div_zero]

lemma dblU_ne_zero_of_Y_eq {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.dblU P ≠ 0 :=
  div_ne_zero (pow_ne_zero 3
    ((nonsingular_iff_of_Y_eq_negY hPz <| Y_eq_negY_of_Y_eq hQz hx hy hy').mp hP).right) <|
    pow_ne_zero 2 hPz

lemma isUnit_dblU_of_Y_eq {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    IsUnit (W.dblU P) :=
  (dblU_ne_zero_of_Y_eq hP hPz hQz hx hy hy').isUnit

variable (W') in
/-- The `Z`-coordinate of a representative of `2 • P` for a projective point representative `P` on a
Weierstrass curve. -/
def dblZ (P : Fin 3 → R) : R :=
  P z * (P y - W'.negY P) ^ 3

lemma dblZ_smul (P : Fin 3 → R) (u : R) : W'.dblZ (u • P) = u ^ 4 * W'.dblZ P := by
  simp only [dblZ, negY_smul, smul_fin3_ext]
  ring1

lemma dblZ_of_Z_eq_zero {P : Fin 3 → R} (hPz : P z = 0) : W'.dblZ P = 0 := by
  rw [dblZ, hPz, zero_mul]

lemma dblZ_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W'.negY Q * P z) : W'.dblZ P = 0 := by
  rw [dblZ, Y_eq_negY_of_Y_eq hQz hx hy hy', sub_self, zero_pow three_ne_zero, mul_zero]

lemma dblZ_ne_zero_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z ≠ Q y * P z) : W'.dblZ P ≠ 0 :=
  mul_ne_zero hPz <| pow_ne_zero 3 <| sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne hP hQ hPz hQz hx hy

lemma isUnit_dblZ_of_Y_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ Q y * P z) : IsUnit (W.dblZ P) :=
  (dblZ_ne_zero_of_Y_ne hP hQ hPz hQz hx hy).isUnit

lemma dblZ_ne_zero_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z ≠ W'.negY Q * P z) : W'.dblZ P ≠ 0 :=
  mul_ne_zero hPz <| pow_ne_zero 3 <| sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy

lemma isUnit_dblZ_of_Y_ne' {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ W.negY Q * P z) :
    IsUnit (W.dblZ P) :=
  (dblZ_ne_zero_of_Y_ne' hP hQ hPz hQz hx hy).isUnit

private lemma toAffine_slope_of_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ W.negY Q * P z) :
    W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z) =
      -eval P W.polynomialX / P z / (P y - W.negY P) := by
  have hPy : P y - W.negY P ≠ 0 := sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy
  simp only [X_eq_iff hPz hQz, ne_eq, Y_eq_iff' hPz hQz] at hx hy
  rw [Affine.slope_of_Y_ne hx <| negY_of_Z_ne_zero hQz ▸ hy, ← negY_of_Z_ne_zero hPz]
  field_simp [eval_polynomialX, hPz]
  ring1

variable (W') in
/-- The `X`-coordinate of a representative of `2 • P` for a projective point representative `P` on a
Weierstrass curve. -/
noncomputable def dblX (P : Fin 3 → R) : R :=
  2 * P x * P y ^ 3 + 3 * W'.a₁ * P x ^ 2 * P y ^ 2 + 6 * W'.a₂ * P x ^ 3 * P y
    - 8 * W'.a₂ * P y ^ 3 * P z + 9 * W'.a₃ * P x ^ 4 - 6 * W'.a₃ * P x * P y ^ 2 * P z
    - 6 * W'.a₄ * P x ^ 2 * P y * P z - 18 * W'.a₆ * P x * P y * P z ^ 2
    + 3 * W'.a₁ ^ 2 * P x ^ 3 * P y - 2 * W'.a₁ ^ 2 * P y ^ 3 * P z + 3 * W'.a₁ * W'.a₂ * P x ^ 4
    - 12 * W'.a₁ * W'.a₂ * P x * P y ^ 2 * P z - 9 * W'.a₁ * W'.a₃ * P x ^ 2 * P y * P z
    - 3 * W'.a₁ * W'.a₄ * P x ^ 3 * P z - 9 * W'.a₁ * W'.a₆ * P x ^ 2 * P z ^ 2
    + 8 * W'.a₂ ^ 2 * P x ^ 2 * P y * P z + 12 * W'.a₂ * W'.a₃ * P x ^ 3 * P z
    - 12 * W'.a₂ * W'.a₃ * P y ^ 2 * P z ^ 2 + 8 * W'.a₂ * W'.a₄ * P x * P y * P z ^ 2
    - 12 * W'.a₃ ^ 2 * P x * P y * P z ^ 2 + 6 * W'.a₃ * W'.a₄ * P x ^ 2 * P z ^ 2
    + 2 * W'.a₄ ^ 2 * P y * P z ^ 3 + W'.a₁ ^ 3 * P x ^ 4 - 3 * W'.a₁ ^ 3 * P x * P y ^ 2 * P z
    - 2 * W'.a₁ ^ 2 * W'.a₂ * P x ^ 2 * P y * P z - 3 * W'.a₁ ^ 2 * W'.a₃ * P y ^ 2 * P z ^ 2
    + 2 * W'.a₁ ^ 2 * W'.a₄ * P x * P y * P z ^ 2 + 4 * W'.a₁ * W'.a₂ ^ 2 * P x ^ 3 * P z
    - 8 * W'.a₁ * W'.a₂ * W'.a₃ * P x * P y * P z ^ 2
    + 4 * W'.a₁ * W'.a₂ * W'.a₄ * P x ^ 2 * P z ^ 2 - 3 * W'.a₁ * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2
    + 2 * W'.a₁ * W'.a₃ * W'.a₄ * P y * P z ^ 3 + W'.a₁ * W'.a₄ ^ 2 * P x * P z ^ 3
    + 4 * W'.a₂ ^ 2 * W'.a₃ * P x ^ 2 * P z ^ 2 - 6 * W'.a₂ * W'.a₃ ^ 2 * P y * P z ^ 3
    + 4 * W'.a₂ * W'.a₃ * W'.a₄ * P x * P z ^ 3 - 2 * W'.a₃ ^ 3 * P x * P z ^ 3
    + W'.a₃ * W'.a₄ ^ 2 * P z ^ 4 - W'.a₁ ^ 4 * P x ^ 2 * P y * P z
    + W'.a₁ ^ 3 * W'.a₂ * P x ^ 3 * P z - 2 * W'.a₁ ^ 3 * W'.a₃ * P x * P y * P z ^ 2
    + W'.a₁ ^ 3 * W'.a₄ * P x ^ 2 * P z ^ 2 + W'.a₁ ^ 2 * W'.a₂ * W'.a₃ * P x ^ 2 * P z ^ 2
    - W'.a₁ ^ 2 * W'.a₃ ^ 2 * P y * P z ^ 3 + 2 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P x * P z ^ 3
    - W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P x * P z ^ 3 - W'.a₂ * W'.a₃ ^ 3 * P z ^ 4
    + W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4

lemma dblX_eq' {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblX P * P z =
    (eval P W'.polynomialX ^ 2 - W'.a₁ * eval P W'.polynomialX * P z * (P y - W'.negY P)
      - W'.a₂ * P z ^ 2 * (P y - W'.negY P) ^ 2 - 2 * P x * P z * (P y - W'.negY P) ^ 2)
      * (P y - W'.negY P) := by
  linear_combination (norm := (rw [dblX, eval_polynomialX, negY]; ring1))
    9 * (W'.a₁ * P x ^ 2 + 2 * P x * P y) * (equation_iff _).mp hP

lemma dblX_eq {P : Fin 3 → F} (hP : W.Equation P) (hPz : P z ≠ 0) : W.dblX P =
    ((eval P W.polynomialX ^ 2 - W.a₁ * eval P W.polynomialX * P z * (P y - W.negY P)
      - W.a₂ * P z ^ 2 * (P y - W.negY P) ^ 2 - 2 * P x * P z * (P y - W.negY P) ^ 2)
      * (P y - W.negY P)) / P z := by
  rw [← dblX_eq' hP, mul_div_cancel_right₀ _ hPz]

lemma dblX_smul (P : Fin 3 → R) (u : R) : W'.dblX (u • P) = u ^ 4 * W'.dblX P := by
  simp only [dblX, smul_fin3_ext]
  ring1

lemma dblX_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblX P = 0 := by
  rw [dblX, hPz, X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

lemma dblX_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z)
    (hy' : P y * Q z = W'.negY Q * P z) : W'.dblX P = 0 := by
  apply eq_zero_of_ne_zero_of_mul_right_eq_zero hPz
  rw [dblX_eq' hP, Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

private lemma toAffine_addX_of_eq {P : Fin 3 → F} (hPz : P z ≠ 0) {n d : F} (hd : d ≠ 0) :
    W.toAffine.addX (P x / P z) (P x / P z) (-n / P z / d) =
      (n ^ 2 - W.a₁ * n * P z * d - W.a₂ * P z ^ 2 * d ^ 2 - 2 * P x * P z * d ^ 2) * d / P z
        / (P z * d ^ 3) := by
  field_simp [mul_ne_zero hPz hd]
  ring1

lemma dblX_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ W.negY Q * P z) :
    W.dblX P / W.dblZ P = W.toAffine.addX (P x / P z) (Q x / Q z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [dblX_eq hP hPz, dblZ, toAffine_slope_of_eq hP hQ hPz hQz hx hy, ← (X_eq_iff hPz hQz).mp hx,
    toAffine_addX_of_eq hPz <| sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy]

variable (W') in
/-- The `Y`-coordinate of a representative of `-(2 • P)` for a projective point representative `P`
on a Weierstrass curve. -/
noncomputable def negDblY (P : Fin 3 → R) : R :=
  -P y ^ 4 - 3 * W'.a₁ * P x * P y ^ 3 - 9 * W'.a₃ * P x ^ 3 * P y + 3 * W'.a₃ * P y ^ 3 * P z
    - 3 * W'.a₄ * P x * P y ^ 2 * P z - 27 * W'.a₆ * P x ^ 3 * P z + 9 * W'.a₆ * P y ^ 2 * P z ^ 2
    - 3 * W'.a₁ ^ 2 * P x ^ 2 * P y ^ 2 + 4 * W'.a₁ * W'.a₂ * P y ^ 3 * P z
    - 3 * W'.a₁ * W'.a₂ * P x ^ 3 * P y - 9 * W'.a₁ * W'.a₃ * P x ^ 4
    + 6 * W'.a₁ * W'.a₃ * P x * P y ^ 2 * P z + 18 * W'.a₁ * W'.a₆ * P x * P y * P z ^ 2
    + 9 * W'.a₂ ^ 2 * P x ^ 4 - 8 * W'.a₂ ^ 2 * P x * P y ^ 2 * P z
    - 9 * W'.a₂ * W'.a₃ * P x ^ 2 * P y * P z + 9 * W'.a₂ * W'.a₄ * P x ^ 3 * P z
    - 4 * W'.a₂ * W'.a₄ * P y ^ 2 * P z ^ 2 - 27 * W'.a₂ * W'.a₆ * P x ^ 2 * P z ^ 2
    - 9 * W'.a₃ ^ 2 * P x ^ 3 * P z + 6 * W'.a₃ ^ 2 * P y ^ 2 * P z ^ 2
    - 12 * W'.a₃ * W'.a₄ * P x * P y * P z ^ 2 + 9 * W'.a₄ ^ 2 * P x ^ 2 * P z ^ 2
    - 2 * W'.a₁ ^ 3 * P x ^ 3 * P y + W'.a₁ ^ 3 * P y ^ 3 * P z + 3 * W'.a₁ ^ 2 * W'.a₂ * P x ^ 4
    + 2 * W'.a₁ ^ 2 * W'.a₂ * P x * P y ^ 2 * P z + 3 * W'.a₁ ^ 2 * W'.a₃ * P x ^ 2 * P y * P z
    + 3 * W'.a₁ ^ 2 * W'.a₄ * P x ^ 3 * P z - W'.a₁ ^ 2 * W'.a₄ * P y ^ 2 * P z ^ 2
    - 12 * W'.a₁ * W'.a₂ ^ 2 * P x ^ 2 * P y * P z - 6 * W'.a₁ * W'.a₂ * W'.a₃ * P x ^ 3 * P z
    + 4 * W'.a₁ * W'.a₂ * W'.a₃ * P y ^ 2 * P z ^ 2
    - 8 * W'.a₁ * W'.a₂ * W'.a₄ * P x * P y * P z ^ 2 + 6 * W'.a₁ * W'.a₃ ^ 2 * P x * P y * P z ^ 2
    - W'.a₁ * W'.a₄ ^ 2 * P y * P z ^ 3 + 8 * W'.a₂ ^ 3 * P x ^ 3 * P z
    - 8 * W'.a₂ ^ 2 * W'.a₃ * P x * P y * P z ^ 2 + 12 * W'.a₂ ^ 2 * W'.a₄ * P x ^ 2 * P z ^ 2
    - 9 * W'.a₂ * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2 - 4 * W'.a₂ * W'.a₃ * W'.a₄ * P y * P z ^ 3
    + 6 * W'.a₂ * W'.a₄ ^ 2 * P x * P z ^ 3 + W'.a₃ ^ 3 * P y * P z ^ 3
    - 3 * W'.a₃ ^ 2 * W'.a₄ * P x * P z ^ 3 + W'.a₄ ^ 3 * P z ^ 4 + W'.a₁ ^ 4 * P x * P y ^ 2 * P z
    - 3 * W'.a₁ ^ 3 * W'.a₂ * P x ^ 2 * P y * P z + W'.a₁ ^ 3 * W'.a₃ * P y ^ 2 * P z ^ 2
    - 2 * W'.a₁ ^ 3 * W'.a₄ * P x * P y * P z ^ 2 + 2 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * P x ^ 3 * P z
    - 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ * P x * P y * P z ^ 2
    + 3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ * P x ^ 2 * P z ^ 2
    - 2 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P y * P z ^ 3 + W'.a₁ ^ 2 * W'.a₄ ^ 2 * P x * P z ^ 3
    + W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P y * P z ^ 3 + 2 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * P x * P z ^ 3
    + W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P z ^ 4 - 2 * W'.a₂ ^ 2 * W'.a₃ ^ 2 * P x * P z ^ 3
    - W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4

lemma negDblY_eq' {P : Fin 3 → R} (hP : W'.Equation P) : W'.negDblY P * P z ^ 2 =
    -eval P W'.polynomialX * (eval P W'.polynomialX ^ 2
      - W'.a₁ * eval P W'.polynomialX * P z * (P y - W'.negY P)
      - W'.a₂ * P z ^ 2 * (P y - W'.negY P) ^ 2 - 2 * P x * P z * (P y - W'.negY P) ^ 2
      - P x * P z * (P y - W'.negY P) ^ 2) + P y * P z ^ 2 * (P y - W'.negY P) ^ 3 := by
  linear_combination (norm := (rw [negDblY, eval_polynomialX, negY]; ring1))
    -9 * (P y ^ 2 * P z + 2 * W'.a₁ * P x * P y * P z - 3 * P x ^ 3 - 3 * W'.a₂ * P x ^ 2 * P z)
      * (equation_iff _).mp hP

lemma negDblY_eq {P : Fin 3 → F} (hP : W.Equation P) (hPz : P z ≠ 0) : W.negDblY P =
    (-eval P W.polynomialX * (eval P W.polynomialX ^ 2
      - W.a₁ * eval P W.polynomialX * P z * (P y - W.negY P)
      - W.a₂ * P z ^ 2 * (P y - W.negY P) ^ 2 - 2 * P x * P z * (P y - W.negY P) ^ 2
      - P x * P z * (P y - W.negY P) ^ 2) + P y * P z ^ 2 * (P y - W.negY P) ^ 3) / P z ^ 2 := by
  rw [← negDblY_eq' hP, mul_div_cancel_right₀ _ <| pow_ne_zero 2 hPz]

lemma negDblY_smul (P : Fin 3 → R) (u : R) : W'.negDblY (u • P) = u ^ 4 * W'.negDblY P := by
  simp only [negDblY, smul_fin3_ext]
  ring1

lemma negDblY_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.negDblY P = -P y ^ 4 := by
  rw [negDblY, hPz, X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

lemma negDblY_of_Y_eq' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W'.negY Q * P z) :
    W'.negDblY P * P z ^ 2 = -eval P W'.polynomialX ^ 3 := by
  rw [negDblY_eq' hP, Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

lemma negDblY_of_Y_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.negDblY P = -W.dblU P := by
  rw [dblU, ← neg_div, ← negDblY_of_Y_eq' hP hQz hx hy hy',
    mul_div_cancel_right₀ _ <| pow_ne_zero 2 hPz]

private lemma toAffine_negAddY_of_eq {P : Fin 3 → F} (hPz : P z ≠ 0) {n d : F} (hd : d ≠ 0) :
    W.toAffine.negAddY (P x / P z) (P x / P z) (P y / P z) (-n / P z / d) =
      (-n * (n ^ 2 - W.a₁ * n * P z * d - W.a₂ * P z ^ 2 * d ^ 2 - 2 * P x * P z * d ^ 2
          - P x * P z * d ^ 2) + P y * P z ^ 2 * d ^ 3) / P z ^ 2 / (P z * d ^ 3) := by
  rw [Affine.negAddY, toAffine_addX_of_eq hPz hd]
  field_simp [mul_ne_zero hPz <| mul_ne_zero hPz <| pow_ne_zero 3 hd]
  ring1

lemma negDblY_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ W.negY Q * P z) :
    W.negDblY P / W.dblZ P = W.toAffine.negAddY (P x / P z) (Q x / Q z) (P y / P z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [negDblY_eq hP hPz, dblZ, toAffine_slope_of_eq hP hQ hPz hQz hx hy, ← (X_eq_iff hPz hQz).mp hx,
    toAffine_negAddY_of_eq hPz <| sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy]

variable (W') in
/-- The `Y`-coordinate of a representative of `2 • P` for a projective point representative `P` on a
Weierstrass curve. -/
noncomputable def dblY (P : Fin 3 → R) : R :=
  W'.negY ![W'.dblX P, W'.negDblY P, W'.dblZ P]

lemma dblY_smul (P : Fin 3 → R) (u : R) : W'.dblY (u • P) = u ^ 4 * W'.dblY P := by
  simp only [dblY, negY_eq, negDblY_smul, dblX_smul, dblZ_smul]
  ring1

lemma dblY_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblY P = P y ^ 4 := by
  rw [dblY, negY_eq, negDblY_of_Z_eq_zero hP hPz, dblX_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz]
  ring1

lemma dblY_of_Y_eq' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z)
    (hy' : P y * Q z = W'.negY Q * P z) : W'.dblY P * P z ^ 2 = eval P W'.polynomialX ^ 3 := by
  linear_combination (norm := (rw [dblY, negY_eq, dblX_of_Y_eq hP hPz hQz hx hy hy',
    dblZ_of_Y_eq hQz hx hy hy']; ring1)) -negDblY_of_Y_eq' hP hQz hx hy hy'

lemma dblY_of_Y_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.dblY P = W.dblU P := by
  rw [dblU, ← dblY_of_Y_eq' hP hPz hQz hx hy hy', mul_div_cancel_right₀ _ <| pow_ne_zero 2 hPz]

lemma dblY_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ W.negY Q * P z) :
    W.dblY P / W.dblZ P = W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  erw [dblY, negY_of_Z_ne_zero <| dblZ_ne_zero_of_Y_ne' hP hQ hPz hQz hx hy,
    dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, negDblY_of_Z_ne_zero hP hQ hPz hQz hx hy, Affine.addY]

variable (W') in
/-- The coordinates of a representative of `2 • P` for a projective point representative `P` on a
Weierstrass curve. -/
noncomputable def dblXYZ (P : Fin 3 → R) : Fin 3 → R :=
  ![W'.dblX P, W'.dblY P, W'.dblZ P]

lemma dblXYZ_X (P : Fin 3 → R) : W'.dblXYZ P x = W'.dblX P :=
  rfl

lemma dblXYZ_Y (P : Fin 3 → R) : W'.dblXYZ P y = W'.dblY P :=
  rfl

lemma dblXYZ_Z (P : Fin 3 → R) : W'.dblXYZ P z = W'.dblZ P :=
  rfl

lemma dblXYZ_smul (P : Fin 3 → R) (u : R) : W'.dblXYZ (u • P) = u ^ 4 • W'.dblXYZ P := by
  rw [dblXYZ, dblX_smul, dblY_smul, dblZ_smul, smul_fin3, dblXYZ_X, dblXYZ_Y, dblXYZ_Z]

lemma dblXYZ_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblXYZ P = P y ^ 4 • ![0, 1, 0] := by
  erw [dblXYZ, dblX_of_Z_eq_zero hP hPz, dblY_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz, smul_fin3,
    mul_zero, mul_one]

lemma dblXYZ_of_Y_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.dblXYZ P = W.dblU P • ![0, 1, 0] := by
  erw [dblXYZ, dblX_of_Y_eq hP hPz hQz hx hy hy', dblY_of_Y_eq hP hPz hQz hx hy hy',
    dblZ_of_Y_eq hQz hx hy hy', smul_fin3, mul_zero, mul_one]

lemma dblXYZ_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ W.negY Q * P z) :
    W.dblXYZ P = W.dblZ P •
      ![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)), 1] := by
  have hZ : IsUnit <| W.dblZ P := isUnit_dblZ_of_Y_ne' hP hQ hPz hQz hx hy
  erw [dblXYZ, smul_fin3, ← dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, hZ.mul_div_cancel,
    ← dblY_of_Z_ne_zero hP hQ hPz hQz hx hy, hZ.mul_div_cancel, mul_one]

end Doubling

section Addition

/-! ### Addition formulae -/

/-- The unit associated to a representative of `P + Q` for two projective point representatives `P`
and `Q` on a Weierstrass curve `W` that are not `2`-torsion.

More specifically, the unit `u` such that `W.add P Q = u • ![0, 1, 0]` where `P x / P z = Q x / Q z`
but `P ≠ W.neg P`. -/
def addU (P Q : Fin 3 → F) : F :=
  -(P y * Q z - Q y * P z) ^ 3 / (P z * Q z)

lemma addU_smul {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) {u v : F} (hu : u ≠ 0)
    (hv : v ≠ 0) : addU (u • P) (v • Q) = (u * v) ^ 2 * addU P Q := by
  field_simp [addU, smul_fin3_ext]
  ring1

lemma addU_of_Z_eq_zero_left {P Q : Fin 3 → F} (hPz : P z = 0) : addU P Q = 0 := by
  rw [addU, hPz, zero_mul, div_zero]

lemma addU_of_Z_eq_zero_right {P Q : Fin 3 → F} (hQz : Q z = 0) : addU P Q = 0 := by
  rw [addU, hQz, mul_zero <| P z, div_zero]

lemma addU_ne_zero_of_Y_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hy : P y * Q z ≠ Q y * P z) : addU P Q ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr <| pow_ne_zero 3 <| sub_ne_zero.mpr hy) <| mul_ne_zero hPz hQz

lemma isUnit_addU_of_Y_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hy : P y * Q z ≠ Q y * P z) : IsUnit (addU P Q) :=
  (addU_ne_zero_of_Y_ne hPz hQz hy).isUnit

variable (W') in
/-- The `Z`-coordinate of a representative of `P + Q` for two distinct projective point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def addZ (P Q : Fin 3 → R) : R :=
  -3 * P x ^ 2 * Q x * Q z + 3 * P x * Q x ^ 2 * P z + P y ^ 2 * Q z ^ 2 - Q y ^ 2 * P z ^ 2
    + W'.a₁ * P x * P y * Q z ^ 2 - W'.a₁ * Q x * Q y * P z ^ 2 - W'.a₂ * P x ^ 2 * Q z ^ 2
    + W'.a₂ * Q x ^ 2 * P z ^ 2 + W'.a₃ * P y * P z * Q z ^ 2 - W'.a₃ * Q y * P z ^ 2 * Q z
    - W'.a₄ * P x * P z * Q z ^ 2 + W'.a₄ * Q x * P z ^ 2 * Q z

lemma addZ_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addZ P Q * (P z * Q z) = (P x * Q z - Q x * P z) ^ 3 := by
  linear_combination (norm := (rw [addZ]; ring1))
    Q z ^ 3 * (equation_iff _).mp hP - P z ^ 3 * (equation_iff _).mp hQ

lemma addZ_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) : W.addZ P Q = (P x * Q z - Q x * P z) ^ 3 / (P z * Q z) := by
  rw [← addZ_eq' hP hQ, mul_div_cancel_right₀ _ <| mul_ne_zero hPz hQz]

lemma addZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addZ (u • P) (v • Q) = (u * v) ^ 2 * W'.addZ P Q := by
  simp only [addZ, smul_fin3_ext]
  ring1

lemma addZ_self (P : Fin 3 → R) : W'.addZ P P = 0 := by
  rw [addZ]
  ring1

lemma addZ_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addZ P Q = P y ^ 2 * Q z * Q z := by
  rw [addZ, hPz, X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

lemma addZ_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addZ P Q = -(Q y ^ 2 * P z) * P z := by
  rw [addZ, hQz, X_eq_zero_of_Z_eq_zero hQ hQz]
  ring1

lemma addZ_of_X_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) : W'.addZ P Q = 0 := by
  apply eq_zero_of_ne_zero_of_mul_right_eq_zero <| mul_ne_zero hPz hQz
  rw [addZ_eq' hP hQ, hx, sub_self, zero_pow three_ne_zero]

lemma addZ_ne_zero_of_X_ne [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hx : P x * Q z ≠ Q x * P z) : W'.addZ P Q ≠ 0 :=
  addZ_eq' hP hQ ▸ left_ne_zero_of_mul <| pow_ne_zero 3 <| sub_ne_zero.mpr hx

lemma isUnit_addZ_of_X_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hx : P x * Q z ≠ Q x * P z) : IsUnit <| W.addZ P Q :=
  (addZ_ne_zero_of_X_ne hP hQ hx).isUnit

private lemma toAffine_slope_of_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ≠ Q x * P z) :
    W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z) =
      (P y * Q z - Q y * P z) / (P x * Q z - Q x * P z) := by
  field_simp [Affine.slope_of_X_ne <| by rwa [ne_eq, ← X_eq_iff hPz hQz]]
  ring1

variable (W') in
/-- The `X`-coordinate of a representative of `P + Q` for two distinct projective point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def addX (P Q : Fin 3 → R) : R :=
  -P x * Q y ^ 2 * P z + Q x * P y ^ 2 * Q z - 2 * P x * P y * Q y * Q z + 2 * Q x * P y * Q y * P z
    - W'.a₁ * P x ^ 2 * Q y * Q z + W'.a₁ * Q x ^ 2 * P y * P z + W'.a₂ * P x ^ 2 * Q x * Q z
    - W'.a₂ * P x * Q x ^ 2 * P z - W'.a₃ * P x * P y * Q z ^ 2 + W'.a₃ * Q x * Q y * P z ^ 2
    - 2 * W'.a₃ * P x * Q y * P z * Q z + 2 * W'.a₃ * Q x * P y * P z * Q z
    + W'.a₄ * P x ^ 2 * Q z ^ 2 - W'.a₄ * Q x ^ 2 * P z ^ 2 + 3 * W'.a₆ * P x * P z * Q z ^ 2
    - 3 * W'.a₆ * Q x * P z ^ 2 * Q z

lemma addX_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * (P z * Q z) ^ 2 =
      ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W'.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W'.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2) * (P x * Q z - Q x * P z) := by
  linear_combination (norm := (rw [addX]; ring1))
    (2 * Q x * P z * Q z ^ 3 - P x * Q z ^ 4) * (equation_iff _).mp hP
      + (Q x * P z ^ 4 - 2 * P x * P z ^ 3 * Q z) * (equation_iff _).mp hQ

lemma addX_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) : W.addX P Q =
      ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2) * (P x * Q z - Q x * P z) / (P z * Q z) ^ 2 := by
  rw [← addX_eq' hP hQ, mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

lemma addX_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addX (u • P) (v • Q) = (u * v) ^ 2 * W'.addX P Q := by
  simp only [addX, smul_fin3_ext]
  ring1

lemma addX_self (P : Fin 3 → R) : W'.addX P P = 0 := by
  rw [addX]
  ring1

lemma addX_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addX P Q = P y ^ 2 * Q z * Q x := by
  rw [addX, hPz, X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

lemma addX_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addX P Q = -(Q y ^ 2 * P z) * P x := by
  rw [addX, hQz, X_eq_zero_of_Z_eq_zero hQ hQz]
  ring1

lemma addX_of_X_eq [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) : W'.addX P Q = 0 := by
  apply eq_zero_of_ne_zero_of_mul_right_eq_zero <| pow_ne_zero 2 <| mul_ne_zero hPz hQz
  rw [addX_eq' hP hQ, hx]
  ring1

private lemma toAffine_addX_of_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) {n d : F}
    (hd : d ≠ 0) : W.toAffine.addX (P x / P z) (Q x / Q z) (n / d) =
      (n ^ 2 * P z * Q z + W.a₁ * n * P z * Q z * d - W.a₂ * P z * Q z * d ^ 2 - P x * Q z * d ^ 2
        - Q x * P z * d ^ 2) * d / (P z * Q z) ^ 2 / (d ^ 3 / (P z * Q z)) := by
  field_simp [hd]
  ring1

lemma addX_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ≠ Q x * P z) : W.addX P Q / W.addZ P Q =
    W.toAffine.addX (P x / P z) (Q x / Q z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [addX_eq hP hQ hPz hQz, addZ_eq hP hQ hPz hQz, toAffine_slope_of_ne hPz hQz hx,
    toAffine_addX_of_ne hPz hQz <| sub_ne_zero.mpr hx]

variable (W') in
/-- The `Y`-coordinate of a representative of `-(P + Q)` for two distinct projective point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def negAddY (P Q : Fin 3 → R) : R :=
  -3 * P x ^ 2 * Q x * Q y + 3 * P x * Q x ^ 2 * P y - P y ^ 2 * Q y * Q z + P y * Q y ^ 2 * P z
    + W'.a₁ * P x * Q y ^ 2 * P z - W'.a₁ * Q x * P y ^ 2 * Q z - W'.a₂ * P x ^ 2 * Q y * Q z
    + W'.a₂ * Q x ^ 2 * P y * P z + 2 * W'.a₂ * P x * Q x * P y * Q z
    - 2 * W'.a₂ * P x * Q x * Q y * P z - W'.a₃ * P y ^ 2 * Q z ^ 2 + W'.a₃ * Q y ^ 2 * P z ^ 2
    + W'.a₄ * P x * P y * Q z ^ 2 - 2 * W'.a₄ * P x * Q y * P z * Q z
    + 2 * W'.a₄ * Q x * P y * P z * Q z - W'.a₄ * Q x * Q y * P z ^ 2
    + 3 * W'.a₆ * P y * P z * Q z ^ 2 - 3 * W'.a₆ * Q y * P z ^ 2 * Q z

lemma negAddY_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.negAddY P Q * (P z * Q z) ^ 2 =
      (P y * Q z - Q y * P z) * ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W'.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W'.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2)
        + P y * Q z * (P x * Q z - Q x * P z) ^ 3 := by
  linear_combination (norm := (rw [negAddY]; ring1))
    (2 * Q y * P z * Q z ^ 3 - P y * Q z ^ 4) * (equation_iff _).mp hP
      + (Q y * P z ^ 4 - 2 * P y * P z ^ 3 * Q z) * (equation_iff _).mp hQ

lemma negAddY_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) : W.negAddY P Q =
      ((P y * Q z - Q y * P z) * ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2)
        + P y * Q z * (P x * Q z - Q x * P z) ^ 3) / (P z * Q z) ^ 2 := by
  rw [← negAddY_eq' hP hQ, mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

lemma negAddY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.negAddY (u • P) (v • Q) = (u * v) ^ 2 * W'.negAddY P Q := by
  simp only [negAddY, smul_fin3_ext]
  ring1

lemma negAddY_self (P : Fin 3 → R) : W'.negAddY P P = 0 := by
  rw [negAddY]
  ring1

lemma negAddY_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.negAddY P Q = P y ^ 2 * Q z * W'.negY Q := by
  rw [negAddY, hPz, X_eq_zero_of_Z_eq_zero hP hPz, negY]
  ring1

lemma negAddY_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.negAddY P Q = -(Q y ^ 2 * P z) * W'.negY P := by
  rw [negAddY, hQz, X_eq_zero_of_Z_eq_zero hQ hQz, negY]
  ring1

lemma negAddY_of_X_eq' {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z = Q x * P z) :
    W'.negAddY P Q * (P z * Q z) ^ 2 = (P y * Q z - Q y * P z) ^ 3 * (P z * Q z) := by
  rw [negAddY_eq' hP hQ, hx]
  ring1

lemma negAddY_of_X_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) : W.negAddY P Q = -addU P Q := by
  rw [addU, neg_div, neg_neg, ← mul_div_mul_right _ _ <| mul_ne_zero hPz hQz,
    ← negAddY_of_X_eq' hP hQ hx, ← sq,
    mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

private lemma toAffine_negAddY_of_ne {P Q : Fin 3 → F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) {n d : F}
    (hd : d ≠ 0) : W.toAffine.negAddY (P x / P z) (Q x / Q z) (P y / P z) (n / d) =
      (n * (n ^ 2 * P z * Q z + W.a₁ * n * P z * Q z * d - W.a₂ * P z * Q z * d ^ 2
        - P x * Q z * d ^ 2 - Q x * P z * d ^ 2 - P x * Q z * d ^ 2) + P y * Q z * d ^ 3)
        / (P z * Q z) ^ 2 / (d ^ 3 / (P z * Q z)) := by
  rw [Affine.negAddY, toAffine_addX_of_ne hPz hQz hd]
  field_simp [mul_ne_zero (pow_ne_zero 2 <| mul_ne_zero hPz hQz) <| pow_ne_zero 3 hd]
  ring1

lemma negAddY_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ≠ Q x * P z) : W.negAddY P Q / W.addZ P Q =
      W.toAffine.negAddY (P x / P z) (Q x / Q z) (P y / P z)
        (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [negAddY_eq hP hQ hPz hQz, addZ_eq hP hQ hPz hQz, toAffine_slope_of_ne hPz hQz hx,
    toAffine_negAddY_of_ne hPz hQz <| sub_ne_zero.mpr hx]

variable (W') in
/-- The `Y`-coordinate of a representative of `P + Q` for two distinct projective point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def addY (P Q : Fin 3 → R) : R :=
  W'.negY ![W'.addX P Q, W'.negAddY P Q, W'.addZ P Q]

lemma addY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addY (u • P) (v • Q) = (u * v) ^ 2 * W'.addY P Q := by
  simp only [addY, negY_eq, negAddY_smul, addX_smul, addZ_smul]
  ring1

lemma addY_self (P : Fin 3 → R) : W'.addY P P = 0 := by
  simp only [addY, negY_eq, negAddY_self, addX_self, addZ_self, neg_zero, mul_zero, sub_zero]

lemma addY_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addY P Q = P y ^ 2 * Q z * Q y := by
  rw [addY, negY_eq, negAddY_of_Z_eq_zero_left hP hPz, negY, addX_of_Z_eq_zero_left hP hPz,
    addZ_of_Z_eq_zero_left hP hPz]
  ring1

lemma addY_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addY P Q = -(Q y ^ 2 * P z) * P y := by
  rw [addY, negY_eq, negAddY_of_Z_eq_zero_right hQ hQz, negY, addX_of_Z_eq_zero_right hQ hQz,
    addZ_of_Z_eq_zero_right hQ hQz]
  ring1

lemma addY_of_X_eq' [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) :
    W'.addY P Q * (P z * Q z) ^ 3 = -(P y * Q z - Q y * P z) ^ 3 * (P z * Q z) ^ 2 := by
  linear_combination (norm := (rw [addY, negY_eq, addX_of_X_eq hP hQ hPz hQz hx,
    addZ_of_X_eq hP hQ hPz hQz hx]; ring1)) -(P z * Q z) * negAddY_of_X_eq' hP hQ hx

lemma addY_of_X_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) : W.addY P Q = addU P Q := by
  rw [addU, ← mul_div_mul_right _ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz,
    ← addY_of_X_eq' hP hQ hPz hQz hx, ← pow_succ',
    mul_div_cancel_right₀ _ <| pow_ne_zero 3 <| mul_ne_zero hPz hQz]

lemma addY_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ≠ Q x * P z) : W.addY P Q / W.addZ P Q =
      W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
        (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  erw [addY, negY_of_Z_ne_zero <| addZ_ne_zero_of_X_ne hP hQ hx, addX_of_Z_ne_zero hP hQ hPz hQz hx,
    negAddY_of_Z_ne_zero hP hQ hPz hQz hx, Affine.addY]

variable (W') in
/-- The coordinates of a representative of `P + Q` for two distinct projective point representatives
`P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `![0, 0, 0]`. -/
noncomputable def addXYZ (P Q : Fin 3 → R) : Fin 3 → R :=
  ![W'.addX P Q, W'.addY P Q, W'.addZ P Q]

lemma addXYZ_X (P Q : Fin 3 → R) : W'.addXYZ P Q x = W'.addX P Q :=
  rfl

lemma addXYZ_Y (P Q : Fin 3 → R) : W'.addXYZ P Q y = W'.addY P Q :=
  rfl

lemma addXYZ_Z (P Q : Fin 3 → R) : W'.addXYZ P Q z = W'.addZ P Q :=
  rfl

lemma addXYZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.addXYZ (u • P) (v • Q) = (u * v) ^ 2 • W'.addXYZ P Q := by
  rw [addXYZ, addX_smul, addY_smul, addZ_smul, smul_fin3, addXYZ_X, addXYZ_Y, addXYZ_Z]

lemma addXYZ_self (P : Fin 3 → R) : W'.addXYZ P P = ![0, 0, 0] := by
  rw [addXYZ, addX_self, addY_self, addZ_self]

lemma addXYZ_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addXYZ P Q = (P y ^ 2 * Q z) • Q := by
  rw [addXYZ, addX_of_Z_eq_zero_left hP hPz, addY_of_Z_eq_zero_left hP hPz,
    addZ_of_Z_eq_zero_left hP hPz, smul_fin3]

lemma addXYZ_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addXYZ P Q = -(Q y ^ 2 * P z) • P := by
  rw [addXYZ, addX_of_Z_eq_zero_right hQ hQz, addY_of_Z_eq_zero_right hQ hQz,
    addZ_of_Z_eq_zero_right hQ hQz, smul_fin3]

lemma addXYZ_of_X_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) : W.addXYZ P Q = addU P Q • ![0, 1, 0] := by
  erw [addXYZ, addX_of_X_eq hP hQ hPz hQz hx, addY_of_X_eq hP hQ hPz hQz hx,
    addZ_of_X_eq hP hQ hPz hQz hx, smul_fin3, mul_zero, mul_one]

lemma addXYZ_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ≠ Q x * P z) : W.addXYZ P Q = W.addZ P Q •
      ![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)), 1] := by
  have hZ : IsUnit <| W.addZ P Q := isUnit_addZ_of_X_ne hP hQ hx
  erw [addXYZ, smul_fin3, ← addX_of_Z_ne_zero hP hQ hPz hQz hx, hZ.mul_div_cancel,
    ← addY_of_Z_ne_zero hP hQ hPz hQz hx, hZ.mul_div_cancel, mul_one]

end Addition

section Negation

/-! ### Negation on point representatives -/

variable (W') in
/-- The negation of a projective point representative on a Weierstrass curve. -/
def neg (P : Fin 3 → R) : Fin 3 → R :=
  ![P x, W'.negY P, P z]

lemma neg_X (P : Fin 3 → R) : W'.neg P x = P x :=
  rfl

lemma neg_Y (P : Fin 3 → R) : W'.neg P y = W'.negY P :=
  rfl

lemma neg_Z (P : Fin 3 → R) : W'.neg P z = P z :=
  rfl

lemma neg_smul (P : Fin 3 → R) (u : R) : W'.neg (u • P) = u • W'.neg P := by
  simpa only [neg, negY_smul] using (smul_fin3 (W'.neg P) u).symm

lemma neg_smul_equiv (P : Fin 3 → R) {u : R} (hu : IsUnit u) : W'.neg (u • P) ≈ W'.neg P :=
  ⟨hu.unit, (neg_smul ..).symm⟩

lemma neg_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.neg P ≈ W'.neg Q := by
  rcases h with ⟨u, rfl⟩
  exact neg_smul_equiv Q u.isUnit

lemma neg_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 → R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.neg P = -P y • ![0, 1, 0] := by
  erw [neg, X_eq_zero_of_Z_eq_zero hP hPz, negY_of_Z_eq_zero hP hPz, hPz, smul_fin3, mul_zero,
    mul_one]

lemma neg_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.neg P = P z • ![P x / P z, W.toAffine.negY (P x / P z) (P y / P z), 1] := by
  erw [neg, smul_fin3, mul_div_cancel₀ _ hPz, ← negY_of_Z_ne_zero hPz, mul_div_cancel₀ _ hPz,
    mul_one]

private lemma nonsingular_neg_of_Z_ne_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) :
    W.Nonsingular ![P x / P z, W.toAffine.negY (P x / P z) (P y / P z), 1] :=
  (nonsingular_some ..).mpr <| Affine.nonsingular_neg <| (nonsingular_of_Z_ne_zero hPz).mp hP

lemma nonsingular_neg {P : Fin 3 → F} (hP : W.Nonsingular P) : W.Nonsingular <| W.neg P := by
  by_cases hPz : P z = 0
  · simp only [neg_of_Z_eq_zero hP.left hPz, nonsingular_smul _ (isUnit_Y_of_Z_eq_zero hP hPz).neg,
      nonsingular_zero]
  · simp only [neg_of_Z_ne_zero hPz, nonsingular_smul _ <| Ne.isUnit hPz,
      nonsingular_neg_of_Z_ne_zero hP hPz]

lemma addZ_neg (P : Fin 3 → R) : W'.addZ P (W'.neg P) = 0 := by
  rw [addZ, neg_X, neg_Y, neg_Z, negY]
  ring1

lemma addX_neg (P : Fin 3 → R) : W'.addX P (W'.neg P) = 0 := by
  rw [addX, neg_X, neg_Y, neg_Z, negY]
  ring1

lemma negAddY_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.negAddY P (W'.neg P) = W'.dblZ P := by
  linear_combination (norm := (rw [negAddY, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -3 * (P y - W'.negY P) * (equation_iff _).mp hP

lemma addY_neg {P : Fin 3 → R} (hP : W'.Equation P) : W'.addY P (W'.neg P) = -W'.dblZ P := by
  rw [addY, negY_eq, addX_neg, negAddY_neg hP, addZ_neg, mul_zero, sub_zero, mul_zero, sub_zero]

lemma addXYZ_neg {P : Fin 3 → R} (hP : W'.Equation P) :
    W'.addXYZ P (W'.neg P) = -W'.dblZ P • ![0, 1, 0] := by
  erw [addXYZ, addX_neg, addY_neg hP, addZ_neg, smul_fin3, mul_zero, mul_one]

variable (W') in
/-- The negation of a projective point class on a Weierstrass curve `W`.

If `P` is a projective point representative on `W`, then `W.negMap ⟦P⟧` is definitionally equivalent
to `W.neg P`. -/
def negMap (P : PointClass R) : PointClass R :=
  P.map W'.neg fun _ _ => neg_equiv

lemma negMap_eq (P : Fin 3 → R) : W'.negMap ⟦P⟧ = ⟦W'.neg P⟧ :=
  rfl

lemma negMap_of_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.negMap ⟦P⟧ = ⟦![0, 1, 0]⟧ := by
  rw [negMap_eq, neg_of_Z_eq_zero hP.left hPz, smul_eq _ (isUnit_Y_of_Z_eq_zero hP hPz).neg]

lemma negMap_of_Z_ne_zero {P : Fin 3 → F} (hPz : P z ≠ 0) :
    W.negMap ⟦P⟧ = ⟦![P x / P z, W.toAffine.negY (P x / P z) (P y / P z), 1]⟧ := by
  rw [negMap_eq, neg_of_Z_ne_zero hPz, smul_eq _ <| Ne.isUnit hPz]

lemma nonsingularLift_negMap {P : PointClass F} (hP : W.NonsingularLift P) :
    W.NonsingularLift <| W.negMap P := by
  rcases P with ⟨_⟩
  exact nonsingular_neg hP

end Negation

section Addition

/-! ### Addition on point representatives -/

open Classical in
variable (W') in
/-- The addition of two projective point representatives on a Weierstrass curve. -/
noncomputable def add (P Q : Fin 3 → R) : Fin 3 → R :=
  if P ≈ Q then W'.dblXYZ P else W'.addXYZ P Q

lemma add_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) : W'.add P Q = W'.dblXYZ P :=
  if_pos h

lemma add_smul_of_equiv {P Q : Fin 3 → R} (h : P ≈ Q) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) = u ^ 4 • W'.add P Q := by
  rw [add_of_equiv <| (smul_equiv_smul P Q hu hv).mpr h, dblXYZ_smul, add_of_equiv h]

lemma add_self (P : Fin 3 → R) : W'.add P P = W'.dblXYZ P :=
  add_of_equiv <| Setoid.refl _

lemma add_of_eq {P Q : Fin 3 → R} (h : P = Q) : W'.add P Q = W'.dblXYZ P :=
  h ▸ add_self P

lemma add_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ P Q :=
  if_neg h

lemma add_smul_of_not_equiv {P Q : Fin 3 → R} (h : ¬P ≈ Q) {u v : R} (hu : IsUnit u)
    (hv : IsUnit v) : W'.add (u • P) (v • Q) = (u * v) ^ 2 • W'.add P Q := by
  rw [add_of_not_equiv <| h.comp (smul_equiv_smul P Q hu hv).mp, addXYZ_smul, add_of_not_equiv h]

lemma add_smul_equiv (P Q : Fin 3 → R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) ≈ W'.add P Q := by
  by_cases h : P ≈ Q
  · exact ⟨hu.unit ^ 4, by convert (add_smul_of_equiv h hu hv).symm⟩
  · exact ⟨(hu.unit * hv.unit) ^ 2, by convert (add_smul_of_not_equiv h hu hv).symm⟩

lemma add_equiv {P P' Q Q' : Fin 3 → R} (hP : P ≈ P') (hQ : Q ≈ Q') :
    W'.add P Q ≈ W'.add P' Q' := by
  rcases hP, hQ with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  exact add_smul_equiv P' Q' u.isUnit v.isUnit

lemma add_of_Z_eq_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : W.add P Q = P y ^ 4 • ![0, 1, 0] := by
  rw [add, if_pos <| equiv_of_Z_eq_zero hP hQ hPz hQz, dblXYZ_of_Z_eq_zero hP.left hPz]

lemma add_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 → R} (hP : W'.Equation P)
    (hPz : P z = 0) (hQz : Q z ≠ 0) : W'.add P Q = (P y ^ 2 * Q z) • Q := by
  rw [add, if_neg <| not_equiv_of_Z_eq_zero_left hPz hQz, addXYZ_of_Z_eq_zero_left hP hPz]

lemma add_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 → R} (hQ : W'.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z = 0) : W'.add P Q = -(Q y ^ 2 * P z) • P := by
  rw [add, if_neg <| not_equiv_of_Z_eq_zero_right hPz hQz, addXYZ_of_Z_eq_zero_right hQ hQz]

lemma add_of_Y_eq {P Q : Fin 3 → F} (hP : W.Equation P) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.add P Q = W.dblU P • ![0, 1, 0] := by
  rw [add, if_pos <| equiv_of_X_eq_of_Y_eq hPz hQz hx hy, dblXYZ_of_Y_eq hP hPz hQz hx hy hy']

lemma add_of_Y_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ Q y * P z) :
    W.add P Q = addU P Q • ![0, 1, 0] := by
  rw [add, if_neg <| not_equiv_of_Y_ne hy, addXYZ_of_X_eq hP hQ hPz hQz hx]

lemma add_of_Y_ne' {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z ≠ W.negY Q * P z) :
    W.add P Q = W.dblZ P •
      ![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)), 1] := by
  rw [add, if_pos <| equiv_of_X_eq_of_Y_eq hPz hQz hx <| Y_eq_of_Y_ne' hP hQ hPz hQz hx hy,
    dblXYZ_of_Z_ne_zero hP hQ hPz hQz hx hy]

lemma add_of_X_ne {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ≠ Q x * P z) : W.add P Q = W.addZ P Q •
      ![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)), 1] := by
  rw [add, if_neg <| not_equiv_of_X_ne hx, addXYZ_of_Z_ne_zero hP hQ hPz hQz hx]

private lemma nonsingular_add_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hxy : ¬(P x * Q z = Q x * P z ∧ P y * Q z = W.negY Q * P z)) : W.Nonsingular
      ![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)), 1] :=
  (nonsingular_some ..).mpr <| Affine.nonsingular_add ((nonsingular_of_Z_ne_zero hPz).mp hP)
    ((nonsingular_of_Z_ne_zero hQz).mp hQ) <| by rwa [← X_eq_iff hPz hQz, ← Y_eq_iff' hPz hQz]

lemma nonsingular_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.Nonsingular <| W.add P Q := by
  by_cases hPz : P z = 0
  · by_cases hQz : Q z = 0
    · simp only [add_of_Z_eq_zero hP hQ hPz hQz,
        nonsingular_smul _ <| (isUnit_Y_of_Z_eq_zero hP hPz).pow 4, nonsingular_zero]
    · simpa only [add_of_Z_eq_zero_left hP.left hPz hQz,
        nonsingular_smul _ <| ((isUnit_Y_of_Z_eq_zero hP hPz).pow 2).mul <| Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · simpa only [add_of_Z_eq_zero_right hQ.left hPz hQz,
        nonsingular_smul _ (((isUnit_Y_of_Z_eq_zero hQ hQz).pow 2).mul <| Ne.isUnit hPz).neg]
    · by_cases hxy : P x * Q z = Q x * P z ∧ P y * Q z = W.negY Q * P z
      · by_cases hy : P y * Q z = Q y * P z
        · simp only [add_of_Y_eq hP.left hPz hQz hxy.left hy hxy.right, nonsingular_smul _ <|
              isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, nonsingular_zero]
        · simp only [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
            nonsingular_smul _ <| isUnit_addU_of_Y_ne hPz hQz hy, nonsingular_zero]
      · have := nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z = Q x * P z
        · simpa only [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
            nonsingular_smul _ <| isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hQz hx <|
              not_and.mp hxy hx]
        · simpa only [add_of_X_ne hP.left hQ.left hPz hQz hx,
            nonsingular_smul _ <| isUnit_addZ_of_X_ne hP.left hQ.left hx]

variable (W') in
/-- The addition of two projective point classes on a Weierstrass curve `W`.

If `P` and `Q` are two projective point representatives on `W`, then `W.addMap ⟦P⟧ ⟦Q⟧` is
definitionally equivalent to `W.add P Q`. -/
noncomputable def addMap (P Q : PointClass R) : PointClass R :=
  Quotient.map₂ W'.add (fun _ _ hP _ _ hQ => add_equiv hP hQ) P Q

lemma addMap_eq (P Q : Fin 3 → R) : W'.addMap ⟦P⟧ ⟦Q⟧ = ⟦W'.add P Q⟧ :=
  rfl

lemma addMap_of_Z_eq_zero_left {P : Fin 3 → F} {Q : PointClass F} (hP : W.Nonsingular P)
    (hQ : W.NonsingularLift Q) (hPz : P z = 0) : W.addMap ⟦P⟧ Q = Q := by
  rcases Q with ⟨Q⟩
  by_cases hQz : Q z = 0
  · erw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_Y_of_Z_eq_zero hP hPz).pow 4, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hQ hQz
  · erw [addMap_eq, add_of_Z_eq_zero_left hP.left hPz hQz,
      smul_eq _ <| ((isUnit_Y_of_Z_eq_zero hP hPz).pow 2).mul <| Ne.isUnit hQz]
    rfl

lemma addMap_of_Z_eq_zero_right {P : PointClass F} {Q : Fin 3 → F} (hP : W.NonsingularLift P)
    (hQ : W.Nonsingular Q) (hQz : Q z = 0) : W.addMap P ⟦Q⟧ = P := by
  rcases P with ⟨P⟩
  by_cases hPz : P z = 0
  · erw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
      smul_eq _ <| (isUnit_Y_of_Z_eq_zero hP hPz).pow 4, Quotient.eq]
    exact Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
  · erw [addMap_eq, add_of_Z_eq_zero_right hQ.left hPz hQz,
      smul_eq _ (((isUnit_Y_of_Z_eq_zero hQ hQz).pow 2).mul <| Ne.isUnit hPz).neg]
    rfl

lemma addMap_of_Y_eq {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z = Q x * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.addMap ⟦P⟧ ⟦Q⟧ = ⟦![0, 1, 0]⟧ := by
  by_cases hy : P y * Q z = Q y * P z
  · rw [addMap_eq, add_of_Y_eq hP.left hPz hQz hx hy hy',
      smul_eq _ <| isUnit_dblU_of_Y_eq hP hPz hQz hx hy hy']
  · rw [addMap_eq, add_of_Y_ne hP.left hQ hPz hQz hx hy,
      smul_eq _ <| isUnit_addU_of_Y_ne hPz hQz hy]

lemma addMap_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hxy : ¬(P x * Q z = Q x * P z ∧ P y * Q z = W.negY Q * P z)) :
    W.addMap ⟦P⟧ ⟦Q⟧ =
      ⟦![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)), 1]⟧ := by
  by_cases hx : P x * Q z = Q x * P z
  · rw [addMap_eq, add_of_Y_ne' hP hQ hPz hQz hx <| not_and.mp hxy hx,
      smul_eq _ <| isUnit_dblZ_of_Y_ne' hP hQ hPz hQz hx <| not_and.mp hxy hx]
  · rw [addMap_eq, add_of_X_ne hP hQ hPz hQz hx, smul_eq _ <| isUnit_addZ_of_X_ne hP hQ hx]

lemma nonsingularLift_addMap {P Q : PointClass F} (hP : W.NonsingularLift P)
    (hQ : W.NonsingularLift Q) : W.NonsingularLift <| W.addMap P Q := by
  rcases P; rcases Q
  exact nonsingular_add hP hQ

end Addition

/-! ### Nonsingular rational points -/

variable (W') in
/-- A nonsingular projective point on a Weierstrass curve `W`. -/
@[ext]
structure Point where
  /-- The projective point class underlying a nonsingular projective point on `W`. -/
  {point : PointClass R}
  /-- The nonsingular condition underlying a nonsingular projective point on `W`. -/
  (nonsingular : W'.NonsingularLift point)

namespace Point

lemma mk_point {P : PointClass R} (h : W'.NonsingularLift P) : (mk h).point = P :=
  rfl

instance instZeroPoint [Nontrivial R] : Zero W'.Point :=
  ⟨⟨nonsingularLift_zero⟩⟩

lemma zero_def [Nontrivial R] : (0 : W'.Point) = ⟨nonsingularLift_zero⟩ :=
  rfl

lemma zero_point [Nontrivial R] : (0 : W'.Point).point = ⟦![0, 1, 0]⟧ :=
  rfl

/-- The natural map from a nonsingular point on a Weierstrass curve in affine coordinates to its
corresponding nonsingular projective point. -/
def fromAffine [Nontrivial R] : W'.toAffine.Point → W'.Point
  | 0 => 0
  | .some h => ⟨(nonsingularLift_some ..).mpr h⟩

lemma fromAffine_zero [Nontrivial R] : fromAffine 0 = (0 : W'.Point) :=
  rfl

lemma fromAffine_some [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y) :
    fromAffine (.some h) = ⟨(nonsingularLift_some ..).mpr h⟩ :=
  rfl

lemma fromAffine_ne_zero [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y) :
    fromAffine (.some h) ≠ 0 := fun h0 ↦ by
  obtain ⟨u, eq⟩ := Quotient.eq.mp <| (Point.ext_iff ..).mp h0
  simpa [Units.smul_def, smul_fin3] using congr_fun eq z

/-- The negation of a nonsingular projective point on a Weierstrass curve `W`.

Given a nonsingular projective point `P` on `W`, use `-P` instead of `neg P`. -/
def neg (P : W.Point) : W.Point :=
  ⟨nonsingularLift_negMap P.nonsingular⟩

instance instNegPoint : Neg W.Point :=
  ⟨neg⟩

lemma neg_def (P : W.Point) : -P = P.neg :=
  rfl

lemma neg_point (P : W.Point) : (-P).point = W.negMap P.point :=
  rfl

/-- The addition of two nonsingular projective points on a Weierstrass curve `W`.

Given two nonsingular projective points `P` and `Q` on `W`, use `P + Q` instead of `add P Q`. -/
noncomputable def add (P Q : W.Point) : W.Point :=
  ⟨nonsingularLift_addMap P.nonsingular Q.nonsingular⟩

noncomputable instance instAddPoint : Add W.Point :=
  ⟨add⟩

lemma add_def (P Q : W.Point) : P + Q = P.add Q :=
  rfl

lemma add_point (P Q : W.Point) : (P + Q).point = W.addMap P.point Q.point :=
  rfl

end Point

section Affine

/-! ### Equivalence with affine coordinates -/

namespace Point

open Classical in
variable (W) in
/-- The natural map from a nonsingular projective point representative on a Weierstrass curve to its
corresponding nonsingular point in affine coordinates. -/
noncomputable def toAffine (P : Fin 3 → F) : W.toAffine.Point :=
  if hP : W.Nonsingular P ∧ P z ≠ 0 then .some <| (nonsingular_of_Z_ne_zero hP.2).mp hP.1 else 0

lemma toAffine_of_singular {P : Fin 3 → F} (hP : ¬W.Nonsingular P) : toAffine W P = 0 := by
  rw [toAffine, dif_neg <| not_and_of_not_left _ hP]

lemma toAffine_of_Z_eq_zero {P : Fin 3 → F} (hPz : P z = 0) : toAffine W P = 0 := by
  rw [toAffine, dif_neg <| not_and_not_right.mpr fun _ => hPz]

lemma toAffine_zero : toAffine W ![0, 1, 0] = 0 :=
  toAffine_of_Z_eq_zero rfl

lemma toAffine_of_Z_ne_zero {P : Fin 3 → F} (hP : W.Nonsingular P) (hPz : P z ≠ 0) :
    toAffine W P = .some ((nonsingular_of_Z_ne_zero hPz).mp hP) := by
  rw [toAffine, dif_pos ⟨hP, hPz⟩]

lemma toAffine_some {X Y : F} (h : W.Nonsingular ![X, Y, 1]) :
    toAffine W ![X, Y, 1] = .some ((nonsingular_some ..).mp h) := by
  simp only [toAffine_of_Z_ne_zero h one_ne_zero, fin3_def_ext, one_pow, div_one]

lemma toAffine_smul (P : Fin 3 → F) {u : F} (hu : IsUnit u) :
    toAffine W (u • P) = toAffine W P := by
  by_cases hP : W.Nonsingular P
  · by_cases hPz : P z = 0
    · rw [toAffine_of_Z_eq_zero <| mul_eq_zero_of_right u hPz, toAffine_of_Z_eq_zero hPz]
    · rw [toAffine_of_Z_ne_zero ((nonsingular_smul P hu).mpr hP) <| mul_ne_zero hu.ne_zero hPz,
        toAffine_of_Z_ne_zero hP hPz, Affine.Point.some.injEq]
      simp only [smul_fin3_ext, mul_div_mul_left _ _ hu.ne_zero, and_self]
  · rw [toAffine_of_singular <| hP.comp (nonsingular_smul P hu).mp, toAffine_of_singular hP]

lemma toAffine_of_equiv {P Q : Fin 3 → F} (h : P ≈ Q) : toAffine W P = toAffine W Q := by
  rcases h with ⟨u, rfl⟩
  exact toAffine_smul Q u.isUnit

lemma toAffine_neg {P : Fin 3 → F} (hP : W.Nonsingular P) :
    toAffine W (W.neg P) = -toAffine W P := by
  by_cases hPz : P z = 0
  · rw [neg_of_Z_eq_zero hP.left hPz, toAffine_smul _ (isUnit_Y_of_Z_eq_zero hP hPz).neg,
      toAffine_zero, toAffine_of_Z_eq_zero hPz, Affine.Point.neg_zero]
  · rw [neg_of_Z_ne_zero hPz, toAffine_smul _ <| Ne.isUnit hPz, toAffine_some <|
        (nonsingular_smul _ <| Ne.isUnit hPz).mp <| neg_of_Z_ne_zero hPz ▸ nonsingular_neg hP,
      toAffine_of_Z_ne_zero hP hPz, Affine.Point.neg_some]

private lemma toAffine_add_of_Z_ne_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hxy : ¬(P x * Q z = Q x * P z ∧ P y * Q z = W.negY Q * P z)) : toAffine W
      ![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        1] = toAffine W P + toAffine W Q := by
  rw [toAffine_some <| nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy, toAffine_of_Z_ne_zero hP hPz,
    toAffine_of_Z_ne_zero hQ hQz,
    Affine.Point.add_some <| by rwa [← X_eq_iff hPz hQz, ← Y_eq_iff' hPz hQz]]

lemma toAffine_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    toAffine W (W.add P Q) = toAffine W P + toAffine W Q := by
  by_cases hPz : P z = 0
  · rw [toAffine_of_Z_eq_zero hPz, zero_add]
    by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero hP hQ hPz hQz, toAffine_smul _ <| (isUnit_Y_of_Z_eq_zero hP hPz).pow 4,
        toAffine_zero, toAffine_of_Z_eq_zero hQz]
    · rw [add_of_Z_eq_zero_left hP.left hPz hQz,
        toAffine_smul _ <| ((isUnit_Y_of_Z_eq_zero hP hPz).pow 2).mul <| Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero_right hQ.left hPz hQz,
        toAffine_smul _ (((isUnit_Y_of_Z_eq_zero hQ hQz).pow 2).mul <| Ne.isUnit hPz).neg,
        toAffine_of_Z_eq_zero hQz, add_zero]
    · by_cases hxy : P x * Q z = Q x * P z ∧ P y * Q z = W.negY Q * P z
      · rw [toAffine_of_Z_ne_zero hP hPz, toAffine_of_Z_ne_zero hQ hQz, Affine.Point.add_of_Y_eq
            ((X_eq_iff hPz hQz).mp hxy.left) ((Y_eq_iff' hPz hQz).mp hxy.right)]
        by_cases hy : P y * Q z = Q y * P z
        · rw [add_of_Y_eq hP.left hPz hQz hxy.left hy hxy.right,
            toAffine_smul _ <| isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, toAffine_zero]
        · rw [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
            toAffine_smul _ <| isUnit_addU_of_Y_ne hPz hQz hy, toAffine_zero]
      · have := toAffine_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z = Q x * P z
        · rwa [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
            toAffine_smul _ <| isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx]
        · rwa [add_of_X_ne hP.left hQ.left hPz hQz hx,
            toAffine_smul _ <| isUnit_addZ_of_X_ne hP.left hQ.left hx]

/-- The natural map from a nonsingular projective point on a Weierstrass curve `W` to its
corresponding nonsingular point in affine coordinates.

If `hP` is the nonsingular condition underlying a nonsingular projective point `P` on `W`, then
`toAffineLift ⟨hP⟩` is definitionally equivalent to `toAffine W P`. -/
noncomputable def toAffineLift (P : W.Point) : W.toAffine.Point :=
  P.point.lift _ fun _ _ => toAffine_of_equiv

lemma toAffineLift_eq {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) :
    toAffineLift ⟨hP⟩ = toAffine W P :=
  rfl

lemma toAffineLift_of_Z_eq_zero {P : Fin 3 → F} (hP : W.NonsingularLift ⟦P⟧) (hPz : P z = 0) :
    toAffineLift ⟨hP⟩ = 0 :=
  toAffine_of_Z_eq_zero hPz

lemma toAffineLift_zero : toAffineLift (0 : W.Point) = 0 :=
  toAffine_zero

lemma toAffineLift_of_Z_ne_zero {P : Fin 3 → F} {hP : W.NonsingularLift ⟦P⟧} (hPz : P z ≠ 0) :
    toAffineLift ⟨hP⟩ = .some ((nonsingular_of_Z_ne_zero hPz).mp hP) :=
  toAffine_of_Z_ne_zero hP hPz

lemma toAffineLift_some {X Y : F} (h : W.NonsingularLift ⟦![X, Y, 1]⟧) :
    toAffineLift ⟨h⟩ = .some ((nonsingular_some ..).mp h) :=
  toAffine_some h

lemma toAffineLift_neg (P : W.Point) : (-P).toAffineLift = -P.toAffineLift := by
  rcases P with @⟨⟨_⟩, hP⟩
  exact toAffine_neg hP

lemma toAffineLift_add (P Q : W.Point) :
    (P + Q).toAffineLift = P.toAffineLift + Q.toAffineLift := by
  rcases P, Q with ⟨@⟨⟨_⟩, hP⟩, @⟨⟨_⟩, hQ⟩⟩
  exact toAffine_add hP hQ

variable (W) in
/-- The addition-preserving equivalence between the type of nonsingular projective points on a
Weierstrass curve `W` and the type of nonsingular points `W⟮F⟯` in affine coordinates. -/
@[simps]
noncomputable def toAffineAddEquiv : W.Point ≃+ W.toAffine.Point where
  toFun := toAffineLift
  invFun := fromAffine
  left_inv := by
    rintro @⟨⟨P⟩, hP⟩
    by_cases hPz : P z = 0
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_eq_zero hPz]
      exact Quotient.eq.mpr <| Setoid.symm <| equiv_zero_of_Z_eq_zero hP hPz
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_ne_zero hP hPz]
      exact Quotient.eq.mpr <| Setoid.symm <| equiv_some_of_Z_ne_zero hPz
  right_inv := by
    rintro (_ | _)
    · erw [fromAffine_zero, toAffineLift_zero, Affine.Point.zero_def]
    · rw [fromAffine_some, toAffineLift_some]
  map_add' := toAffineLift_add

end Point

end Affine

section Map

/-! ### Maps across ring homomorphisms -/

variable {S : Type v} [CommRing S] (f : R →+* S)

@[simp]
lemma map_polynomial : (W'.map f).toProjective.polynomial = MvPolynomial.map f W'.polynomial := by
  simp only [polynomial]
  map_simp

lemma Equation.map {P : Fin 3 → R} (h : W'.Equation P) :
    (W'.map f).toProjective.Equation (f ∘ P) := by
  rw [Equation, map_polynomial, eval_map, ← eval₂_comp, ← map_zero f]
  exact congr_arg f h

variable {f} in
@[simp]
lemma map_equation (hf : Function.Injective f) (P : Fin 3 → R) :
    (W'.map f).toProjective.Equation (f ∘ P) ↔ W'.Equation P := by
  simp only [Equation, map_polynomial, eval_map, ← eval₂_comp, map_eq_zero_iff f hf]

@[simp]
lemma map_polynomialX :
    (W'.map f).toProjective.polynomialX = MvPolynomial.map f W'.polynomialX := by
  simp only [polynomialX, map_polynomial, pderiv_map]

@[simp]
lemma map_polynomialY :
    (W'.map f).toProjective.polynomialY = MvPolynomial.map f W'.polynomialY := by
  simp only [polynomialY, map_polynomial, pderiv_map]

@[simp]
lemma map_polynomialZ :
    (W'.map f).toProjective.polynomialZ = MvPolynomial.map f W'.polynomialZ := by
  simp only [polynomialZ, map_polynomial, pderiv_map]

variable {f} in
@[simp]
lemma map_nonsingular (hf : Function.Injective f) (P : Fin 3 → R) :
    (W'.map f).toProjective.Nonsingular (f ∘ P) ↔ W'.Nonsingular P := by
  simp only [Nonsingular, map_equation hf, map_polynomialX, map_polynomialY, map_polynomialZ,
    eval_map, ← eval₂_comp, map_ne_zero_iff f hf]

@[simp]
lemma map_negY (P : Fin 3 → R) : (W'.map f).toProjective.negY (f ∘ P) = f (W'.negY P) := by
  simp only [negY]
  map_simp

@[simp]
protected lemma map_neg (P : Fin 3 → R) : (W'.map f).toProjective.neg (f ∘ P) = f ∘ W'.neg P := by
  simp only [neg, map_negY, comp_fin3]
  map_simp

@[simp]
lemma map_dblU {K : Type v} [Field K] (f : F →+* K) (P : Fin 3 → F) :
    (W.map f).toProjective.dblU (f ∘ P) = f (W.dblU P) := by
  simp only [dblU_eq]
  map_simp

@[simp]
lemma map_dblZ (P : Fin 3 → R) : (W'.map f).toProjective.dblZ (f ∘ P) = f (W'.dblZ P) := by
  simp only [dblZ, negY]
  map_simp

@[simp]
lemma map_dblX (P : Fin 3 → R) : (W'.map f).toProjective.dblX (f ∘ P) = f (W'.dblX P) := by
  simp only [dblX, map_dblU, map_negY]
  map_simp

@[simp]
lemma map_negDblY (P : Fin 3 → R) : (W'.map f).toProjective.negDblY (f ∘ P) = f (W'.negDblY P) := by
  simp only [negDblY, map_dblU, map_dblX, map_negY]
  map_simp

@[simp]
lemma map_dblY (P : Fin 3 → R) : (W'.map f).toProjective.dblY (f ∘ P) = f (W'.dblY P) := by
  simp only [dblY, negY_eq, map_negDblY, map_dblX, map_dblZ]
  map_simp

@[simp]
lemma map_dblXYZ (P : Fin 3 → R) : (W'.map f).toProjective.dblXYZ (f ∘ P) = f ∘ dblXYZ W' P := by
  simp only [dblXYZ, map_dblX, map_dblY, map_dblZ, comp_fin3]

@[simp]
lemma map_addU {K : Type v} [Field K] (f : F →+* K) (P Q : Fin 3 → F) :
    addU (f ∘ P) (f ∘ Q) = f (addU P Q) := by
  simp only [addU]
  map_simp

@[simp]
lemma map_addZ (P Q : Fin 3 → R) :
    (W'.map f).toProjective.addZ (f ∘ P) (f ∘ Q) = f (W'.addZ P Q) := by
  simp only [addZ]
  map_simp

@[simp]
lemma map_addX (P Q : Fin 3 → R) :
    (W'.map f).toProjective.addX (f ∘ P) (f ∘ Q) = f (W'.addX P Q) := by
  simp only [addX]
  map_simp

@[simp]
lemma map_negAddY (P Q : Fin 3 → R) :
    (W'.map f).toProjective.negAddY (f ∘ P) (f ∘ Q) = f (W'.negAddY P Q) := by
  simp only [negAddY]
  map_simp

@[simp]
lemma map_addY (P Q : Fin 3 → R) :
    (W'.map f).toProjective.addY (f ∘ P) (f ∘ Q) = f (W'.addY P Q) := by
  simp only [addY, negY_eq, map_negAddY, map_addX, map_addZ]
  map_simp

@[simp]
lemma map_addXYZ (P Q : Fin 3 → R) :
    (W'.map f).toProjective.addXYZ (f ∘ P) (f ∘ Q) = f ∘ addXYZ W' P Q := by
  simp only [addXYZ, map_addX, map_addY, map_addZ, comp_fin3]

@[simp]
protected lemma map_add {K : Type v} [Field K] (f : F →+* K) {P Q : Fin 3 → F}
    (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    (W.map f).toProjective.add (f ∘ P) (f ∘ Q) = f ∘ W.add P Q := by
  by_cases h : P ≈ Q
  · rw [add_of_equiv <| (comp_equiv_comp f hP hQ).mpr h, add_of_equiv h, map_dblXYZ]
  · rw [add_of_not_equiv <| h.comp (comp_equiv_comp f hP hQ).mp, add_of_not_equiv h, map_addXYZ]

end Map

section BaseChange

/-! ### Base changes across algebra homomorphisms -/

variable {R : Type r} [CommRing R] (W' : Projective R) {S : Type s} [CommRing S] [Algebra R S]
  {A : Type u} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  {B : Type v} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[S] B)

lemma baseChange_polynomial : (W'.baseChange B).toProjective.polynomial =
    MvPolynomial.map f (W'.baseChange A).toProjective.polynomial := by
  rw [← map_polynomial, map_baseChange]

variable {f} in
lemma baseChange_equation (hf : Function.Injective f) (P : Fin 3 → A) :
    (W'.baseChange B).toProjective.Equation (f ∘ P) ↔
      (W'.baseChange A).toProjective.Equation P := by
  rw [← RingHom.coe_coe, ← map_equation hf, AlgHom.toRingHom_eq_coe, map_baseChange]

lemma baseChange_polynomialX : (W'.baseChange B).toProjective.polynomialX =
    MvPolynomial.map f (W'.baseChange A).toProjective.polynomialX := by
  rw [← map_polynomialX, map_baseChange]

lemma baseChange_polynomialY : (W'.baseChange B).toProjective.polynomialY =
    MvPolynomial.map f (W'.baseChange A).toProjective.polynomialY := by
  rw [← map_polynomialY, map_baseChange]

lemma baseChange_polynomialZ : (W'.baseChange B).toProjective.polynomialZ =
    MvPolynomial.map f (W'.baseChange A).toProjective.polynomialZ := by
  rw [← map_polynomialZ, map_baseChange]

variable {f} in
lemma baseChange_nonsingular (hf : Function.Injective f) (P : Fin 3 → A) :
    (W'.baseChange B).toProjective.Nonsingular (f ∘ P) ↔
      (W'.baseChange A).toProjective.Nonsingular P := by
  rw [← RingHom.coe_coe, ← map_nonsingular hf, AlgHom.toRingHom_eq_coe, map_baseChange]

lemma baseChange_negY (P : Fin 3 → A) :
    (W'.baseChange B).toProjective.negY (f ∘ P) = f ((W'.baseChange A).toProjective.negY P) := by
  rw [← RingHom.coe_coe, ← map_negY, map_baseChange]

lemma baseChange_neg (P : Fin 3 → A) :
    (W'.baseChange B).toProjective.neg (f ∘ P) = f ∘ (W'.baseChange A).toProjective.neg P := by
  rw [← RingHom.coe_coe, ← WeierstrassCurve.Projective.map_neg, map_baseChange]

lemma baseChange_dblZ (P : Fin 3 → A) : (W'.baseChange B).toProjective.dblZ (f ∘ P) =
    f ((W'.baseChange A).toProjective.dblZ P) := by
  rw [← RingHom.coe_coe, ← map_dblZ, map_baseChange]

lemma baseChange_dblX (P : Fin 3 → A) : (W'.baseChange B).toProjective.dblX (f ∘ P) =
    f ((W'.baseChange A).toProjective.dblX P) := by
  rw [← RingHom.coe_coe, ← map_dblX, map_baseChange]

lemma baseChange_negDblY (P : Fin 3 → A) : (W'.baseChange B).toProjective.negDblY (f ∘ P) =
    f ((W'.baseChange A).toProjective.negDblY P) := by
  rw [← RingHom.coe_coe, ← map_negDblY, map_baseChange]

lemma baseChange_dblY (P : Fin 3 → A) : (W'.baseChange B).toProjective.dblY (f ∘ P) =
    f ((W'.baseChange A).toProjective.dblY P) := by
  rw [← RingHom.coe_coe, ← map_dblY, map_baseChange]

lemma baseChange_dblXYZ (P : Fin 3 → A) : (W'.baseChange B).toProjective.dblXYZ (f ∘ P) =
    f ∘ (W'.baseChange A).toProjective.dblXYZ P := by
  rw [← RingHom.coe_coe, ← map_dblXYZ, map_baseChange]

lemma baseChange_addX (P Q : Fin 3 → A) : (W'.baseChange B).toProjective.addX (f ∘ P) (f ∘ Q) =
    f ((W'.baseChange A).toProjective.addX P Q) := by
  rw [← RingHom.coe_coe, ← map_addX, map_baseChange]

lemma baseChange_negAddY (P Q : Fin 3 → A) :
    (W'.baseChange B).toProjective.negAddY (f ∘ P) (f ∘ Q) =
      f ((W'.baseChange A).toProjective.negAddY P Q) := by
  rw [← RingHom.coe_coe, ← map_negAddY, map_baseChange]

lemma baseChange_addY (P Q : Fin 3 → A) : (W'.baseChange B).toProjective.addY (f ∘ P) (f ∘ Q) =
    f ((W'.baseChange A).toProjective.addY P Q) := by
  rw [← RingHom.coe_coe, ← map_addY, map_baseChange]

lemma baseChange_addXYZ (P Q : Fin 3 → A) : (W'.baseChange B).toProjective.addXYZ (f ∘ P) (f ∘ Q) =
    f ∘ (W'.baseChange A).toProjective.addXYZ P Q := by
  rw [← RingHom.coe_coe, ← map_addXYZ, map_baseChange]

variable [Algebra R F] [Algebra S F] [IsScalarTower R S F] {K : Type v} [Field K] [Algebra R K]
  [Algebra S K] [IsScalarTower R S K] (f : F →ₐ[S] K)

lemma baseChange_dblU (P : Fin 3 → F) : (W'.baseChange K).toProjective.dblU (f ∘ P) =
    f ((W'.baseChange F).toProjective.dblU P) := by
  rw [← RingHom.coe_coe, ← map_dblU, map_baseChange]

lemma baseChange_add {P Q : Fin 3 → F} (hP : (W'.baseChange F).toProjective.Nonsingular P)
    (hQ : (W'.baseChange F).toProjective.Nonsingular Q) :
    (W'.baseChange K).toProjective.add (f ∘ P) (f ∘ Q) =
      f ∘ (W'.baseChange F).toProjective.add P Q := by
  rw [← RingHom.coe_coe, ← WeierstrassCurve.Projective.map_add f hP hQ (K := K), map_baseChange]

end BaseChange

end WeierstrassCurve.Projective

/-- An abbreviation for `WeierstrassCurve.Projective.Point.fromAffine` for dot notation. -/
abbrev WeierstrassCurve.Affine.Point.toProjective {R : Type u} [CommRing R] [Nontrivial R]
    {W : Affine R} (P : W.Point) : W.toProjective.Point :=
  Projective.Point.fromAffine P

set_option linter.style.longFile 2100
