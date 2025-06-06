/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# Weierstrass equations and the nonsingular condition in Jacobian coordinates

A point on the projective plane over a commutative ring `R` with weights `(2, 3, 1)` is an
equivalence class `[x : y : z]` of triples `(x, y, z) ≠ (0, 0, 0)` of elements in `R` such that
`(x, y, z) ∼ (x', y', z')` if there is some unit `u` in `Rˣ` with `(x, y, z) = (u²x', u³y', uz')`.

Let `W` be a Weierstrass curve over a commutative ring `R` with coefficients `aᵢ`. A
*Jacobian point* is a point on the projective plane over `R` with weights `(2, 3, 1)` satisfying the
*`(2, 3, 1)`-homogeneous Weierstrass equation* `W(X, Y, Z) = 0` in *Jacobian coordinates*, where
`W(X, Y, Z) := Y² + a₁XYZ + a₃YZ³ - (X³ + a₂X²Z² + a₄XZ⁴ + a₆Z⁶)`. It is *nonsingular* if the ideal
spanned by its partial derivatives `W_X(x, y, z)`, `W_Y(x, y, z)`, and `W_Z(x, y, z)` is `R`.

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

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Basic.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, Jacobian, Weierstrass equation, nonsingular
-/

local notation3 P " x" => Prod.fst P

local notation3 P " y" => Prod.fst (Prod.snd P)

local notation3 P " z" => Prod.snd (Prod.snd P)

local notation3 f " ∘ " P:51 => Prod.map f (Prod.map f f) P

open MvPolynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_C, map_X, map_neg, map_add, map_sub, map_mul, map_pow,
    map_div₀, Prod.map_snd, Prod.map_fst, WeierstrassCurve.map])

local macro "pderiv_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, pderiv_mul, pderiv_pow,
    pderiv_C, pderiv_X_self,
    pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 1), pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 0),
    pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 2), pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0),
    pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 2), pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 1)])

universe r s u v

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v}

namespace WeierstrassCurve

/-! ## Jacobian coordinates -/

variable (R) in
/-- An abbreviation for a Weierstrass curve in Jacobian coordinates. -/
abbrev Jacobian : Type r :=
  WeierstrassCurve R

/-- The conversion from a Weierstrass curve to Jacobian coordinates. -/
abbrev toJacobian (W' : WeierstrassCurve R) : Jacobian R :=
  W'

namespace Jacobian

/-- The conversion from a Weierstrass curve in Jacobian coordinates to affine coordinates. -/
abbrev toAffine (W' : Jacobian R) : Affine R :=
  W'

lemma map_eq (f : R → S) (P : R × R × R) : f ∘ P = (f (P x), f (P y), f (P z)) := by
  rfl

lemma map_fin3 (f : R → S) (P : R × R × R) :
    f ∘ ![P x, P y, P z] = ![f (P x), f (P y), f (P z)] := by
  ext n; fin_cases n <;> simp

@[deprecated (since := "2025-05-04")] alias comp_fin3 := map_fin3
@[deprecated (since := "2025-05-04")] alias comp_smul := map_fin3

variable [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Field F] [Field K] {W' : Jacobian R}
  {W : Jacobian F}

/-- The scalar multiplication for a Jacobian point representative on a Weierstrass curve. -/
scoped instance : SMul R <| R × R × R :=
  ⟨fun u P => (u ^ 2 * P x, u ^ 3 * P y, u * P z)⟩

lemma smul_eq (P : R × R × R) (u : R) : u • P = (u ^ 2 * P x, u ^ 3 * P y, u * P z) :=
  rfl

@[deprecated (since := "2025-05-04")] alias fin3_def := smul_eq
@[deprecated (since := "2025-05-04")] alias fin3_def_ext := smul_eq
@[deprecated (since := "2025-05-04")] alias smul_fin3 := smul_eq
@[deprecated (since := "2025-05-04")] alias smul_fin3_ext := smul_eq

protected lemma map_smul (f : R →* S) (P : R × R × R) (u : R) : f ∘ u • P = f u • f ∘ P := by
  simp_rw [map_eq, smul_eq, map_mul, map_pow]

/-- The multiplicative action for a Jacobian point representative on a Weierstrass curve. -/
scoped instance : MulAction R <| R × R × R where
  one_smul _ := by simp_rw [smul_eq, one_pow, one_mul]
  mul_smul _ _ _ := by simp_rw [smul_eq, mul_pow, mul_assoc]

/-- The equivalence setoid for a Jacobian point representative on a Weierstrass curve. -/
@[reducible]
scoped instance : Setoid <| R × R × R :=
  MulAction.orbitRel Rˣ <| R × R × R

variable (R) in
/-- The equivalence class of a Jacobian point representative on a Weierstrass curve. -/
abbrev PointClass : Type r :=
  MulAction.orbitRel.Quotient Rˣ <| R × R × R

lemma smul_equiv (P : R × R × R) {u : R} (hu : IsUnit u) : u • P ≈ P :=
  ⟨hu.unit, rfl⟩

lemma mk_smul (P : R × R × R) {u : R} (hu : IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧ :=
  Quotient.eq.mpr <| smul_equiv P hu

lemma smul_equiv_smul (P Q : R × R × R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    u • P ≈ v • Q ↔ P ≈ Q := by
  rw [← Quotient.eq_iff_equiv, ← Quotient.eq_iff_equiv, mk_smul P hu, mk_smul Q hv]

lemma equiv_iff_eq_of_Z_eq {P Q : R × R × R} (hz : P z = Q z) (hQz : IsUnit <| Q z) :
    P ≈ Q ↔ P = Q := by
  refine ⟨?_, Quotient.exact.comp <| congrArg _⟩
  rintro ⟨_, rfl⟩
  simp_rw [Units.smul_def, hQz.mul_eq_right.mp hz, one_smul]

@[deprecated (since := "2025-05-26")] alias equiv_iff_eq_of_Z_eq' := equiv_iff_eq_of_Z_eq

lemma Z_eq_zero_of_equiv {P Q : R × R × R} (h : P ≈ Q) : P z = 0 ↔ Q z = 0 := by
  rcases h with ⟨u, rfl⟩
  exact u.mul_right_eq_zero

lemma X_eq_of_equiv {P Q : R × R × R} (h : P ≈ Q) : P x * Q z ^ 2 = Q x * P z ^ 2 := by
  rcases h with ⟨_, rfl⟩
  simp_rw [Units.smul_def, smul_eq]
  ring1

lemma Y_eq_of_equiv {P Q : R × R × R} (h : P ≈ Q) : P y * Q z ^ 3 = Q y * P z ^ 3 := by
  rcases h with ⟨_, rfl⟩
  simp_rw [Units.smul_def, smul_eq]
  ring1

lemma not_equiv_of_Z_eq_zero_left {P Q : R × R × R} (hPz : P z = 0) (hQz : Q z ≠ 0) : ¬P ≈ Q :=
  fun h => hQz <| (Z_eq_zero_of_equiv h).mp hPz

lemma not_equiv_of_Z_eq_zero_right {P Q : R × R × R} (hPz : P z ≠ 0) (hQz : Q z = 0) : ¬P ≈ Q :=
  fun h => hPz <| (Z_eq_zero_of_equiv h).mpr hQz

lemma not_equiv_of_X_ne {P Q : R × R × R} (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : ¬P ≈ Q :=
  hx.comp X_eq_of_equiv

lemma not_equiv_of_Y_ne {P Q : R × R × R} (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) : ¬P ≈ Q :=
  hy.comp Y_eq_of_equiv

lemma equiv_of_X_eq_of_Y_eq {P Q : R × R × R} (hPz : IsUnit <| P z) (hQz : IsUnit <| Q z)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3) : P ≈ Q := by
  use hPz.unit * hQz.unit⁻¹
  simp_rw [Units.smul_def, smul_eq, Units.val_mul, mul_pow, mul_comm, ← mul_assoc, hPz.unit_spec,
    ← hx, ← hy, mul_assoc, ← mul_pow, hQz.mul_val_inv, one_pow, mul_one, mul_comm <| Q z, mul_assoc,
    hQz.val_inv_mul, mul_one]

lemma equiv_some_of_isUnit_Z {P : R × R × R} (hPz : IsUnit <| P z) :
    P ≈ (P x * hPz.unit⁻¹ ^ 2, P y * hPz.unit⁻¹ ^ 3, 1) := by
  simp_rw [← Units.inv_pow_eq_pow_inv, ← hPz.unit_pow]
  exact equiv_of_X_eq_of_Y_eq hPz isUnit_one
    (by linear_combination (norm := ring1) -P x * (hPz.pow 2).mul_val_inv)
    (by linear_combination (norm := ring1) -P y * (hPz.pow 3).mul_val_inv)

lemma equiv_some_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) :
    P ≈ (P x / P z ^ 2, P y / P z ^ 3, 1) := by
  convert equiv_some_of_isUnit_Z hPz.isUnit using 1
  simp_rw [Units.val_inv_eq_inv_val, IsUnit.unit_spec, inv_pow, div_eq_mul_inv]

lemma X_eq_of_isUnit_Z {P Q : R × R × R} (hPz : IsUnit <| P z) (hQz : IsUnit <| Q z) :
    P x * Q z ^ 2 = Q x * P z ^ 2 ↔ P x * hPz.unit⁻¹ ^ 2 = Q x * hQz.unit⁻¹ ^ 2 :=
  (Units.mul_inv_eq_mul_inv_iff _ _ (hPz.unit ^ 2) (hQz.unit ^ 2)).symm

@[deprecated (since := "2025-05-26")] alias X_eq_iff := X_eq_of_isUnit_Z

lemma X_eq_of_Z_ne_zero {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P x * Q z ^ 2 = Q x * P z ^ 2 ↔ P x / P z ^ 2 = Q x / Q z ^ 2 :=
  (div_eq_div_iff (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz)).symm

lemma Y_eq_of_isUnit_Z {P Q : R × R × R} (hPz : IsUnit <| P z) (hQz : IsUnit <| Q z) :
    P y * Q z ^ 3 = Q y * P z ^ 3 ↔ P y * hPz.unit⁻¹ ^ 3 = Q y * hQz.unit⁻¹ ^ 3 :=
  (Units.mul_inv_eq_mul_inv_iff _ _ (hPz.unit ^ 3) (hQz.unit ^ 3)).symm

@[deprecated (since := "2025-05-26")] alias Y_eq_iff := Y_eq_of_isUnit_Z

lemma Y_eq_of_Z_ne_zero {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P y * Q z ^ 3 = Q y * P z ^ 3 ↔ P y / P z ^ 3 = Q y / Q z ^ 3 :=
  (div_eq_div_iff (pow_ne_zero 3 hPz) (pow_ne_zero 3 hQz)).symm

/-! ## Weierstrass equations in Jacobian coordinates -/

variable (W') in
/-- The polynomial `W(X, Y, Z) := Y² + a₁XYZ + a₃YZ³ - (X³ + a₂X²Z² + a₄XZ⁴ + a₆Z⁶)` associated to a
Weierstrass curve `W` over a ring `R` in Jacobian coordinates.

This is represented as a term of type `MvPolynomial (Fin 3) R`, where `X 0`, `X 1`, and `X 2`
represent `X`, `Y`, and `Z` respectively. -/
noncomputable def polynomial : MvPolynomial (Fin 3) R :=
  X 1 ^ 2 + C W'.a₁ * X 0 * X 1 * X 2 + C W'.a₃ * X 1 * X 2 ^ 3
    - (X 0 ^ 3 + C W'.a₂ * X 0 ^ 2 * X 2 ^ 2 + C W'.a₄ * X 0 * X 2 ^ 4 + C W'.a₆ * X 2 ^ 6)

lemma eval_polynomial (P : R × R × R) : eval ![P x, P y, P z] W'.polynomial =
    P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 3
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z ^ 2 + W'.a₄ * P x * P z ^ 4 + W'.a₆ * P z ^ 6) := by
  rw [polynomial]
  eval_simp
  rfl

lemma eval_polynomial_of_isUnit_Z {P : R × R × R} (hPz : IsUnit <| P z) :
    eval ![P x, P y, P z] W'.polynomial =
      W'.toAffine.polynomial.evalEval (P x * hPz.unit⁻¹ ^ 2) (P y * hPz.unit⁻¹ ^ 3) * P z ^ 6 := by
  rw [eval_polynomial, Affine.evalEval_polynomial]
  linear_combination (norm := (simp_rw [hPz.unit_pow, Units.inv_pow_eq_pow_inv]; ring1))
    -P y ^ 2 * (hPz.pow 6).mul_val_inv - W'.a₁ * P x * P y * P z * (hPz.pow 5).mul_val_inv
      - W'.a₃ * P y * P z ^ 3 * (hPz.pow 3).mul_val_inv + P x ^ 3 * (hPz.pow 6).mul_val_inv
      + W'.a₂ * P x ^ 2 * P z ^ 2 * (hPz.pow 4).mul_val_inv
      + W'.a₄ * P x * P z ^ 4 * (hPz.pow 2).mul_val_inv

lemma eval_polynomial_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) :
    eval ![P x, P y, P z] W.polynomial =
      W.toAffine.polynomial.evalEval (P x / P z ^ 2) (P y / P z ^ 3) * P z ^ 6 := by
  simp_rw [div_eq_mul_inv, ← inv_pow]
  convert eval_polynomial_of_isUnit_Z hPz.isUnit using 5 <;>
    exact hPz.isUnit.unit.val_inv_eq_inv_val.symm

variable (W') in
/-- The proposition that a Jacobian point representative `(x, y, z)` lies in a Weierstrass curve
`W`.

In other words, it satisfies the `(2, 3, 1)`-homogeneous Weierstrass equation `W(X, Y, Z) = 0`. -/
def Equation (P : R × R × R) : Prop :=
  eval ![P x, P y, P z] W'.polynomial = 0

lemma equation_iff (P : R × R × R) : W'.Equation P ↔
    P y ^ 2 + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 3
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z ^ 2 + W'.a₄ * P x * P z ^ 4 + W'.a₆ * P z ^ 6) = 0 := by
  rw [Equation, eval_polynomial]

lemma equation_smul (P : R × R × R) {u : R} (hu : IsUnit u) : W'.Equation (u • P) ↔ W'.Equation P :=
  have hP (u : R) {P : R × R × R} (hP : W'.Equation P) : W'.Equation <| u • P := by
    rw [equation_iff] at hP ⊢
    linear_combination (norm := (rw [smul_eq]; ring1)) u ^ 6 * hP
  ⟨fun h => by convert hP ↑hu.unit⁻¹ h; rw [smul_smul, hu.val_inv_mul, one_smul], hP u⟩

lemma equation_of_equiv {P Q : R × R × R} (h : P ≈ Q) : W'.Equation P ↔ W'.Equation Q := by
  rcases h with ⟨u, rfl⟩
  exact equation_smul Q u.isUnit

lemma equation_of_Z_eq_zero {P : R × R × R} (hPz : P z = 0) :
    W'.Equation P ↔ P y ^ 2 = P x ^ 3 := by
  simp_rw [equation_iff, hPz, sub_eq_zero, zero_pow <| OfNat.ofNat_ne_zero _, mul_zero, add_zero]

lemma equation_zero : W'.Equation (1, 1, 0) := by
  simp_rw [equation_of_Z_eq_zero, one_pow]

lemma equation_some (X Y : R) : W'.Equation (X, Y, 1) ↔ W'.toAffine.Equation X Y := by
  simp_rw [equation_iff, Affine.equation_iff', one_pow, mul_one]

lemma equation_of_isUnit_Z {P : R × R × R} (hPz : IsUnit <| P z) :
    W'.Equation P ↔ W'.toAffine.Equation (P x * hPz.unit⁻¹ ^ 2) (P y * hPz.unit⁻¹ ^ 3) :=
  (equation_of_equiv <| equiv_some_of_isUnit_Z hPz).trans <| equation_some ..

lemma equation_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) :
    W.Equation P ↔ W.toAffine.Equation (P x / P z ^ 2) (P y / P z ^ 3) := by
  simp_rw [div_eq_mul_inv, ← inv_pow]
  convert equation_of_isUnit_Z hPz.isUnit using 4 <;> exact hPz.isUnit.unit.val_inv_eq_inv_val.symm

/-! ## The nonsingular condition in Jacobian coordinates -/

variable (W') in
/-- The partial derivative `W_X(X, Y, Z)` with respect to `X` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates. -/
noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  pderiv 0 W'.polynomial

lemma polynomialX_eq : W'.polynomialX =
    C W'.a₁ * X 1 * X 2 - (C 3 * X 0 ^ 2 + C (2 * W'.a₂) * X 0 * X 2 ^ 2 + C W'.a₄ * X 2 ^ 4) := by
  rw [polynomialX, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialX (P : R × R × R) : eval ![P x, P y, P z] W'.polynomialX =
    W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z ^ 2 + W'.a₄ * P z ^ 4) := by
  rw [polynomialX_eq]
  eval_simp
  rfl

lemma eval_polynomialX_of_isUnit_Z {P : R × R × R} (hPz : IsUnit <| P z) :
    eval ![P x, P y, P z] W'.polynomialX =
      W'.toAffine.polynomialX.evalEval (P x * hPz.unit⁻¹ ^ 2) (P y * hPz.unit⁻¹ ^ 3) * P z ^ 4 := by
  rw [eval_polynomialX, Affine.evalEval_polynomialX]
  linear_combination (norm := (simp_rw [hPz.unit_pow, Units.inv_pow_eq_pow_inv]; ring1))
    -W'.a₁ * P y * P z * (hPz.pow 3).mul_val_inv + 3 * P x ^ 2 * (hPz.pow 4).mul_val_inv
      + 2 * W'.a₂ * P x * P z ^ 2 * (hPz.pow 2).mul_val_inv

lemma eval_polynomialX_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) :
    eval ![P x, P y, P z] W.polynomialX =
      W.toAffine.polynomialX.evalEval (P x / P z ^ 2) (P y / P z ^ 3) * P z ^ 4 := by
  simp_rw [div_eq_mul_inv, ← inv_pow]
  convert eval_polynomialX_of_isUnit_Z hPz.isUnit using 5 <;>
    exact hPz.isUnit.unit.val_inv_eq_inv_val.symm

variable (W') in
/-- The partial derivative `W_Y(X, Y, Z)` with respect to `Y` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates. -/
noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  pderiv 1 W'.polynomial

lemma polynomialY_eq : W'.polynomialY = C 2 * X 1 + C W'.a₁ * X 0 * X 2 + C W'.a₃ * X 2 ^ 3 := by
  rw [polynomialY, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialY (P : R × R × R) :
    eval ![P x, P y, P z] W'.polynomialY = 2 * P y + W'.a₁ * P x * P z + W'.a₃ * P z ^ 3 := by
  rw [polynomialY_eq]
  eval_simp
  rfl

lemma eval_polynomialY_of_isUnit_Z {P : R × R × R} (hPz : IsUnit <| P z) :
    eval ![P x, P y, P z] W'.polynomialY =
      W'.toAffine.polynomialY.evalEval (P x * hPz.unit⁻¹ ^ 2) (P y * hPz.unit⁻¹ ^ 3) * P z ^ 3 := by
  rw [eval_polynomialY, Affine.evalEval_polynomialY]
  linear_combination (norm := (simp_rw [hPz.unit_pow, Units.inv_pow_eq_pow_inv]; ring1))
    -2 * P y * (hPz.pow 3).mul_val_inv - W'.a₁ * P x * P z * (hPz.pow 2).mul_val_inv

lemma eval_polynomialY_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) :
    eval ![P x, P y, P z] W.polynomialY =
      W.toAffine.polynomialY.evalEval (P x / P z ^ 2) (P y / P z ^ 3) * P z ^ 3 := by
  simp_rw [div_eq_mul_inv, ← inv_pow]
  convert eval_polynomialY_of_isUnit_Z hPz.isUnit using 5 <;>
    exact hPz.isUnit.unit.val_inv_eq_inv_val.symm

variable (W') in
/-- The partial derivative `W_Z(X, Y, Z)` with respect to `Z` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in Jacobian coordinates. -/
noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  pderiv 2 W'.polynomial

lemma polynomialZ_eq : W'.polynomialZ = C W'.a₁ * X 0 * X 1 + C (3 * W'.a₃) * X 1 * X 2 ^ 2 -
    (C (2 * W'.a₂) * X 0 ^ 2 * X 2 + C (4 * W'.a₄) * X 0 * X 2 ^ 3 + C (6 * W'.a₆) * X 2 ^ 5) := by
  rw [polynomialZ, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialZ (P : R × R × R) : eval ![P x, P y, P z] W'.polynomialZ =
    W'.a₁ * P x * P y + 3 * W'.a₃ * P y * P z ^ 2 -
      (2 * W'.a₂ * P x ^ 2 * P z + 4 * W'.a₄ * P x * P z ^ 3 + 6 * W'.a₆ * P z ^ 5) := by
  rw [polynomialZ_eq]
  eval_simp
  rfl

/-- Euler's homogeneous function theorem in Jacobian coordinates. -/
theorem polynomial_relation (P : R × R × R) : 6 * eval ![P x, P y, P z] W'.polynomial =
    2 * P x * eval ![P x, P y, P z] W'.polynomialX +
      3 * P y * eval ![P x, P y, P z] W'.polynomialY +
      P z * eval ![P x, P y, P z] W'.polynomialZ := by
  rw [eval_polynomial, eval_polynomialX, eval_polynomialY, eval_polynomialZ]
  ring1

variable (W') in
/-- The proposition that a Jacobian point representative `(x, y, z)` on a Weierstrass curve `W` is
nonsingular.

In other words, the ideal spanned by `W_X(x, y, z)`, `W_Y(x, y, z)`, and `W_z(x, y, z)` is `R`.

Note that this definition is only mathematically accurate for certain rings `R` whose Picard group
has trivial 12-torsion, such as a field or a PID. -/
def Nonsingular (P : R × R × R) : Prop :=
  W'.Equation P ∧ Ideal.span {eval ![P x, P y, P z] W'.polynomialX,
    eval ![P x, P y, P z] W'.polynomialY, eval ![P x, P y, P z] W'.polynomialZ} = ⊤

lemma nonsingular_iff (P : R × R × R) : W'.Nonsingular P ↔ W'.Equation P ∧ Ideal.span
    {W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z ^ 2 + W'.a₄ * P z ^ 4),
      2 * P y + W'.a₁ * P x * P z + W'.a₃ * P z ^ 3,
      W'.a₁ * P x * P y + 3 * W'.a₃ * P y * P z ^ 2
        - (2 * W'.a₂ * P x ^ 2 * P z + 4 * W'.a₄ * P x * P z ^ 3 + 6 * W'.a₆ * P z ^ 5)} = ⊤ := by
  rw [Nonsingular, eval_polynomialX, eval_polynomialY, eval_polynomialZ]

lemma nonsingular_smul (P : R × R × R) {u : R} (hu : IsUnit u) :
    W'.Nonsingular (u • P) ↔ W'.Nonsingular P :=
  have hP {u : R} (hu : IsUnit u) {P : R × R × R} (hP : W'.Nonsingular <| u • P) :
      W'.Nonsingular P := by
    rcases (nonsingular_iff _).mp hP with ⟨hP, hP'⟩
    refine (nonsingular_iff P).mpr ⟨(equation_smul P hu).mp hP, ?_⟩
    simp_rw [Ideal.span_insert, ← Ideal.span_singleton_mul_left_unit (hu.pow 4) <| _ * _ - _,
      ← Ideal.span_singleton_mul_left_unit (hu.pow 3) <| _ + _,
      ← Ideal.span_singleton_mul_left_unit (hu.pow 5) <| _ - _, ← hP', smul_eq, Ideal.span_insert]
    ring_nf
  ⟨hP hu, fun h => hP hu.unit⁻¹.isUnit <| by rwa [smul_smul, hu.val_inv_mul, one_smul]⟩

lemma nonsingular_of_equiv {P Q : R × R × R} (h : P ≈ Q) : W'.Nonsingular P ↔ W'.Nonsingular Q := by
  rcases h with ⟨u, rfl⟩
  exact nonsingular_smul Q u.isUnit

lemma nonsingular_of_Z_eq_zero {P : R × R × R} (hPz : P z = 0) : W'.Nonsingular P ↔
    W'.Equation P ∧ Ideal.span {3 * P x ^ 2, 2 * P y, W'.a₁ * P x * P y} = ⊤ := by
  simp_rw [nonsingular_iff, hPz, zero_pow <| OfNat.ofNat_ne_zero _, mul_zero, zero_sub, add_zero,
    sub_zero, Ideal.span_insert, Ideal.span_singleton_neg]

lemma nonsingular_zero : W'.Nonsingular (1, 1, 0) := by
  simp_rw [nonsingular_of_Z_eq_zero, Ideal.eq_top_iff_one, Ideal.mem_span_insert',
    Ideal.mem_span_singleton']
  exact ⟨equation_zero, ⟨-1, 1, 0, by ring1⟩⟩

lemma nonsingular_some (X Y : R) : W'.Nonsingular (X, Y, 1) ↔ W'.toAffine.Nonsingular X Y := by
  simp_rw [nonsingular_iff, equation_some, Affine.nonsingular_iff, Affine.equation_iff',
    and_congr_right_iff, Ideal.span_insert, ← sup_assoc, ← Ideal.span_insert, one_pow, mul_one]
  intro h
  congr! 1
  rw [sup_eq_left, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_pair]
  exact ⟨-2 * X, -3 * Y, by linear_combination (norm := ring1) -6 * h⟩

lemma nonsingular_of_isUnit_Z {P : R × R × R} (hPz : IsUnit <| P z) :
    W'.Nonsingular P ↔ W'.toAffine.Nonsingular (P x * hPz.unit⁻¹ ^ 2) (P y * hPz.unit⁻¹ ^ 3) :=
  (nonsingular_of_equiv <| equiv_some_of_isUnit_Z hPz).trans <| nonsingular_some ..

lemma nonsingular_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.toAffine.Nonsingular (P x / P z ^ 2) (P y / P z ^ 3) := by
  simp_rw [div_eq_mul_inv, ← inv_pow]
  convert nonsingular_of_isUnit_Z hPz.isUnit using 4 <;>
    exact hPz.isUnit.unit.val_inv_eq_inv_val.symm

lemma nonsingular_iff_of_isUnit_Z {P : R × R × R} (hPz : IsUnit <| P z) : W'.Nonsingular P ↔
    W'.Equation P ∧ Ideal.span {eval ![P x, P y, P z] W'.polynomialX,
      eval ![P x, P y, P z] W'.polynomialY} = ⊤ := by
  simp_rw [nonsingular_of_isUnit_Z hPz, Affine.Nonsingular, ← equation_of_isUnit_Z hPz,
    eval_polynomialX_of_isUnit_Z hPz, eval_polynomialY_of_isUnit_Z hPz, Ideal.span_insert,
    Ideal.span_singleton_mul_right_unit <| hPz.pow _]

@[deprecated (since := "2025-05-26")] alias nonsingular_iff_of_Z_ne_zero :=
  nonsingular_iff_of_isUnit_Z

lemma isCoprime_X_Y_of_Z_eq_zero {P : R × R × R} (hP : W'.Nonsingular P) (hPz : P z = 0) :
    IsCoprime (P x) (P y) := by
  simp_rw [nonsingular_of_Z_eq_zero hPz, equation_of_Z_eq_zero hPz, Ideal.eq_top_iff_one,
    Ideal.mem_span_insert, Ideal.mem_span_singleton'] at hP
  rcases hP with ⟨h, a, _, ⟨b, _, ⟨c, rfl⟩, rfl⟩, h'⟩
  exact ⟨3 * P x * a, 2 * b + W'.a₁ * P x * c, by linear_combination (norm := ring1) -h'⟩

lemma isUnit_X_of_Z_eq_zero {P : R × R × R} (hP : W'.Nonsingular P) (hPz : P z = 0) :
    IsUnit <| P x := by
  rw [← isCoprime_self, ← IsCoprime.pow_right_iff three_pos,
    ← (equation_of_Z_eq_zero hPz).mp ((nonsingular_of_Z_eq_zero hPz).mp hP).left]
  exact (isCoprime_X_Y_of_Z_eq_zero hP hPz).pow_right

@[deprecated (since := "2025-05-26")] alias X_ne_zero_of_Z_eq_zero := isUnit_X_of_Z_eq_zero

lemma isUnit_Y_of_Z_eq_zero {P : R × R × R} (hP : W'.Nonsingular P) (hPz : P z = 0) :
    IsUnit <| P y := by
  rw [← isCoprime_self, ← IsCoprime.pow_left_iff two_pos,
    (equation_of_Z_eq_zero hPz).mp ((nonsingular_of_Z_eq_zero hPz).mp hP).left]
  exact (isCoprime_X_Y_of_Z_eq_zero hP hPz).pow_left

@[deprecated (since := "2025-05-26")] alias Y_ne_zero_of_Z_eq_zero := isUnit_Y_of_Z_eq_zero

lemma equiv_of_Z_eq_zero {P Q : R × R × R} (hP : W'.Nonsingular P) (hQ : W'.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : P ≈ Q := by
  use (isUnit_Y_of_Z_eq_zero hP hPz).unit * (isUnit_X_of_Z_eq_zero hP hPz).unit⁻¹
    * ((isUnit_Y_of_Z_eq_zero hQ hQz).unit⁻¹ * (isUnit_X_of_Z_eq_zero hQ hQz).unit)
  simp only [nonsingular_of_Z_eq_zero, equation_of_Z_eq_zero, hPz, hQz] at hP hQ
  simp_rw [Units.smul_def, smul_eq, Units.val_mul, IsUnit.unit_spec, mul_pow, hQz, mul_zero]
  congr! 2
  · rw [hP.left, pow_succ', mul_assoc <| P x, ← mul_pow, IsUnit.mul_val_inv, one_pow, mul_one,
      mul_assoc, mul_assoc, ← pow_succ, ← hQ.left, ← mul_pow, IsUnit.val_inv_mul, one_pow, mul_one]
  · rw [pow_succ', hP.left, mul_assoc <| P y, ← mul_pow, IsUnit.mul_val_inv, one_pow, mul_one,
      mul_assoc, mul_assoc, ← hQ.left, ← pow_succ, ← mul_pow, IsUnit.val_inv_mul, one_pow, mul_one]
  · exact hPz.symm

lemma equiv_zero_of_Z_eq_zero {P : R × R × R} (hP : W'.Nonsingular P) (hPz : P z = 0) :
    P ≈ (1, 1, 0) :=
  equiv_of_Z_eq_zero hP nonsingular_zero hPz rfl

lemma map_equiv_map (f : F →+* K) {P Q : F × F × F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    f ∘ P ≈ f ∘ Q ↔ P ≈ Q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hz : f (P z) = 0
    · exact equiv_of_Z_eq_zero hP hQ ((map_eq_zero_iff f f.injective).mp hz) <|
        (map_eq_zero_iff f f.injective).mp <| (Z_eq_zero_of_equiv h).mp hz
    · refine equiv_of_X_eq_of_Y_eq ((map_ne_zero_iff f f.injective).mp hz).isUnit
        ((map_ne_zero_iff f f.injective).mp <| hz.comp (Z_eq_zero_of_equiv h).mpr).isUnit ?_ ?_
      all_goals apply f.injective; map_simp
      exacts [X_eq_of_equiv h, Y_eq_of_equiv h]
  · rcases h with ⟨u, rfl⟩
    exact ⟨Units.map f u, (WeierstrassCurve.Jacobian.map_smul ..).symm⟩

@[deprecated (since := "2025-05-04")] alias comp_equiv_comp := map_equiv_map

variable (W') in
/-- The proposition that a Jacobian point class on a Weierstrass curve `W` is nonsingular.

If `P` is a Jacobian point representative on `W`, then `W.NonsingularLift ⟦P⟧` is definitionally
equivalent to `W.Nonsingular P`.

Note that this definition is only mathematically accurate for certain rings `R` whose Picard group
has trivial 12-torsion, such as a field or a PID. -/
def NonsingularLift (P : PointClass R) : Prop :=
  P.lift W'.Nonsingular fun _ _ => propext ∘ nonsingular_of_equiv

lemma nonsingularLift_iff (P : R × R × R) : W'.NonsingularLift ⟦P⟧ ↔ W'.Nonsingular P :=
  Iff.rfl

lemma nonsingularLift_zero : W'.NonsingularLift ⟦(1, 1, 0)⟧ :=
  nonsingular_zero

lemma nonsingularLift_some (X Y : R) :
    W'.NonsingularLift ⟦(X, Y, 1)⟧ ↔ W'.toAffine.Nonsingular X Y :=
  nonsingular_some X Y

/-! ## Maps and base changes -/

variable (f : R →+* S) (P : R × R × R)

@[simp]
lemma map_polynomial : (W'.map f).toJacobian.polynomial = W'.polynomial.map f := by
  simp_rw [polynomial]
  map_simp

variable {P} in
lemma Equation.map (h : W'.Equation P) : (W'.map f).toJacobian.Equation <| f ∘ P := by
  rw [Equation, map_polynomial, eval_map, map_eq, ← map_fin3, ← eval₂_comp, h, map_zero]

variable {f} in
@[simp]
lemma map_equation (hf : Function.Injective f) :
    (W'.map f).toJacobian.Equation (f ∘ P) ↔ W'.Equation P := by
  simp_rw [Equation, map_polynomial, eval_map, map_eq, ← map_fin3, ← eval₂_comp,
    map_eq_zero_iff f hf]

@[simp]
lemma map_polynomialX : (W'.map f).toJacobian.polynomialX = W'.polynomialX.map f := by
  simp_rw [polynomialX, map_polynomial, pderiv_map]

@[simp]
lemma map_polynomialY : (W'.map f).toJacobian.polynomialY = W'.polynomialY.map f := by
  simp_rw [polynomialY, map_polynomial, pderiv_map]

@[simp]
lemma map_polynomialZ : (W'.map f).toJacobian.polynomialZ = W'.polynomialZ.map f := by
  simp_rw [polynomialZ, map_polynomial, pderiv_map]

variable {P} in
lemma Nonsingular.map (h : W'.Nonsingular P) : (W'.map f).toJacobian.Nonsingular <| f ∘ P := by
  simp_rw [Nonsingular, h.left.map f, true_and, map_polynomialX, map_polynomialY, map_polynomialZ,
    eval_map, map_eq, ← map_fin3, ← eval₂_comp, ← Set.image_pair f, ← Set.image_insert_eq,
    ← Ideal.map_span, h.right, Ideal.map_top]

variable {f} in
@[simp]
lemma map_nonsingular (hf : Function.Bijective f) :
    (W'.map f).toJacobian.Nonsingular (f ∘ P) ↔ W'.Nonsingular P := by
  refine ⟨?_, fun h => h.map f⟩
  simp_rw [Nonsingular, map_equation _ hf.left, map_polynomialX, map_polynomialY, map_polynomialZ,
    eval_map, map_eq, ← map_fin3, ← eval₂_comp, ← Set.image_pair f, ← Set.image_insert_eq,
    ← Ideal.map_span, Ideal.map_span_triple_eq_top hf, imp_self]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A →ₐ[S] B) (P : A × A × A)

lemma baseChange_polynomial :
    (W'.baseChange B).toJacobian.polynomial = (W'.baseChange A).toJacobian.polynomial.map f := by
  rw [← map_polynomial, map_baseChange]

variable {P} in
lemma Equation.baseChange (h : (W'.baseChange A).toJacobian.Equation P) :
    (W'.baseChange B).toJacobian.Equation <| f ∘ P := by
  convert h.map f.toRingHom using 1
  rw [AlgHom.toRingHom_eq_coe, map_baseChange]

variable {f} in
lemma baseChange_equation (hf : Function.Injective f) :
    (W'.baseChange B).toJacobian.Equation (f ∘ P) ↔ (W'.baseChange A).toJacobian.Equation P := by
  rw [← RingHom.coe_coe, ← map_equation P hf, AlgHom.toRingHom_eq_coe, map_baseChange]

lemma baseChange_polynomialX :
    (W'.baseChange B).toJacobian.polynomialX = (W'.baseChange A).toJacobian.polynomialX.map f := by
  rw [← map_polynomialX, map_baseChange]

lemma baseChange_polynomialY :
    (W'.baseChange B).toJacobian.polynomialY = (W'.baseChange A).toJacobian.polynomialY.map f := by
  rw [← map_polynomialY, map_baseChange]

lemma baseChange_polynomialZ :
    (W'.baseChange B).toJacobian.polynomialZ = (W'.baseChange A).toJacobian.polynomialZ.map f := by
  rw [← map_polynomialZ, map_baseChange]

variable {P} in
lemma Nonsingular.baseChange (h : (W'.baseChange A).toJacobian.Nonsingular P) :
    (W'.baseChange B).toJacobian.Nonsingular <| f ∘ P := by
  convert h.map f.toRingHom using 1
  rw [AlgHom.toRingHom_eq_coe, map_baseChange]

variable {f} in
lemma baseChange_nonsingular (hf : Function.Bijective f) :
    (W'.baseChange B).toJacobian.Nonsingular (f ∘ P) ↔
      (W'.baseChange A).toJacobian.Nonsingular P := by
  rw [← RingHom.coe_coe, ← map_nonsingular P hf, AlgHom.toRingHom_eq_coe, map_baseChange]

end Jacobian

end WeierstrassCurve
