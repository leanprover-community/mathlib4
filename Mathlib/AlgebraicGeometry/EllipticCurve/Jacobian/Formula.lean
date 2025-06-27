/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Basic

/-!
# Negation and addition formulae for nonsingular points in Jacobian coordinates

Let `W` be a Weierstrass curve over a field `F`. The nonsingular Jacobian points on `W` can be given
negation and addition operations defined by an analogue of the secant-and-tangent process in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`, but the polynomials involved are
`(2, 3, 1)`-homogeneous, so any instances of division become multiplication in the `Z`-coordinate.
Most computational proofs are immediate from their analogous proofs for affine coordinates.

This file defines polynomials associated to negation, doubling, and addition of Jacobian point
representatives. The group operations and the group law on actual nonsingular Jacobian points will
be defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean`.

## Main definitions

* `WeierstrassCurve.Jacobian.negY`: the `Y`-coordinate of `-P`.
* `WeierstrassCurve.Jacobian.dblZ`: the `Z`-coordinate of `2 • P`.
* `WeierstrassCurve.Jacobian.dblX`: the `X`-coordinate of `2 • P`.
* `WeierstrassCurve.Jacobian.negDblY`: the `Y`-coordinate of `-(2 • P)`.
* `WeierstrassCurve.Jacobian.dblY`: the `Y`-coordinate of `2 • P`.
* `WeierstrassCurve.Jacobian.addZ`: the `Z`-coordinate of `P + Q`.
* `WeierstrassCurve.Jacobian.addX`: the `X`-coordinate of `P + Q`.
* `WeierstrassCurve.Jacobian.negAddY`: the `Y`-coordinate of `-(P + Q)`.
* `WeierstrassCurve.Jacobian.addY`: the `Y`-coordinate of `P + Q`.

## Implementation notes

The definitions of `WeierstrassCurve.Jacobian.addX` and `WeierstrassCurve.Jacobian.negAddY` are
given explicitly by large polynomials that are homogeneous of degrees `8` and `12` respectively.
Clearing the denominators of their corresponding affine rational functions in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean` would give polynomials that are
homogeneous of degrees `12` and `18` respectively, so their actual definitions are off by powers of
a certain polynomial factor that is homogeneous of degree `2`. This factor divides their
corresponding affine polynomials only modulo the `(2, 3, 1)`-homogeneous Weierstrass equation, so
their large quotient polynomials are calculated explicitly in a computer algebra system. All of this
is done to ensure that the definitions of both `WeierstrassCurve.Jacobian.dblXYZ` and
`WeierstrassCurve.Jacobian.addXYZ` are `(2, 3, 1)`-homogeneous of degree `4`.

For ease of naming, the following conventions will be used in theorems about nonsingular Jacobian
points `P` and `Q` on a Weierstrass curve `W` over a commutative ring `R`.
* `Y_eq'` is the condition `P y * Q z ^ 3 = W.negY Q * P z ^ 3` assuming `X_eq`.
* `Y_ne'` is the condition `IsUnit <| P y * Q z ^ 3 - W.negY Q * P z ^ 3` (which is equivalent to
  `P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3` if `R` is a field) assuming `X_eq`.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, Jacobian, negation, doubling, addition, group law
-/

local notation3 P " x" => Prod.fst P

local notation3 P " y" => Prod.fst (Prod.snd P)

local notation3 P " z" => Prod.snd (Prod.snd P)

local notation3 f " ∘ " P:51 => Prod.map f (Prod.map f f) P

open MvPolynomial

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_C, map_X, map_neg, map_add, map_sub, map_mul, map_pow,
    map_div₀, Prod.map_snd, Prod.map_fst, WeierstrassCurve.map])

universe r s u v

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Field F] [Field K] {W' : Jacobian R} {W : Jacobian F}

namespace Jacobian

/-! ## Negation formulae in Jacobian coordinates -/

variable (W') in
/-- The `Y`-coordinate of a representative of `-P` for a Jacobian point representative `P` on a
Weierstrass curve. -/
def negY (P : R × R × R) : R :=
  -P y - W'.a₁ * P x * P z - W'.a₃ * P z ^ 3

@[deprecated (since := "2025-05-04")] alias negY_eq := negY

lemma negY_smul (P : R × R × R) (u : R) : W'.negY (u • P) = u ^ 3 * W'.negY P := by
  simp_rw [negY, smul_eq]
  ring1

lemma negY_of_Z_eq_zero {P : R × R × R} (hPz : P z = 0) : W'.negY P = -P y := by
  rw [negY, hPz, mul_zero, sub_zero, zero_pow three_ne_zero, mul_zero, sub_zero]

lemma negY_of_isUnit_Z {P : R × R × R} (hPz : IsUnit <| P z) :
    W'.negY P = W'.toAffine.negY (P x * hPz.unit⁻¹ ^ 2) (P y * hPz.unit⁻¹ ^ 3) * P z ^ 3 := by
  linear_combination
    (norm := (simp_rw [negY, Affine.negY, hPz.unit_pow, Units.inv_pow_eq_pow_inv]; ring1))
    P y * (hPz.pow 3).mul_val_inv + W'.a₁ * P x * P z * (hPz.pow 2).mul_val_inv

lemma negY_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) :
    W.negY P = W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3) * P z ^ 3 := by
  simp_rw [negY_of_isUnit_Z hPz.isUnit, Units.val_inv_eq_inv_val, IsUnit.unit_spec, inv_pow,
    div_eq_mul_inv]

lemma Y_sub_Y_mul_Y_sub_negY_of_X_eq {P Q : R × R × R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    (P y * Q z ^ 3 - Q y * P z ^ 3) * (P y * Q z ^ 3 - W'.negY Q * P z ^ 3) = 0 := by
  linear_combination (norm := (rw [negY]; ring1)) Q z ^ 6 * (equation_iff P).mp hP
    - P z ^ 6 * (equation_iff Q).mp hQ + (P x ^ 2 * Q z ^ 4 + P x * Q x * P z ^ 2 * Q z ^ 2
      + Q x ^ 2 * P z ^ 4 - W'.a₁ * P y * P z * Q z ^ 4 + W'.a₂ * P x * P z ^ 2 * Q z ^ 4
      + W'.a₂ * Q x * P z ^ 4 * Q z ^ 2 + W'.a₄ * P z ^ 4 * Q z ^ 4) * hx

@[deprecated (since := "2025-05-26")] alias Y_sub_Y_mul_Y_sub_negY := Y_sub_Y_mul_Y_sub_negY_of_X_eq

lemma Y_eq_or_Y_eq'_of_X_eq [NoZeroDivisors R] {P Q : R × R × R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    P y * Q z ^ 3 = Q y * P z ^ 3 ∨ P y * Q z ^ 3 = W'.negY Q * P z ^ 3 := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := _ * _), ← mul_eq_zero,
    Y_sub_Y_mul_Y_sub_negY_of_X_eq hP hQ hx]

lemma Y_eq'_of_Y_ne {P Q : R × R × R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : IsUnit <| P y * Q z ^ 3 - Q y * P z ^ 3) :
    P y * Q z ^ 3 = W'.negY Q * P z ^ 3 :=
  sub_eq_zero.mp <| hy.mul_right_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY_of_X_eq hP hQ hx

@[deprecated (since := "2025-05-26")] alias Y_eq_of_Y_ne := Y_eq'_of_Y_ne

lemma Y_eq_of_Y_ne' {P Q : R × R × R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : IsUnit <| P y * Q z ^ 3 - W'.negY Q * P z ^ 3) :
    P y * Q z ^ 3 = Q y * P z ^ 3 :=
  sub_eq_zero.mp <| hy.mul_left_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY_of_X_eq hP hQ hx

lemma Y_sub_negY_of_isUnit_Z {P Q : R × R × R} (hPz : IsUnit <| P z) (hQz : IsUnit <| Q z) :
    P y * Q z ^ 3 - W'.negY Q * P z ^ 3 = P z ^ 3 * Q z ^ 3 *
      (P y * hPz.unit⁻¹ ^ 3 - W'.toAffine.negY (Q x * hQz.unit⁻¹ ^ 2) (Q y * hQz.unit⁻¹ ^ 3)) := by
  rw [mul_comm <| _ ^ 3, mul_comm <| _ * _, sub_mul, mul_mul_mul_comm, ← mul_pow, hPz.val_inv_mul,
    one_pow, mul_one, ← mul_assoc, ← negY_of_isUnit_Z hQz]

lemma Y_sub_negY_of_Z_ne_zero {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P y * Q z ^ 3 - W.negY Q * P z ^ 3 =
      P z ^ 3 * Q z ^ 3 * (P y / P z ^ 3 - W.toAffine.negY (Q x / Q z ^ 2) (Q y / Q z ^ 3)) := by
  simp_rw [Y_sub_negY_of_isUnit_Z hPz.isUnit hQz.isUnit, Units.val_inv_eq_inv_val, IsUnit.unit_spec,
    inv_pow, div_eq_mul_inv]

lemma Y_eq'_iff_of_isUnit_Z {P Q : R × R × R} (hPz : IsUnit <| P z) (hQz : IsUnit <| Q z) :
    P y * Q z ^ 3 = W'.negY Q * P z ^ 3 ↔
      P y * hPz.unit⁻¹ ^ 3 = W'.toAffine.negY (Q x * hQz.unit⁻¹ ^ 2) (Q y * hQz.unit⁻¹ ^ 3) := by
  rw [← sub_eq_zero, Y_sub_negY_of_isUnit_Z hPz hQz,
    ((hPz.pow 3).mul (hQz.pow 3)).mul_right_eq_zero, sub_eq_zero]

@[deprecated (since := "2025-05-26")] alias Y_eq_iff' := Y_eq'_iff_of_isUnit_Z

lemma Y_eq'_iff_of_Z_ne_zero {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P y * Q z ^ 3 = W.negY Q * P z ^ 3 ↔
      P y / P z ^ 3 = W.toAffine.negY (Q x / Q z ^ 2) (Q y / Q z ^ 3) := by
  simp_rw [Y_eq'_iff_of_isUnit_Z hPz.isUnit hQz.isUnit, Units.val_inv_eq_inv_val, IsUnit.unit_spec,
    inv_pow, div_eq_mul_inv]

lemma Y_ne'_iff_of_isUnit_Z {P Q : R × R × R} (hPz : IsUnit <| P z) (hQz : IsUnit <| Q z) :
    IsUnit (P y * Q z ^ 3 - W'.negY Q * P z ^ 3) ↔ IsUnit
      (P y * hPz.unit⁻¹ ^ 3 - W'.toAffine.negY (Q x * hQz.unit⁻¹ ^ 2) (Q y * hQz.unit⁻¹ ^ 3)) := by
  simp_rw [Y_sub_negY_of_isUnit_Z hPz hQz, IsUnit.mul_iff, isUnit_pow_iff three_ne_zero, hPz, hQz,
    true_and]

lemma Y_ne'_iff_of_Z_ne_zero {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3 ↔
      P y / P z ^ 3 ≠ W.toAffine.negY (Q x / Q z ^ 2) (Q y / Q z ^ 3) := by
  rw [ne_eq, Y_eq'_iff_of_Z_ne_zero hPz hQz]

lemma Y_sub_Y_add_Y_sub_negY_of_X_eq {P Q : R × R × R} (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    (P y * Q z ^ 3 - Q y * P z ^ 3) + (P y * Q z ^ 3 - W'.negY Q * P z ^ 3) =
      (P y - W'.negY P) * Q z ^ 3 := by
  linear_combination (norm := (rw [negY, negY]; ring1)) -W'.a₁ * P z * Q z * hx

@[deprecated (since := "2025-05-26")] alias Y_sub_Y_add_Y_sub_negY := Y_sub_Y_add_Y_sub_negY_of_X_eq

lemma isUnit_Y_sub_negY_of_Y_ne {P Q : R × R × R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : IsUnit <| P y * Q z ^ 3 - Q y * P z ^ 3) :
    IsUnit <| P y - W'.negY P :=
  isUnit_of_mul_isUnit_left <| by
    rwa [← Y_sub_Y_add_Y_sub_negY_of_X_eq hx, ← Y_eq'_of_Y_ne hP hQ hx hy, sub_self, add_zero]

@[deprecated (since := "2025-05-26")] alias Y_ne_negY_of_Y_ne := isUnit_Y_sub_negY_of_Y_ne

lemma isUnit_Y_sub_negY_of_Y_ne' {P Q : R × R × R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : IsUnit <| P y * Q z ^ 3 - W'.negY Q * P z ^ 3) :
    IsUnit <| P y - W'.negY P :=
  isUnit_of_mul_isUnit_left <| by
    rwa [← Y_sub_Y_add_Y_sub_negY_of_X_eq hx, ← Y_eq_of_Y_ne' hP hQ hx hy, sub_self, zero_add]

@[deprecated (since := "2025-05-26")] alias Y_ne_negY_of_Y_ne' := isUnit_Y_sub_negY_of_Y_ne'

lemma Y_eq_negY_of_Y_eq_of_Y_eq' {P Q : R × R × R} (hQz : IsUnit <| Q z)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W'.negY Q * P z ^ 3) : P y = W'.negY P :=
  (hQz.pow 3).mul_left_injective <| by
    linear_combination (norm := ring1) -Y_sub_Y_add_Y_sub_negY_of_X_eq hx + hy + hy'

@[deprecated (since := "2025-05-26")] alias Y_ne_negY_of_Y_eq := Y_eq_negY_of_Y_eq_of_Y_eq'

lemma nonsingular_iff_of_Y_eq_negY {P : R × R × R} (hPz : IsUnit <| P z) (hy : P y = W'.negY P) :
    W'.Nonsingular P ↔ W'.Equation P ∧ IsUnit (eval ![P x, P y, P z] W'.polynomialX) := by
  rw [nonsingular_iff_of_isUnit_Z hPz, ← Ideal.span_singleton_eq_top, ← Ideal.span_pair_zero]
  congr! 5
  linear_combination (norm := (rw [eval_polynomialY, negY]; ring1)) hy

/-! ## Doubling formulae in Jacobian coordinates -/

variable (W') in
/-- The unit associated to a representative of `2 • P` for a Jacobian point representative `P` on a
Weierstrass curve `W` that is `2`-torsion.

More specifically, the unit `u` such that `W.add P P = u • (1, 1, 0)` where `P = W.neg P`. -/
noncomputable def dblU (P : R × R × R) : R :=
  eval ![P x, P y, P z] W'.polynomialX

lemma dblU_eq (P : R × R × R) : W'.dblU P =
    W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z ^ 2 + W'.a₄ * P z ^ 4) := by
  rw [dblU, eval_polynomialX]

lemma dblU_smul (P : R × R × R) (u : R) : W'.dblU (u • P) = u ^ 4 * W'.dblU P :=
  eval_polynomialX_smul ..

lemma dblU_of_Z_eq_zero {P : R × R × R} (hPz : P z = 0) : W'.dblU P = -3 * P x ^ 2 := by
  simp_rw [dblU_eq, hPz, zero_pow <| OfNat.ofNat_ne_zero _, mul_zero, zero_sub, add_zero, neg_mul]

lemma dblU_of_isUnit_Z {P : R × R × R} (hPz : IsUnit <| P z) :
    W'.dblU P = (W'.a₁ * (P y * hPz.unit⁻¹ ^ 3) - (3 * (P x * hPz.unit⁻¹ ^ 2) ^ 2
      + 2 * W'.a₂ * (P x * hPz.unit⁻¹ ^ 2) + W'.a₄)) * P z ^ 4 := by
  rw [dblU, eval_polynomialX_of_isUnit_Z hPz, Affine.evalEval_polynomialX]

lemma dblU_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) : W.dblU P = (W.a₁ * (P y / P z ^ 3) -
    (3 * (P x / P z ^ 2) ^ 2 + 2 * W.a₂ * (P x / P z ^ 2) + W.a₄)) * P z ^ 4 := by
  simp_rw [dblU_of_isUnit_Z hPz.isUnit, Units.val_inv_eq_inv_val, IsUnit.unit_spec, inv_pow,
    div_eq_mul_inv]

lemma isUnit_dblU_of_Y_eq_of_Y_eq' {P Q : R × R × R} (hP : W'.Nonsingular P) (hPz : IsUnit <| P z)
    (hQz : IsUnit <| Q z) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W'.negY Q * P z ^ 3) : IsUnit <| W'.dblU P :=
  ((nonsingular_iff_of_Y_eq_negY hPz <| Y_eq_negY_of_Y_eq_of_Y_eq' hQz hx hy hy').mp hP).right

@[deprecated (since := "2025-05-26")] alias dblU_ne_zero_of_Y_eq := isUnit_dblU_of_Y_eq_of_Y_eq'
@[deprecated (since := "2025-05-26")] alias isUnit_dblU_of_Y_eq := isUnit_dblU_of_Y_eq_of_Y_eq'

variable (W') in
/-- The `Z`-coordinate of a representative of `2 • P` for a Jacobian point representative `P` on a
Weierstrass curve. -/
def dblZ (P : R × R × R) : R :=
  P z * (P y - W'.negY P)

lemma dblZ_smul (P : R × R × R) (u : R) : W'.dblZ (u • P) = u ^ 4 * W'.dblZ P := by
  simp_rw [dblZ, negY_smul, smul_eq]
  ring1

lemma dblZ_of_Z_eq_zero {P : R × R × R} (hPz : P z = 0) : W'.dblZ P = 0 := by
  rw [dblZ, hPz, zero_mul]

lemma dblZ_of_isUnit_Z {P : R × R × R} (hPz : IsUnit <| P z) : W'.dblZ P =
    (P y * hPz.unit⁻¹ ^ 3 - W'.toAffine.negY (P x * hPz.unit⁻¹ ^ 2) (P y * hPz.unit⁻¹ ^ 3))
      * P z ^ 4 := by
  rw [dblZ, mul_comm, pow_succ _ 3, ← mul_assoc, sub_mul <| _ * _, mul_assoc, ← mul_pow,
    hPz.val_inv_mul, one_pow, mul_one, ← negY_of_isUnit_Z hPz]

lemma dblZ_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) :
    W.dblZ P = (P y / P z ^ 3 - W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3)) * P z ^ 4 := by
  simp_rw [dblZ_of_isUnit_Z hPz.isUnit, Units.val_inv_eq_inv_val, IsUnit.unit_spec, inv_pow,
    div_eq_mul_inv]

lemma dblZ_of_Y_eq_of_Y_eq' {P Q : R × R × R} (hQz : IsUnit <| Q z)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W'.negY Q * P z ^ 3) : W'.dblZ P = 0 := by
  rw [dblZ, Y_eq_negY_of_Y_eq_of_Y_eq' hQz hx hy hy', sub_self, mul_zero]

@[deprecated (since := "2025-05-26")] alias dblZ_of_Y_eq := dblZ_of_Y_eq_of_Y_eq'

lemma isUnit_dblZ_of_Y_ne {P Q : R × R × R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : IsUnit <| P z) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : IsUnit <| P y * Q z ^ 3 - Q y * P z ^ 3) : IsUnit <| W'.dblZ P :=
  hPz.mul <| isUnit_Y_sub_negY_of_Y_ne hP hQ hx hy

@[deprecated (since := "2025-05-26")] alias dblZ_ne_zero_of_Y_ne := isUnit_dblZ_of_Y_ne

lemma isUnit_dblZ_of_Y_ne' {P Q : R × R × R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : IsUnit <| P z) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : IsUnit <| P y * Q z ^ 3 - W'.negY Q * P z ^ 3) : IsUnit <| W'.dblZ P :=
  hPz.mul <| isUnit_Y_sub_negY_of_Y_ne' hP hQ hx hy

@[deprecated (since := "2025-05-26")] alias dblZ_ne_zero_of_Y_ne' := isUnit_dblZ_of_Y_ne'

private lemma toAffine_slope_of_Y_ne' [Nontrivial R] {P Q : R × R × R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : IsUnit <| P z) (hQz : IsUnit <| Q z)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : IsUnit <| P y * Q z ^ 3 - W'.negY Q * P z ^ 3) :
    W'.toAffine.slope (P x * hPz.unit⁻¹ ^ 2) (Q x * hQz.unit⁻¹ ^ 2) (P y * hPz.unit⁻¹ ^ 3)
      (Q y * hQz.unit⁻¹ ^ 3) = -W'.dblU P * (isUnit_dblZ_of_Y_ne' hP hQ hPz hx hy).unit⁻¹ := by
  have hx' := (X_eq_iff_of_isUnit_Z hPz hQz).mp hx
  have hy' := (Y_ne'_iff_of_isUnit_Z hPz hQz).mp hy
  rw [← hx', ← (Y_eq_iff_of_isUnit_Z hPz hQz).mp <| Y_eq_of_Y_ne' hP hQ hx hy] at hy' ⊢
  rw [Affine.slope_of_Y_ne' rfl hy', Units.mul_inv_eq_mul_inv_iff, IsUnit.unit_spec,
    dblZ_of_isUnit_Z hPz, dblU_of_isUnit_Z hPz, ← neg_mul, neg_sub, mul_assoc _ <| _ ^ _,
    mul_comm <| _ ^ _, IsUnit.unit_spec]

#exit

variable (W') in
/-- The `X`-coordinate of a representative of `2 • P` for a Jacobian point representative `P` on a
Weierstrass curve. -/
noncomputable def dblX (P : R × R × R) : R :=
  W'.dblU P ^ 2 - W'.a₁ * W'.dblU P * P z * (P y - W'.negY P)
    - W'.a₂ * P z ^ 2 * (P y - W'.negY P) ^ 2 - 2 * P x * (P y - W'.negY P) ^ 2

lemma dblX_smul (P : R × R × R) (u : R) : W'.dblX (u • P) = (u ^ 4) ^ 2 * W'.dblX P := by
  simp_rw [dblX, dblU_smul, negY_smul, smul_eq]
  ring1

lemma dblX_of_Z_eq_zero {P : R × R × R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblX P = (P x ^ 2) ^ 2 := by
  linear_combination (norm := (rw [dblX, dblU_of_Z_eq_zero hPz, negY_of_Z_eq_zero hPz, hPz]; ring1))
    -8 * P x * (equation_of_Z_eq_zero hPz).mp hP

lemma dblX_of_Y_eq [NoZeroDivisors R] {P Q : R × R × R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W'.negY Q * P z ^ 3) : W'.dblX P = W'.dblU P ^ 2 := by
  rw [dblX, Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

private lemma toAffine_addX_of_eq {P : F × F × F} (hPz : P z ≠ 0) {n d : F} (hd : d ≠ 0) :
    W.toAffine.addX (P x / P z ^ 2) (P x / P z ^ 2) (-n / (P z * d)) =
      (n ^ 2 - W.a₁ * n * P z * d - W.a₂ * P z ^ 2 * d ^ 2 - 2 * P x * d ^ 2) / (P z * d) ^ 2 := by
  field_simp [mul_ne_zero hPz hd]
  ring1

lemma dblX_of_Z_ne_zero {P Q : F × F × F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.dblX P / W.dblZ P ^ 2 = W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [dblX, toAffine_slope_of_eq hP hQ hPz hQz hx hy, dblZ, ← (X_eq_iff hPz hQz).mp hx,
    toAffine_addX_of_eq hPz <| sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne' hP hQ hx hy]

variable (W') in
/-- The `Y`-coordinate of a representative of `-(2 • P)` for a Jacobian point representative `P` on
a Weierstrass curve. -/
noncomputable def negDblY (P : R × R × R) : R :=
  -W'.dblU P * (W'.dblX P - P x * (P y - W'.negY P) ^ 2) + P y * (P y - W'.negY P) ^ 3

lemma negDblY_smul (P : R × R × R) (u : R) : W'.negDblY (u • P) = (u ^ 4) ^ 3 * W'.negDblY P := by
  simp_rw [negDblY, dblU_smul, dblX_smul, negY_smul, smul_eq]
  ring1

lemma negDblY_of_Z_eq_zero {P : R × R × R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.negDblY P = -(P x ^ 2) ^ 3 := by
  linear_combination (norm :=
      (rw [negDblY, dblU_of_Z_eq_zero hPz, dblX_of_Z_eq_zero hP hPz, negY_of_Z_eq_zero hPz]; ring1))
    (8 * P y ^ 2 - 4 * P x ^ 3) * (equation_of_Z_eq_zero hPz).mp hP

lemma negDblY_of_Y_eq [NoZeroDivisors R] {P Q : R × R × R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W'.negY Q * P z ^ 3) : W'.negDblY P = (-W'.dblU P) ^ 3 := by
  rw [negDblY, dblX_of_Y_eq hQz hx hy hy', Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

private lemma toAffine_negAddY_of_eq {P : F × F × F} (hPz : P z ≠ 0) {n d : F} (hd : d ≠ 0) :
    W.toAffine.negAddY (P x / P z ^ 2) (P x / P z ^ 2) (P y / P z ^ 3) (-n / (P z * d)) =
      (-n * (n ^ 2 - W.a₁ * n * P z * d - W.a₂ * P z ^ 2 * d ^ 2 - 2 * P x * d ^ 2 - P x * d ^ 2)
        + P y * d ^ 3) / (P z * d) ^ 3 := by
  rw [Affine.negAddY, toAffine_addX_of_eq hPz hd]
  field_simp [mul_ne_zero (pow_ne_zero 2 <| mul_ne_zero hPz hd) <| pow_ne_zero 2 hPz]
  ring1

lemma negDblY_of_Z_ne_zero {P Q : F × F × F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z ≠ 0) (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) : W.negDblY P / W.dblZ P ^ 3 =
    W.toAffine.negAddY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [negDblY, dblX, toAffine_slope_of_eq hP hQ hPz hQz hx hy, dblZ, ← (X_eq_iff hPz hQz).mp hx,
    toAffine_negAddY_of_eq hPz <| sub_ne_zero.mpr <| Y_ne_negY_of_Y_ne' hP hQ hx hy]

variable (W') in
/-- The `Y`-coordinate of a representative of `2 • P` for a Jacobian point representative `P` on a
Weierstrass curve. -/
noncomputable def dblY (P : R × R × R) : R :=
  W'.negY (W'.dblX P, W'.negDblY P, W'.dblZ P)

lemma dblY_smul (P : R × R × R) (u : R) : W'.dblY (u • P) = (u ^ 4) ^ 3 * W'.dblY P := by
  simp_rw [dblY, negY, negDblY_smul, dblX_smul, dblZ_smul]
  ring1

lemma dblY_of_Z_eq_zero {P : R × R × R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblY P = (P x ^ 2) ^ 3 := by
  rw [dblY, negY, negDblY_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz]
  ring1

lemma dblY_of_Y_eq [NoZeroDivisors R] {P Q : R × R × R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W'.negY Q * P z ^ 3) : W'.dblY P = W'.dblU P ^ 3 := by
  rw [dblY, negY, negDblY_of_Y_eq hQz hx hy hy', dblZ_of_Y_eq hQz hx hy hy']
  ring1

lemma dblY_of_Z_ne_zero {P Q : F × F × F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.dblY P / W.dblZ P ^ 3 = W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [dblY, negY_of_Z_ne_zero <| dblZ_ne_zero_of_Y_ne' hP hQ hPz hx hy,
    dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, negDblY_of_Z_ne_zero hP hQ hPz hQz hx hy, Affine.addY]

variable (W') in
/-- The coordinates of a representative of `2 • P` for a Jacobian point representative `P` on a
Weierstrass curve. -/
noncomputable def dblXYZ (P : R × R × R) : R × R × R :=
  (W'.dblX P, W'.dblY P, W'.dblZ P)

@[deprecated (since := "2025-05-04")] alias dblXYZ_X := dblXYZ
@[deprecated (since := "2025-05-04")] alias dblXYZ_Y := dblXYZ
@[deprecated (since := "2025-05-04")] alias dblXYZ_Z := dblXYZ

lemma dblXYZ_smul (P : R × R × R) (u : R) : W'.dblXYZ (u • P) = u ^ 4 • W'.dblXYZ P := by
  simp_rw [dblXYZ, dblX_smul, dblY_smul, dblZ_smul, smul_eq]

lemma dblXYZ_of_Z_eq_zero {P : R × R × R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblXYZ P = P x ^ 2 • (1, 1, 0) := by
  rw [dblXYZ, dblX_of_Z_eq_zero hP hPz, dblY_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz, smul_eq,
    mul_one, mul_one, mul_zero]

lemma dblXYZ_of_Y_eq' [NoZeroDivisors R] {P Q : R × R × R} (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W'.negY Q * P z ^ 3) :
    W'.dblXYZ P = (W'.dblU P ^ 2, W'.dblU P ^ 3, 0) := by
  rw [dblXYZ, dblX_of_Y_eq hQz hx hy hy', dblY_of_Y_eq hQz hx hy hy', dblZ_of_Y_eq hQz hx hy hy']

lemma dblXYZ_of_Y_eq {P Q : F × F × F} (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy : P y * Q z ^ 3 = Q y * P z ^ 3) (hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3) :
    W.dblXYZ P = W.dblU P • (1, 1, 0) := by
  rw [dblXYZ_of_Y_eq' hQz hx hy hy', smul_eq, mul_one, mul_one, mul_zero]

lemma dblXYZ_of_Z_ne_zero {P Q : F × F × F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 ≠ W.negY Q * P z ^ 3) :
    W.dblXYZ P = W.dblZ P •
      (W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1) := by
  have hZ {n : ℕ} : IsUnit <| W.dblZ P ^ n := (isUnit_dblZ_of_Y_ne' hP hQ hPz hx hy).pow n
  rw [dblXYZ, ← dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, ← dblY_of_Z_ne_zero hP hQ hPz hQz hx hy,
    smul_eq, hZ.mul_div_cancel, hZ.mul_div_cancel, mul_one]

/-! ## Addition formulae in Jacobian coordinates -/

/-- The unit associated to a representative of `P + Q` for two Jacobian point representatives `P`
and `Q` on a Weierstrass curve `W` that are not `2`-torsion.

More specifically, the unit `u` such that `W.add P Q = u • (1, 1, 0)` where
`P x / P z ^ 2 = Q x / Q z ^ 2` but `P ≠ W.neg P`. -/
def addU (P Q : F × F × F) : F :=
  -((P y * Q z ^ 3 - Q y * P z ^ 3) / (P z * Q z))

lemma addU_smul {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) {u v : F} (hu : u ≠ 0)
    (hv : v ≠ 0) : addU (u • P) (v • Q) = (u * v) ^ 2 * addU P Q := by
  field_simp [addU, smul_eq]
  ring1

lemma addU_of_Z_eq_zero_left {P Q : F × F × F} (hPz : P z = 0) : addU P Q = 0 := by
  rw [addU, hPz, zero_mul, div_zero, neg_zero]

lemma addU_of_Z_eq_zero_right {P Q : F × F × F} (hQz : Q z = 0) : addU P Q = 0 := by
  rw [addU, hQz, mul_zero, div_zero, neg_zero]

lemma addU_ne_zero_of_Y_ne {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) : addU P Q ≠ 0 :=
  neg_ne_zero.mpr <| div_ne_zero (sub_ne_zero.mpr hy) <| mul_ne_zero hPz hQz

lemma isUnit_addU_of_Y_ne {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hy : P y * Q z ^ 3 ≠ Q y * P z ^ 3) : IsUnit (addU P Q) :=
  (addU_ne_zero_of_Y_ne hPz hQz hy).isUnit

/-- The `Z`-coordinate of a representative of `P + Q` for two distinct Jacobian point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def addZ (P Q : R × R × R) : R :=
  P x * Q z ^ 2 - Q x * P z ^ 2

lemma addZ_smul (P Q : R × R × R) (u v : R) : addZ (u • P) (v • Q) = (u * v) ^ 2 * addZ P Q := by
  simp_rw [addZ, smul_eq]
  ring1

lemma addZ_self (P : R × R × R) : addZ P P = 0 :=
  sub_self <| P x * P z ^ 2

lemma addZ_of_Z_eq_zero_left {P Q : R × R × R} (hPz : P z = 0) : addZ P Q = P x * Q z * Q z := by
  rw [addZ, hPz]
  ring1

lemma addZ_of_Z_eq_zero_right {P Q : R × R × R} (hQz : Q z = 0) :
    addZ P Q = -(Q x * P z) * P z := by
  rw [addZ, hQz]
  ring1

lemma addZ_of_X_eq {P Q : R × R × R} (hx : P x * Q z ^ 2 = Q x * P z ^ 2) : addZ P Q = 0 := by
  rw [addZ, hx, sub_self]

lemma addZ_ne_zero_of_X_ne {P Q : R × R × R} (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : addZ P Q ≠ 0 :=
  sub_ne_zero.mpr hx

lemma isUnit_addZ_of_X_ne {P Q : F × F × F} (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) :
    IsUnit <| addZ P Q :=
  (addZ_ne_zero_of_X_ne hx).isUnit

private lemma toAffine_slope_of_ne {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) :
    W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3) =
      (P y * Q z ^ 3 - Q y * P z ^ 3) / (P z * Q z * addZ P Q) := by
  rw [Affine.slope_of_X_ne <| by rwa [ne_eq, ← X_eq_iff hPz hQz],
    div_sub_div _ _ (pow_ne_zero 2 hPz) (pow_ne_zero 2 hQz), mul_comm <| _ ^ 2, addZ]
  field_simp [mul_ne_zero (mul_ne_zero hPz hQz) <| sub_ne_zero.mpr hx,
    mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hPz) (pow_ne_zero 3 hQz)) <| sub_ne_zero.mpr hx]
  ring1

variable (W') in
/-- The `X`-coordinate of a representative of `P + Q` for two distinct Jacobian point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def addX (P Q : R × R × R) : R :=
  P x * Q x ^ 2 * P z ^ 2 - 2 * P y * Q y * P z * Q z + P x ^ 2 * Q x * Q z ^ 2
    - W'.a₁ * P x * Q y * P z ^ 2 * Q z - W'.a₁ * P y * Q x * P z * Q z ^ 2
    + 2 * W'.a₂ * P x * Q x * P z ^ 2 * Q z ^ 2 - W'.a₃ * Q y * P z ^ 4 * Q z
    - W'.a₃ * P y * P z * Q z ^ 4 + W'.a₄ * Q x * P z ^ 4 * Q z ^ 2
    + W'.a₄ * P x * P z ^ 2 * Q z ^ 4 + 2 * W'.a₆ * P z ^ 4 * Q z ^ 4

lemma addX_eq' {P Q : R × R × R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * (P z * Q z) ^ 2 =
      (P y * Q z ^ 3 - Q y * P z ^ 3) ^ 2
        + W'.a₁ * (P y * Q z ^ 3 - Q y * P z ^ 3) * P z * Q z * addZ P Q
        - W'.a₂ * P z ^ 2 * Q z ^ 2 * addZ P Q ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2
        - Q x * P z ^ 2 * addZ P Q ^ 2 := by
  linear_combination (norm := (rw [addX, addZ]; ring1)) -Q z ^ 6 * (equation_iff P).mp hP
    - P z ^ 6 * (equation_iff Q).mp hQ

lemma addX_eq {P Q : F × F × F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) : W.addX P Q =
      ((P y * Q z ^ 3 - Q y * P z ^ 3) ^ 2
        + W.a₁ * (P y * Q z ^ 3 - Q y * P z ^ 3) * P z * Q z * addZ P Q
        - W.a₂ * P z ^ 2 * Q z ^ 2 * addZ P Q ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2
        - Q x * P z ^ 2 * addZ P Q ^ 2) / (P z * Q z) ^ 2 := by
  rw [← addX_eq' hP hQ, mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

lemma addX_smul (P Q : R × R × R) (u v : R) :
    W'.addX (u • P) (v • Q) = ((u * v) ^ 2) ^ 2 * W'.addX P Q := by
  simp_rw [addX, smul_eq]
  ring1

lemma addX_self {P : R × R × R} (hP : W'.Equation P) : W'.addX P P = 0 := by
  linear_combination (norm := (rw [addX]; ring1)) -2 * P z ^ 2 * (equation_iff _).mp hP

lemma addX_of_Z_eq_zero_left {P Q : R × R × R} (hPz : P z = 0) :
    W'.addX P Q = (P x * Q z) ^ 2 * Q x := by
  rw [addX, hPz]
  ring1

lemma addX_of_Z_eq_zero_right {P Q : R × R × R} (hQz : Q z = 0) :
    W'.addX P Q = (-(Q x * P z)) ^ 2 * P x := by
  rw [addX, hQz]
  ring1

lemma addX_of_X_eq' {P Q : R × R × R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W'.addX P Q * (P z * Q z) ^ 2 = (P y * Q z ^ 3 - Q y * P z ^ 3) ^ 2 := by
  rw [addX_eq' hP hQ, addZ_of_X_eq hx]
  ring1

lemma addX_of_X_eq {P Q : F × F × F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) : W.addX P Q = addU P Q ^ 2 := by
  rw [addU, neg_sq, div_pow, ← addX_of_X_eq' hP hQ hx,
    mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

private lemma toAffine_addX_of_ne {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) {n d : F}
    (hd : d ≠ 0) : W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2) (n / (P z * Q z * d)) =
      (n ^ 2 + W.a₁ * n * P z * Q z * d - W.a₂ * P z ^ 2 * Q z ^ 2 * d ^ 2 - P x * Q z ^ 2 * d ^ 2
        - Q x * P z ^ 2 * d ^ 2) / (P z * Q z) ^ 2 / d ^ 2 := by
  field_simp [mul_ne_zero (mul_ne_zero hPz hQz) hd]
  ring1

lemma addX_of_Z_ne_zero {P Q : F × F × F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : W.addX P Q / addZ P Q ^ 2 =
      W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
        (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [addX_eq hP hQ hPz hQz, toAffine_slope_of_ne hPz hQz hx,
    toAffine_addX_of_ne hPz hQz <| addZ_ne_zero_of_X_ne hx]

variable (W') in
/-- The `Y`-coordinate of a representative of `-(P + Q)` for two distinct Jacobian point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def negAddY (P Q : R × R × R) : R :=
  -P y * Q x ^ 3 * P z ^ 3 + 2 * P y * Q y ^ 2 * P z ^ 3 - 3 * P x ^ 2 * Q x * Q y * P z ^ 2 * Q z
    + 3 * P x * P y * Q x ^ 2 * P z * Q z ^ 2 + P x ^ 3 * Q y * Q z ^ 3
    - 2 * P y ^ 2 * Q y * Q z ^ 3 + W'.a₁ * P x * Q y ^ 2 * P z ^ 4
    + W'.a₁ * P y * Q x * Q y * P z ^ 3 * Q z - W'.a₁ * P x * P y * Q y * P z * Q z ^ 3
    - W'.a₁ * P y ^ 2 * Q x * Q z ^ 4 - 2 * W'.a₂ * P x * Q x * Q y * P z ^ 4 * Q z
    + 2 * W'.a₂ * P x * P y * Q x * P z * Q z ^ 4 + W'.a₃ * Q y ^ 2 * P z ^ 6
    - W'.a₃ * P y ^ 2 * Q z ^ 6 - W'.a₄ * Q x * Q y * P z ^ 6 * Q z
    - W'.a₄ * P x * Q y * P z ^ 4 * Q z ^ 3 + W'.a₄ * P y * Q x * P z ^ 3 * Q z ^ 4
    + W'.a₄ * P x * P y * P z * Q z ^ 6 - 2 * W'.a₆ * Q y * P z ^ 6 * Q z ^ 3
    + 2 * W'.a₆ * P y * P z ^ 3 * Q z ^ 6

lemma negAddY_eq' (P Q : R × R × R) : W'.negAddY P Q * (P z * Q z) ^ 3 =
    (P y * Q z ^ 3 - Q y * P z ^ 3) * (W'.addX P Q * (P z * Q z) ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2)
      + P y * Q z ^ 3 * addZ P Q ^ 3 := by
  rw [negAddY, addX, addZ]
  ring1

lemma negAddY_eq {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) : W.negAddY P Q =
    ((P y * Q z ^ 3 - Q y * P z ^ 3) * (W.addX P Q * (P z * Q z) ^ 2 - P x * Q z ^ 2 * addZ P Q ^ 2)
      + P y * Q z ^ 3 * addZ P Q ^ 3) / (P z * Q z) ^ 3 := by
  rw [← negAddY_eq', mul_div_cancel_right₀ _ <| pow_ne_zero 3 <| mul_ne_zero hPz hQz]

lemma negAddY_smul (P Q : R × R × R) (u v : R) :
    W'.negAddY (u • P) (v • Q) = ((u * v) ^ 2) ^ 3 * W'.negAddY P Q := by
  simp_rw [negAddY, smul_eq]
  ring1

lemma negAddY_self (P : R × R × R) : W'.negAddY P P = 0 := by
  rw [negAddY]
  ring1

lemma negAddY_of_Z_eq_zero_left {P Q : R × R × R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.negAddY P Q = (P x * Q z) ^ 3 * W'.negY Q := by
  linear_combination (norm := (rw [negAddY, negY, hPz]; ring1))
    (W'.negY Q - Q y) * Q z ^ 3 * (equation_of_Z_eq_zero hPz).mp hP

lemma negAddY_of_Z_eq_zero_right {P Q : R × R × R} (hQ : W'.Equation Q) (hQz : Q z = 0) :
    W'.negAddY P Q = (-(Q x * P z)) ^ 3 * W'.negY P := by
  linear_combination (norm := (rw [negAddY, negY, hQz]; ring1))
    (P y - W'.negY P) * P z ^ 3 * (equation_of_Z_eq_zero hQz).mp hQ

lemma negAddY_of_X_eq' {P Q : R × R × R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W'.negAddY P Q * (P z * Q z) ^ 3 = (P y * Q z ^ 3 - Q y * P z ^ 3) ^ 3 := by
  rw [negAddY_eq', addX_eq' hP hQ, addZ_of_X_eq hx]
  ring1

lemma negAddY_of_X_eq {P Q : F × F × F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) : W.negAddY P Q = (-addU P Q) ^ 3 := by
  rw [addU, neg_neg, div_pow, ← negAddY_of_X_eq' hP hQ hx,
    mul_div_cancel_right₀ _ <| pow_ne_zero 3 <| mul_ne_zero hPz hQz]

private lemma toAffine_negAddY_of_ne {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) {n d : F}
    (hd : d ≠ 0) :
    W.toAffine.negAddY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (n / (P z * Q z * d)) =
      (n * (n ^ 2 + W.a₁ * n * P z * Q z * d - W.a₂ * P z ^ 2 * Q z ^ 2 * d ^ 2
        - P x * Q z ^ 2 * d ^ 2 - Q x * P z ^ 2 * d ^ 2 - P x * Q z ^ 2 * d ^ 2)
        + P y * Q z ^ 3 * d ^ 3) / (P z * Q z) ^ 3 / d ^ 3 := by
  rw [Affine.negAddY, toAffine_addX_of_ne hPz hQz hd]
  field_simp [mul_ne_zero (mul_ne_zero hPz hQz) hd, mul_ne_zero
      (mul_ne_zero (pow_ne_zero 2 <| mul_ne_zero hPz hQz) <| pow_ne_zero 2 hd) <| pow_ne_zero 2 hPz]
  ring1

lemma negAddY_of_Z_ne_zero {P Q : F × F × F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : W.negAddY P Q / addZ P Q ^ 3 =
      W.toAffine.negAddY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
        (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [negAddY_eq hPz hQz, addX_eq' hP hQ, toAffine_slope_of_ne hPz hQz hx,
    toAffine_negAddY_of_ne hPz hQz <| addZ_ne_zero_of_X_ne hx]

variable (W') in
/-- The `Y`-coordinate of a representative of `P + Q` for two distinct Jacobian point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `0`. -/
def addY (P Q : R × R × R) : R :=
  W'.negY (W'.addX P Q, W'.negAddY P Q, addZ P Q)

lemma addY_smul (P Q : R × R × R) (u v : R) :
    W'.addY (u • P) (v • Q) = ((u * v) ^ 2) ^ 3 * W'.addY P Q := by
  simp_rw [addY, negY, negAddY_smul, addX_smul, addZ_smul]
  ring1

lemma addY_self {P : R × R × R} (hP : W'.Equation P) : W'.addY P P = 0 := by
  rw [addY, negY, addX_self hP, negAddY_self, addZ_self]
  ring1

lemma addY_of_Z_eq_zero_left {P Q : R × R × R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.addY P Q = (P x * Q z) ^ 3 * Q y := by
  rw [addY, negY, negAddY_of_Z_eq_zero_left hP hPz, negY, addX_of_Z_eq_zero_left hPz,
    addZ_of_Z_eq_zero_left hPz]
  ring1

lemma addY_of_Z_eq_zero_right {P Q : R × R × R} (hQ : W'.Equation Q) (hQz : Q z = 0) :
    W'.addY P Q = (-(Q x * P z)) ^ 3 * P y := by
  rw [addY, negY, negAddY_of_Z_eq_zero_right hQ hQz, negY, addX_of_Z_eq_zero_right hQz,
    addZ_of_Z_eq_zero_right hQz]
  ring1

lemma addY_of_X_eq' {P Q : R × R × R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W'.addY P Q * (P z * Q z) ^ 3 = (-(P y * Q z ^ 3 - Q y * P z ^ 3)) ^ 3 := by
  linear_combination (norm := (rw [addY, negY, addZ_of_X_eq hx]; ring1))
    -negAddY_of_X_eq' hP hQ hx

lemma addY_of_X_eq {P Q : F × F × F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) : W.addY P Q = addU P Q ^ 3 := by
  rw [addU, ← neg_div, div_pow, ← addY_of_X_eq' hP hQ hx,
    mul_div_cancel_right₀ _ <| pow_ne_zero 3 <| mul_ne_zero hPz hQz]

lemma addY_of_Z_ne_zero {P Q : F × F × F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) :
    W.addY P Q / addZ P Q ^ 3 = W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
      (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)) := by
  rw [addY, negY_of_Z_ne_zero <| addZ_ne_zero_of_X_ne hx, addX_of_Z_ne_zero hP hQ hPz hQz hx,
    negAddY_of_Z_ne_zero hP hQ hPz hQz hx, Affine.addY]

variable (W') in
/-- The coordinates of a representative of `P + Q` for two distinct Jacobian point
representatives `P` and `Q` on a Weierstrass curve.

If the representatives of `P` and `Q` are equal, then this returns the value `(0, 0, 0)`. -/
noncomputable def addXYZ (P Q : R × R × R) : R × R × R :=
  (W'.addX P Q, W'.addY P Q, addZ P Q)

@[deprecated (since := "2025-05-04")] alias addXYZ_X := addXYZ
@[deprecated (since := "2025-05-04")] alias addXYZ_Y := addXYZ
@[deprecated (since := "2025-05-04")] alias addXYZ_Z := addXYZ

lemma addXYZ_smul (P Q : R × R × R) (u v : R) :
    W'.addXYZ (u • P) (v • Q) = (u * v) ^ 2 • W'.addXYZ P Q := by
  simp_rw [addXYZ, addX_smul, addY_smul, addZ_smul, smul_eq]

lemma addXYZ_self {P : R × R × R} (hP : W'.Equation P) : W'.addXYZ P P = (0, 0, 0) := by
  rw [addXYZ, addX_self hP, addY_self hP, addZ_self]

lemma addXYZ_of_Z_eq_zero_left {P Q : R × R × R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.addXYZ P Q = (P x * Q z) • Q := by
  rw [addXYZ, addX_of_Z_eq_zero_left hPz, addY_of_Z_eq_zero_left hP hPz, addZ_of_Z_eq_zero_left hPz,
    smul_eq]

lemma addXYZ_of_Z_eq_zero_right {P Q : R × R × R} (hQ : W'.Equation Q) (hQz : Q z = 0) :
    W'.addXYZ P Q = -(Q x * P z) • P := by
  rw [addXYZ, addX_of_Z_eq_zero_right hQz, addY_of_Z_eq_zero_right hQ hQz,
    addZ_of_Z_eq_zero_right hQz, smul_eq]

lemma addXYZ_of_X_eq {P Q : F × F × F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) :
    W.addXYZ P Q = addU P Q • (1, 1, 0) := by
  rw [addXYZ, addX_of_X_eq hP hQ hPz hQz hx, addY_of_X_eq hP hQ hPz hQz hx, addZ_of_X_eq hx,
    smul_eq, mul_one, mul_one, mul_zero]

lemma addXYZ_of_Z_ne_zero {P Q : F × F × F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z ≠ 0)
    (hQz : Q z ≠ 0) (hx : P x * Q z ^ 2 ≠ Q x * P z ^ 2) : W.addXYZ P Q = addZ P Q •
      (W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1) := by
  have hZ {n : ℕ} : IsUnit <| addZ P Q ^ n := (isUnit_addZ_of_X_ne hx).pow n
  rw [addXYZ, ← addX_of_Z_ne_zero hP hQ hPz hQz hx, ← addY_of_Z_ne_zero hP hQ hPz hQz hx, smul_eq,
    hZ.mul_div_cancel, hZ.mul_div_cancel, mul_one]

/-! ## Maps and base changes -/

variable (f : R →+* S) (P Q : R × R × R)

@[simp]
lemma map_negY : (W'.map f).toJacobian.negY (f ∘ P) = f (W'.negY P) := by
  simp_rw [negY]
  map_simp

@[simp]
lemma map_dblU : (W'.map f).toJacobian.dblU (f ∘ P) = f (W'.dblU P) := by
  simp_rw [dblU_eq]
  map_simp

@[simp]
lemma map_dblZ : (W'.map f).toJacobian.dblZ (f ∘ P) = f (W'.dblZ P) := by
  simp_rw [dblZ, negY]
  map_simp

@[simp]
lemma map_dblX : (W'.map f).toJacobian.dblX (f ∘ P) = f (W'.dblX P) := by
  simp_rw [dblX, map_dblU, map_negY]
  map_simp

@[simp]
lemma map_negDblY : (W'.map f).toJacobian.negDblY (f ∘ P) = f (W'.negDblY P) := by
  simp_rw [negDblY, map_dblU, map_dblX, map_negY]
  map_simp

@[simp]
lemma map_dblY : (W'.map f).toJacobian.dblY (f ∘ P) = f (W'.dblY P) := by
  simp_rw [dblY, negY, map_negDblY, map_dblX, map_dblZ]
  map_simp

@[simp]
lemma map_dblXYZ : (W'.map f).toJacobian.dblXYZ (f ∘ P) = f ∘ W'.dblXYZ P := by
  simp_rw [dblXYZ, map_dblX, map_dblY, map_dblZ, map_eq]

@[simp]
lemma map_addU (f : F →+* K) (P Q : F × F × F) : addU (f ∘ P) (f ∘ Q) = f (addU P Q) := by
  simp_rw [addU]
  map_simp

@[simp]
lemma map_addZ : addZ (f ∘ P) (f ∘ Q) = f (addZ P Q) := by
  simp_rw [addZ]
  map_simp

@[simp]
lemma map_addX : (W'.map f).toJacobian.addX (f ∘ P) (f ∘ Q) = f (W'.addX P Q) := by
  simp_rw [addX]
  map_simp

@[simp]
lemma map_negAddY : (W'.map f).toJacobian.negAddY (f ∘ P) (f ∘ Q) = f (W'.negAddY P Q) := by
  simp_rw [negAddY]
  map_simp

@[simp]
lemma map_addY : (W'.map f).toJacobian.addY (f ∘ P) (f ∘ Q) = f (W'.addY P Q) := by
  simp_rw [addY, negY, map_negAddY, map_addX, map_addZ]
  map_simp

@[simp]
lemma map_addXYZ : (W'.map f).toJacobian.addXYZ (f ∘ P) (f ∘ Q) = f ∘ W'.addXYZ P Q := by
  simp_rw [addXYZ, map_addX, map_addY, map_addZ, map_eq]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A →ₐ[S] B) (P Q : A × A × A)

lemma baseChange_negY :
    (W'.baseChange B).toJacobian.negY (f ∘ P) = f ((W'.baseChange A).toJacobian.negY P) := by
  rw [← RingHom.coe_coe, ← map_negY, map_baseChange]

lemma baseChange_dblU :
    (W'.baseChange B).toJacobian.dblU (f ∘ P) = f ((W'.baseChange A).toJacobian.dblU P) := by
  rw [← RingHom.coe_coe, ← map_dblU, map_baseChange]

lemma baseChange_dblZ :
    (W'.baseChange B).toJacobian.dblZ (f ∘ P) = f ((W'.baseChange A).toJacobian.dblZ P) := by
  rw [← RingHom.coe_coe, ← map_dblZ, map_baseChange]

lemma baseChange_dblX :
    (W'.baseChange B).toJacobian.dblX (f ∘ P) = f ((W'.baseChange A).toJacobian.dblX P) := by
  rw [← RingHom.coe_coe, ← map_dblX, map_baseChange]

lemma baseChange_negDblY :
    (W'.baseChange B).toJacobian.negDblY (f ∘ P) = f ((W'.baseChange A).toJacobian.negDblY P) := by
  rw [← RingHom.coe_coe, ← map_negDblY, map_baseChange]

lemma baseChange_dblY :
    (W'.baseChange B).toJacobian.dblY (f ∘ P) = f ((W'.baseChange A).toJacobian.dblY P) := by
  rw [← RingHom.coe_coe, ← map_dblY, map_baseChange]

lemma baseChange_dblXYZ :
    (W'.baseChange B).toJacobian.dblXYZ (f ∘ P) = f ∘ (W'.baseChange A).toJacobian.dblXYZ P := by
  rw [← RingHom.coe_coe, ← map_dblXYZ, map_baseChange]

lemma baseChange_addX : (W'.baseChange B).toJacobian.addX (f ∘ P) (f ∘ Q) =
    f ((W'.baseChange A).toJacobian.addX P Q) := by
  rw [← RingHom.coe_coe, ← map_addX, map_baseChange]

lemma baseChange_negAddY : (W'.baseChange B).toJacobian.negAddY (f ∘ P) (f ∘ Q) =
    f ((W'.baseChange A).toJacobian.negAddY P Q) := by
  rw [← RingHom.coe_coe, ← map_negAddY, map_baseChange]

lemma baseChange_addY : (W'.baseChange B).toJacobian.addY (f ∘ P) (f ∘ Q) =
    f ((W'.baseChange A).toJacobian.addY P Q) := by
  rw [← RingHom.coe_coe, ← map_addY, map_baseChange]

lemma baseChange_addXYZ : (W'.baseChange B).toJacobian.addXYZ (f ∘ P) (f ∘ Q) =
    f ∘ (W'.baseChange A).toJacobian.addXYZ P Q := by
  rw [← RingHom.coe_coe, ← map_addXYZ, map_baseChange]

end Jacobian

end WeierstrassCurve
