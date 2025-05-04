/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# Weierstrass equations and the nonsingular condition in projective coordinates

A point on the unweighted projective plane over a commutative ring `R` is an equivalence class
`[x : y : z]` of triples `(x, y, z) ≠ (0, 0, 0)` of elements in `R` such that
`(x, y, z) ∼ (x', y', z')` if there is some unit `u` in `Rˣ` with `(x, y, z) = (ux', uy', uz')`.

Let `W` be a Weierstrass curve over a commutative ring `R` with coefficients `aᵢ`. A
*projective point* is a point on the unweighted projective plane over `R` satisfying the
*homogeneous Weierstrass equation* `W(X, Y, Z) = 0` in *projective coordinates*, where
`W(X, Y, Z) := Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)`. It is *nonsingular* if its
partial derivatives `W_X(x, y, z)`, `W_Y(x, y, z)`, and `W_Z(x, y, z)` do not vanish simultaneously.

This file gives an explicit implementation of equivalence classes of triples up to scaling by units,
and defines polynomials associated to Weierstrass equations and the nonsingular condition in
projective coordinates. The group law on the actual type of nonsingular projective points will be
defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean`, based on the formulae
for group operations in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean`.

## Main definitions

 * `WeierstrassCurve.Projective.PointClass`: the equivalence class of a point representative.
 * `WeierstrassCurve.Projective.Nonsingular`: the nonsingular condition on a point representative.
 * `WeierstrassCurve.Projective.NonsingularLift`: the nonsingular condition on a point class.

## Main statements

 * `WeierstrassCurve.Projective.polynomial_relation`: Euler's homogeneous function theorem.

## Implementation notes

All definitions and lemmas for Weierstrass curves in projective coordinates live in the namespace
`WeierstrassCurve.Projective` to distinguish them from those in other coordinates. This is simply an
abbreviation for `WeierstrassCurve` that can be converted using `WeierstrassCurve.toProjective`.
This can be converted into `WeierstrassCurve.Affine` using `WeierstrassCurve.Projective.toAffine`.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Basic.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, projective, Weierstrass equation, nonsingular
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
    pderiv_C, pderiv_X_self, pderiv_X_of_ne one_ne_zero, pderiv_X_of_ne one_ne_zero.symm,
    pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0), pderiv_X_of_ne (by decide : 0 ≠ (2 : Fin 3)),
    pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 1), pderiv_X_of_ne (by decide : 1 ≠ (2 : Fin 3))])

universe r s u v

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v}

namespace WeierstrassCurve

/-! ## Projective coordinates -/

variable (R) in
/-- An abbreviation for a Weierstrass curve in projective coordinates. -/
abbrev Projective : Type r :=
  WeierstrassCurve R

/-- The conversion from a Weierstrass curve to projective coordinates. -/
abbrev toProjective (W : WeierstrassCurve R) : Projective R :=
  W

namespace Projective

/-- The conversion from a Weierstrass curve in projective coordinates to affine coordinates. -/
abbrev toAffine (W' : Projective R) : Affine R :=
  W'

lemma map_eq (f : R → S) (P : R × R × R) : f ∘ P = (f (P x), f (P y), f (P z)) := by
  rfl

lemma map_fin3 (f : R → S) (P : R × R × R) :
    f ∘ ![P x, P y, P z] = ![f (P x), f (P y), f (P z)] := by
  ext n; fin_cases n <;> simp

variable [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Field F] [Field K] {W' : Projective R}
  {W : Projective F}

lemma smul_eq (P : R × R × R) (u : R) : u • P = (u * P x, u * P y, u * P z) :=
  rfl

protected lemma map_smul (f : R →* S) (P : R × R × R) (u : R) : f ∘ u • P = f u • f ∘ P := by
  simp_rw [map_eq, smul_eq, map_mul]

/-- The equivalence setoid for a projective point representative on a Weierstrass curve. -/
@[reducible]
scoped instance : Setoid <| R × R × R :=
  MulAction.orbitRel Rˣ <| R × R × R

variable (R) in
/-- The equivalence class of a projective point representative on a Weierstrass curve. -/
abbrev PointClass : Type r :=
  MulAction.orbitRel.Quotient Rˣ <| R × R × R

lemma smul_equiv (P : R × R × R) {u : R} (hu : IsUnit u) : u • P ≈ P :=
  ⟨hu.unit, rfl⟩

lemma mk_smul (P : R × R × R) {u : R} (hu : IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧ :=
  Quotient.eq.mpr <| smul_equiv P hu

lemma smul_equiv_smul (P Q : R × R × R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    u • P ≈ v • Q ↔ P ≈ Q := by
  rw [← Quotient.eq_iff_equiv, ← Quotient.eq_iff_equiv, mk_smul P hu, mk_smul Q hv]

lemma equiv_iff_eq_of_Z_eq' {P Q : R × R × R} (hz : P z = Q z) (hQz : Q z ∈ nonZeroDivisors R) :
    P ≈ Q ↔ P = Q := by
  refine ⟨?_, Quotient.exact.comp <| congrArg _⟩
  rintro ⟨u, rfl⟩
  simp_rw [Units.smul_def, (mul_cancel_right_mem_nonZeroDivisors hQz).mp <| one_mul (Q z) ▸ hz,
    one_smul]

lemma equiv_iff_eq_of_Z_eq [NoZeroDivisors R] {P Q : R × R × R} (hz : P z = Q z) (hQz : Q z ≠ 0) :
    P ≈ Q ↔ P = Q :=
  equiv_iff_eq_of_Z_eq' hz <| mem_nonZeroDivisors_of_ne_zero hQz

lemma Z_eq_zero_of_equiv {P Q : R × R × R} (h : P ≈ Q) : P z = 0 ↔ Q z = 0 := by
  rcases h with ⟨u, rfl⟩
  exact u.mul_right_eq_zero

lemma X_eq_of_equiv {P Q : R × R × R} (h : P ≈ Q) : P x * Q z = Q x * P z := by
  rcases h with ⟨u, rfl⟩
  simp_rw [Units.smul_def, smul_eq]
  ring1

lemma Y_eq_of_equiv {P Q : R × R × R} (h : P ≈ Q) : P y * Q z = Q y * P z := by
  rcases h with ⟨u, rfl⟩
  simp_rw [Units.smul_def, smul_eq]
  ring1

lemma not_equiv_of_Z_eq_zero_left {P Q : R × R × R} (hPz : P z = 0) (hQz : Q z ≠ 0) : ¬P ≈ Q :=
  fun h => hQz <| (Z_eq_zero_of_equiv h).mp hPz

lemma not_equiv_of_Z_eq_zero_right {P Q : R × R × R} (hPz : P z ≠ 0) (hQz : Q z = 0) : ¬P ≈ Q :=
  fun h => hPz <| (Z_eq_zero_of_equiv h).mpr hQz

lemma not_equiv_of_X_ne {P Q : R × R × R} (hx : P x * Q z ≠ Q x * P z) : ¬P ≈ Q :=
  hx.comp X_eq_of_equiv

lemma not_equiv_of_Y_ne {P Q : R × R × R} (hy : P y * Q z ≠ Q y * P z) : ¬P ≈ Q :=
  hy.comp Y_eq_of_equiv

lemma equiv_of_X_eq_of_Y_eq {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) : P ≈ Q := by
  use Units.mk0 _ hPz / Units.mk0 _ hQz
  simp_rw [Units.smul_def, Units.val_div_eq_div_val, Units.val_mk0, smul_eq, mul_comm, mul_div,
    ← hx, ← hy, mul_div_cancel_right₀ _ hQz, mul_div_cancel_left₀ _ hQz]

lemma equiv_some_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) : P ≈ (P x / P z, P y / P z, 1) :=
  equiv_of_X_eq_of_Y_eq hPz one_ne_zero (by linear_combination (norm := ring1) -P x * div_self hPz)
    (by linear_combination (norm := ring1) -P y * div_self hPz)

lemma X_eq_iff {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P x * Q z = Q x * P z ↔ P x / P z = Q x / Q z :=
  (div_eq_div_iff hPz hQz).symm

lemma Y_eq_iff {P Q : F × F × F} (hPz : P z ≠ 0) (hQz : Q z ≠ 0) :
    P y * Q z = Q y * P z ↔ P y / P z = Q y / Q z :=
  (div_eq_div_iff hPz hQz).symm

/-! ## Weierstrass equations in projective coordinates -/

variable (W') in
/-- The polynomial `W(X, Y, Z) := Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)` associated to a
Weierstrass curve `W` over a ring `R` in projective coordinates.

This is represented as a term of type `MvPolynomial (Fin 3) R`, where `X 0`, `X 1`, and `X 2`
represent `X`, `Y`, and `Z` respectively. -/
noncomputable def polynomial : MvPolynomial (Fin 3) R :=
  X 1 ^ 2 * X 2 + C W'.a₁ * X 0 * X 1 * X 2 + C W'.a₃ * X 1 * X 2 ^ 2
    - (X 0 ^ 3 + C W'.a₂ * X 0 ^ 2 * X 2 + C W'.a₄ * X 0 * X 2 ^ 2 + C W'.a₆ * X 2 ^ 3)

lemma eval_polynomial (P : R × R × R) : eval ![P x, P y, P z] W'.polynomial =
    P y ^ 2 * P z + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 2
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z + W'.a₄ * P x * P z ^ 2 + W'.a₆ * P z ^ 3) := by
  rw [polynomial]
  eval_simp
  rfl

lemma eval_polynomial_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) :
    eval ![P x, P y, P z] W.polynomial / P z ^ 3 =
      W.toAffine.polynomial.evalEval (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [eval_polynomial, Affine.evalEval_polynomial]; ring1))
    P y ^ 2 / P z ^ 2 * div_self hPz + W.a₁ * P x * P y / P z ^ 2 * div_self hPz
      + W.a₃ * P y / P z * div_self (pow_ne_zero 2 hPz) - W.a₂ * P x ^ 2 / P z ^ 2 * div_self hPz
      - W.a₄ * P x / P z * div_self (pow_ne_zero 2 hPz) - W.a₆ * div_self (pow_ne_zero 3 hPz)

variable (W') in
/-- The proposition that a projective point representative `(x, y, z)` lies in a Weierstrass curve
`W`.

In other words, it satisfies the homogeneous Weierstrass equation `W(X, Y, Z) = 0`. -/
def Equation (P : R × R × R) : Prop :=
  eval ![P x, P y, P z] W'.polynomial = 0

lemma equation_iff (P : R × R × R) : W'.Equation P ↔
    P y ^ 2 * P z + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 2
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z + W'.a₄ * P x * P z ^ 2 + W'.a₆ * P z ^ 3) = 0 := by
  rw [Equation, eval_polynomial]

lemma equation_smul (P : R × R × R) {u : R} (hu : IsUnit u) : W'.Equation (u • P) ↔ W'.Equation P :=
  have hP (u : R) {P : R × R × R} (hP : W'.Equation P) : W'.Equation <| u • P := by
    rw [equation_iff] at hP ⊢
    linear_combination (norm := (rw [smul_eq]; ring1)) u ^ 3 * hP
  ⟨fun h => by convert hP ↑hu.unit⁻¹ h; rw [smul_smul, hu.val_inv_mul, one_smul], hP u⟩

lemma equation_of_equiv {P Q : R × R × R} (h : P ≈ Q) : W'.Equation P ↔ W'.Equation Q := by
  rcases h with ⟨u, rfl⟩
  exact equation_smul Q u.isUnit

lemma equation_of_Z_eq_zero {P : R × R × R} (hPz : P z = 0) : W'.Equation P ↔ P x ^ 3 = 0 := by
  simp_rw [equation_iff, hPz, sub_eq_zero, zero_pow <| OfNat.ofNat_ne_zero _, mul_zero, add_zero,
    eq_comm]

lemma equation_zero : W'.Equation (0, 1, 0) := by
  simp_rw [equation_of_Z_eq_zero, zero_pow three_ne_zero]

lemma equation_some (X Y : R) : W'.Equation (X, Y, 1) ↔ W'.toAffine.Equation X Y := by
  simp_rw [equation_iff, Affine.equation_iff', one_pow, mul_one]

lemma equation_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) :
    W.Equation P ↔ W.toAffine.Equation (P x / P z) (P y / P z) :=
  (equation_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| equation_some ..

lemma X_eq_zero_of_Z_eq_zero [NoZeroDivisors R] {P : R × R × R} (hP : W'.Equation P)
    (hPz : P z = 0) : P x = 0 :=
  pow_eq_zero <| (equation_of_Z_eq_zero hPz).mp hP

/-! ## The nonsingular condition in projective coordinates -/

variable (W') in
/-- The partial derivative `W_X(X, Y, Z)` with respect to `X` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in projective coordinates. -/
noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  pderiv 0 W'.polynomial

lemma polynomialX_eq : W'.polynomialX =
    C W'.a₁ * X 1 * X 2 - (C 3 * X 0 ^ 2 + C (2 * W'.a₂) * X 0 * X 2 + C W'.a₄ * X 2 ^ 2) := by
  rw [polynomialX, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialX (P : R × R × R) : eval ![P x, P y, P z] W'.polynomialX =
    W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z + W'.a₄ * P z ^ 2) := by
  rw [polynomialX_eq]
  eval_simp
  rfl

lemma eval_polynomialX_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) :
    eval ![P x, P y, P z] W.polynomialX / P z ^ 2 =
      W.toAffine.polynomialX.evalEval (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [eval_polynomialX, Affine.evalEval_polynomialX]; ring1))
    W.a₁ * P y / P z * div_self hPz - 2 * W.a₂ * P x / P z * div_self hPz
      - W.a₄ * div_self (pow_ne_zero 2 hPz)

variable (W') in
/-- The partial derivative `W_Y(X, Y, Z)` with respect to `Y` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in projective coordinates. -/
noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  pderiv 1 W'.polynomial

lemma polynomialY_eq : W'.polynomialY =
    C 2 * X 1 * X 2 + C W'.a₁ * X 0 * X 2 + C W'.a₃ * X 2 ^ 2 := by
  rw [polynomialY, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialY (P : R × R × R) :
    eval ![P x, P y, P z] W'.polynomialY = 2 * P y * P z + W'.a₁ * P x * P z + W'.a₃ * P z ^ 2 := by
  rw [polynomialY_eq]
  eval_simp
  rfl

lemma eval_polynomialY_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) :
    eval ![P x, P y, P z] W.polynomialY / P z ^ 2 =
      W.toAffine.polynomialY.evalEval (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [eval_polynomialY, Affine.evalEval_polynomialY]; ring1))
    2 * P y / P z * div_self hPz + W.a₁ * P x / P z * div_self hPz
      + W.a₃ * div_self (pow_ne_zero 2 hPz)

variable (W') in
/-- The partial derivative `W_Z(X, Y, Z)` with respect to `Z` of the polynomial `W(X, Y, Z)`
associated to a Weierstrass curve `W` in projective coordinates. -/
noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  pderiv 2 W'.polynomial

lemma polynomialZ_eq : W'.polynomialZ = X 1 ^ 2 + C W'.a₁ * X 0 * X 1 + C (2 * W'.a₃) * X 1 * X 2 -
    (C W'.a₂ * X 0 ^ 2 + C (2 * W'.a₄) * X 0 * X 2 + C (3 * W'.a₆) * X 2 ^ 2) := by
  rw [polynomialZ, polynomial]
  pderiv_simp
  ring1

lemma eval_polynomialZ (P : R × R × R) : eval ![P x, P y, P z] W'.polynomialZ =
    P y ^ 2 + W'.a₁ * P x * P y + 2 * W'.a₃ * P y * P z -
      (W'.a₂ * P x ^ 2 + 2 * W'.a₄ * P x * P z + 3 * W'.a₆ * P z ^ 2) := by
  rw [polynomialZ_eq]
  eval_simp
  rfl

/-- Euler's homogeneous function theorem in projective coordinates. -/
theorem polynomial_relation (P : R × R × R) : 3 * eval ![P x, P y, P z] W'.polynomial =
    P x * eval ![P x, P y, P z] W'.polynomialX + P y * eval ![P x, P y, P z] W'.polynomialY +
      P z * eval ![P x, P y, P z] W'.polynomialZ := by
  rw [eval_polynomial, eval_polynomialX, eval_polynomialY, eval_polynomialZ]
  ring1

variable (W') in
/-- The proposition that a projective point representative `(x, y, z)` on a Weierstrass curve `W` is
nonsingular.

In other words, either `W_X(x, y, z) ≠ 0`, `W_Y(x, y, z) ≠ 0`, or `W_Z(x, y, z) ≠ 0`.

Note that this definition is only mathematically accurate for fields. -/
-- TODO: generalise this definition to be mathematically accurate for a larger class of rings.
def Nonsingular (P : R × R × R) : Prop :=
  W'.Equation P ∧ (eval ![P x, P y, P z] W'.polynomialX ≠ 0 ∨
    eval ![P x, P y, P z] W'.polynomialY ≠ 0 ∨ eval ![P x, P y, P z] W'.polynomialZ ≠ 0)

lemma nonsingular_iff (P : R × R × R) : W'.Nonsingular P ↔ W'.Equation P ∧
    (W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z + W'.a₄ * P z ^ 2) ≠ 0 ∨
      2 * P y * P z + W'.a₁ * P x * P z + W'.a₃ * P z ^ 2 ≠ 0 ∨
      P y ^ 2 + W'.a₁ * P x * P y + 2 * W'.a₃ * P y * P z
        - (W'.a₂ * P x ^ 2 + 2 * W'.a₄ * P x * P z + 3 * W'.a₆ * P z ^ 2) ≠ 0) := by
  rw [Nonsingular, eval_polynomialX, eval_polynomialY, eval_polynomialZ]

lemma nonsingular_smul (P : R × R × R) {u : R} (hu : IsUnit u) :
    W'.Nonsingular (u • P) ↔ W'.Nonsingular P :=
  have hP {u : R} (hu : IsUnit u) {P : R × R × R} (hP : W'.Nonsingular <| u • P) :
      W'.Nonsingular P := by
    rcases (nonsingular_iff _).mp hP with ⟨hP, hP'⟩
    refine (nonsingular_iff P).mpr ⟨(equation_smul P hu).mp hP, ?_⟩
    contrapose! hP'
    rw [smul_eq]
    exact ⟨by linear_combination (norm := ring1) u ^ 2 * hP'.left,
      by linear_combination (norm := ring1) u ^ 2 * hP'.right.left,
      by linear_combination (norm := ring1) u ^ 2 * hP'.right.right⟩
  ⟨hP hu, fun h => hP hu.unit⁻¹.isUnit <| by rwa [smul_smul, hu.val_inv_mul, one_smul]⟩

lemma nonsingular_of_equiv {P Q : R × R × R} (h : P ≈ Q) : W'.Nonsingular P ↔ W'.Nonsingular Q := by
  rcases h with ⟨u, rfl⟩
  exact nonsingular_smul Q u.isUnit

lemma nonsingular_of_Z_eq_zero {P : R × R × R} (hPz : P z = 0) :
    W'.Nonsingular P ↔
      W'.Equation P ∧ (3 * P x ^ 2 ≠ 0 ∨ P y ^ 2 + W'.a₁ * P x * P y - W'.a₂ * P x ^ 2 ≠ 0) := by
  simp_rw [nonsingular_iff, hPz, zero_pow <| OfNat.ofNat_ne_zero _, mul_zero, zero_sub, neg_ne_zero,
    add_zero, ne_self_iff_false, false_or]

lemma nonsingular_zero [Nontrivial R] : W'.Nonsingular (0, 1, 0) := by
  simp_rw [nonsingular_of_Z_eq_zero, equation_zero, true_and, ← not_and_or]
  exact fun h => one_ne_zero <| by linear_combination (norm := ring1) h.right

lemma nonsingular_some (X Y : R) : W'.Nonsingular (X, Y, 1) ↔ W'.toAffine.Nonsingular X Y := by
  simp_rw [nonsingular_iff, equation_some, Affine.nonsingular_iff', Affine.equation_iff',
    and_congr_right_iff, ← not_and_or, not_iff_not, one_pow, mul_one, and_congr_right_iff, Iff.comm,
    iff_self_and]
  intro h hX hY
  linear_combination (norm := ring1) 3 * h - X * hX - Y * hY

lemma nonsingular_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.toAffine.Nonsingular (P x / P z) (P y / P z) :=
  (nonsingular_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans <| nonsingular_some ..

lemma nonsingular_iff_of_Z_ne_zero {P : F × F × F} (hPz : P z ≠ 0) :
    W.Nonsingular P ↔ W.Equation P ∧
      (eval ![P x, P y, P z] W.polynomialX ≠ 0 ∨ eval ![P x, P y, P z] W.polynomialY ≠ 0) := by
  rw [nonsingular_of_Z_ne_zero hPz, Affine.Nonsingular, ← equation_of_Z_ne_zero hPz,
    ← eval_polynomialX_of_Z_ne_zero hPz, div_ne_zero_iff, and_iff_left <| pow_ne_zero 2 hPz,
    ← eval_polynomialY_of_Z_ne_zero hPz, div_ne_zero_iff, and_iff_left <| pow_ne_zero 2 hPz]

lemma Y_ne_zero_of_Z_eq_zero [NoZeroDivisors R] {P : R × R × R} (hP : W'.Nonsingular P)
    (hPz : P z = 0) : P y ≠ 0 := by
  intro hPy
  simp_rw [nonsingular_of_Z_eq_zero hPz, X_eq_zero_of_Z_eq_zero hP.left hPz, hPy,
    zero_pow two_ne_zero, mul_zero, add_zero, sub_zero, or_self, ne_self_iff_false, and_false] at hP

lemma isUnit_Y_of_Z_eq_zero {P : F × F × F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P y) :=
  (Y_ne_zero_of_Z_eq_zero hP hPz).isUnit

lemma equiv_of_Z_eq_zero {P Q : F × F × F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : P ≈ Q := by
  have hPy : IsUnit <| P y := isUnit_Y_of_Z_eq_zero hP hPz
  have hQy : IsUnit <| Q y := isUnit_Y_of_Z_eq_zero hQ hQz
  use hPy.unit / hQy.unit
  simp_rw [Units.smul_def, smul_eq, X_eq_zero_of_Z_eq_zero hQ.left hQz, hQz, mul_zero,
    Units.val_div_eq_div_val, IsUnit.unit_spec, hQy.div_mul_cancel]
  congr! 2
  · exact (X_eq_zero_of_Z_eq_zero hP.left hPz).symm
  · exact hPz.symm

lemma equiv_zero_of_Z_eq_zero {P : F × F × F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    P ≈ (0, 1, 0) :=
  equiv_of_Z_eq_zero hP nonsingular_zero hPz rfl

lemma map_equiv_map (f : F →+* K) {P Q : F × F × F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    f ∘ P ≈ f ∘ Q ↔ P ≈ Q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hz : f (P z) = 0
    · exact equiv_of_Z_eq_zero hP hQ ((map_eq_zero_iff f f.injective).mp hz) <|
        (map_eq_zero_iff f f.injective).mp <| (Z_eq_zero_of_equiv h).mp hz
    · refine equiv_of_X_eq_of_Y_eq ((map_ne_zero_iff f f.injective).mp hz)
        ((map_ne_zero_iff f f.injective).mp <| hz.comp (Z_eq_zero_of_equiv h).mpr) ?_ ?_
      all_goals apply f.injective; map_simp
      exacts [X_eq_of_equiv h, Y_eq_of_equiv h]
  · rcases h with ⟨u, rfl⟩
    exact ⟨Units.map f u, (WeierstrassCurve.Projective.map_smul ..).symm⟩

variable (W') in
/-- The proposition that a projective point class on a Weierstrass curve `W` is nonsingular.

If `P` is a projective point representative on `W`, then `W.NonsingularLift ⟦P⟧` is definitionally
equivalent to `W.Nonsingular P`.

Note that this definition is only mathematically accurate for fields. -/
def NonsingularLift (P : PointClass R) : Prop :=
  P.lift W'.Nonsingular fun _ _ => propext ∘ nonsingular_of_equiv

lemma nonsingularLift_iff (P : R × R × R) : W'.NonsingularLift ⟦P⟧ ↔ W'.Nonsingular P :=
  Iff.rfl

lemma nonsingularLift_zero [Nontrivial R] : W'.NonsingularLift ⟦(0, 1, 0)⟧ :=
  nonsingular_zero

lemma nonsingularLift_some (X Y : R) :
    W'.NonsingularLift ⟦(X, Y, 1)⟧ ↔ W'.toAffine.Nonsingular X Y :=
  nonsingular_some X Y

/-! ## Maps and base changes -/

variable (f : R →+* S) (P : R × R × R)

@[simp]
lemma map_polynomial : (W'.map f).toProjective.polynomial = MvPolynomial.map f W'.polynomial := by
  simp_rw [polynomial]
  map_simp

variable {P} in
lemma Equation.map (h : W'.Equation P) : (W'.map f).toProjective.Equation (f ∘ P) := by
  rw [Equation, map_polynomial, eval_map, map_eq, ← map_fin3, ← eval₂_comp, h, map_zero]

variable {f} in
@[simp]
lemma map_equation (hf : Function.Injective f) :
    (W'.map f).toProjective.Equation (f ∘ P) ↔ W'.Equation P := by
  simp_rw [Equation, map_polynomial, eval_map, map_eq, ← map_fin3, ← eval₂_comp,
    map_eq_zero_iff f hf]

@[simp]
lemma map_polynomialX :
    (W'.map f).toProjective.polynomialX = MvPolynomial.map f W'.polynomialX := by
  simp_rw [polynomialX, map_polynomial, pderiv_map]

@[simp]
lemma map_polynomialY :
    (W'.map f).toProjective.polynomialY = MvPolynomial.map f W'.polynomialY := by
  simp_rw [polynomialY, map_polynomial, pderiv_map]

@[simp]
lemma map_polynomialZ :
    (W'.map f).toProjective.polynomialZ = MvPolynomial.map f W'.polynomialZ := by
  simp_rw [polynomialZ, map_polynomial, pderiv_map]

variable {f} in
@[simp]
lemma map_nonsingular (hf : Function.Injective f) :
    (W'.map f).toProjective.Nonsingular (f ∘ P) ↔ W'.Nonsingular P := by
  simp_rw [Nonsingular, map_equation P hf, map_polynomialX, map_polynomialY, map_polynomialZ,
    eval_map, map_eq, ← map_fin3, ← eval₂_comp, map_ne_zero_iff f hf]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A →ₐ[S] B) (P : A × A × A)

lemma baseChange_polynomial : (W'.baseChange B).toProjective.polynomial =
    MvPolynomial.map f (W'.baseChange A).toProjective.polynomial := by
  rw [← map_polynomial, map_baseChange]

variable {P} in
lemma Equation.baseChange (h : (W'.baseChange A).toProjective.Equation P) :
    (W'.baseChange B).toProjective.Equation (f ∘ P) := by
  convert Equation.map f.toRingHom h using 1
  rw [AlgHom.toRingHom_eq_coe, map_baseChange]

variable {f} in
lemma baseChange_equation (hf : Function.Injective f) :
    (W'.baseChange B).toProjective.Equation (f ∘ P) ↔
      (W'.baseChange A).toProjective.Equation P := by
  rw [← RingHom.coe_coe, ← map_equation P hf, AlgHom.toRingHom_eq_coe, map_baseChange]

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
lemma baseChange_nonsingular (hf : Function.Injective f) :
    (W'.baseChange B).toProjective.Nonsingular (f ∘ P) ↔
      (W'.baseChange A).toProjective.Nonsingular P := by
  rw [← RingHom.coe_coe, ← map_nonsingular P hf, AlgHom.toRingHom_eq_coe, map_baseChange]

end Projective

end WeierstrassCurve
