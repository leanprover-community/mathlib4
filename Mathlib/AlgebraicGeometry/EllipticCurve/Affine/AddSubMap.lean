/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.Ring.NamePolyVars

/-!
# The approximate parallelogram law on elliptic curves

If `K` is a field with `AdmissibleAbsoluteValues` and `E` is an elliptic curve over `K`,
let `h : E(K) → ℝ` be the naïve height of the x-coordinate.

The goal of this file is to show the approximate parallelogram law:
`∃ C, ∀ P Q : E(K), |h(P+Q) + h(P-Q) - 2*h(P) - 2*h(Q)| ≤ C`,
where `h` denotes the (logarithmic) naïve height on `E(K)`,
and to show that there are only finitely many points in `E(K)` of bounded height
when `K` has the Northcott property.
-/

public section

namespace WeierstrassCurve

/-!
### The addition-and-subtraction map on x-coordinates
-/

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (a b : R)

open MvPolynomial

name_poly_vars s, t, u over R

/-- The polynomial map on coordinate vectors giving
`(x(P) * x(Q) : x(P) + x(Q) : 1) ↦ (x(P+Q) * x(P-Q) : x(P+Q) + x(P-Q) : 1)`
for points `P`, `Q` on the elliptic curve `W`. -/
noncomputable def addSubMap : Fin 3 → MvPolynomial (Fin 3) R :=
  ![s ^ 2 - C W.b₄ * s * u - C W.b₆ * t * u - C W.b₈ * u ^ 2,
    C 2 * t * s + C W.b₂ * s * u + C W.b₄ * t * u + C W.b₆ * u ^ 2,
    t ^ 2 - C 4 * s * u]

/-- The coefficient polynomials in linear combinations of the polynomials in `addSubMap`
that result in the fourth powers of the variables, multiplied by `W.Δ`. -/
noncomputable def addSubMapCoeff : Fin 3 × Fin 3 → MvPolynomial (Fin 3) R :=
  ![![C (-W.b₂ ^ 2 * W.b₈ + 9 * W.b₂ * W.b₄ * W.b₆ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2) * s ^ 2 +
        C (2 * W.b₂ * W.b₄ * W.b₈ - 2 * W.b₄ ^ 2 * W.b₆ + 8 * W.b₆ * W.b₈) * s * t +
        C (8 * W.b₄ ^ 2 * W.b₈ + W.b₄ * W.b₆ ^ 2 - 16 * W.b₈ ^ 2) * s * u +
        C (3 * W.b₂ * W.b₆ * W.b₈ - 3 * W.b₄ * W.b₆ ^ 2) * t ^ 2 +
        C (12 * W.b₄ * W.b₆ * W.b₈ - 3 * W.b₆ ^ 3) * t * u +
        C (9 * W.b₆ ^ 2 * W.b₈) * u ^ 2,
      C (-W.b₂ * W.b₄ * W.b₈ + W.b₄ ^ 2 * W.b₆ - 4 * W.b₆ * W.b₈) * s ^ 2 +
        C (2 * W.b₂ * W.b₆ * W.b₈ - 2 * W.b₄ * W.b₆^2 - 10 * W.b₈ ^ 2) * s * t  +
        C (-W.b₂ * W.b₈ ^ 2 + 10 * W.b₄ * W.b₆ * W.b₈) * s * u +
        C (3 * W.b₄ * W.b₆ * W.b₈ - 3 * W.b₆ ^ 3) * t ^ 2 +
        C (3 * W.b₄ * W.b₈ ^ 2 + 6 * W.b₆ ^ 2 * W.b₈) * t * u +
        C (9 * W.b₆ * W.b₈ ^ 2) * u ^ 2,
      C (-7 * W.b₂ * W.b₆ * W.b₈ + 7 * W.b₄ * W.b₆ ^ 2 + 20 * W.b₈ ^ 2) * s ^ 2 +
        C (-6 * W.b₄ * W.b₆ * W.b₈ + 6 * W.b₆ ^ 3) * s * t +
        C (4 * W.b₄ * W.b₈ ^ 2 + 8 * W.b₆ ^ 2 * W.b₈) * s * u +
        C (8 * W.b₂ * W.b₆ ^ 2 * W.b₈ - 8 * W.b₄ ^ 2 * W.b₆ * W.b₈ - 20 * W.b₆ * W.b₈ ^ 2) * t * u +
        C (8 * W.b₂ * W.b₆ * W.b₈ ^ 2 - 8 * W.b₄ ^ 2 * W.b₈ ^ 2 - 20 * W.b₈ ^ 3) * u ^ 2],
    ![C (96 * W.b₆) * s * t +  C (-256 * W.b₈) * s * u + C (12 * W.b₂ * W.b₆) * t ^ 2 +
        C (16 * W.b₄ * W.b₆) * t * u,
      C (-48 * W.b₆) * s ^ 2 + C (32 * W.b₈) * s * t +
        C (-4 * W.b₂ * W.b₈ + 16 * W.b₄ * W.b₆) * t ^ 2 + C (16 * W.b₄ * W.b₈) * t * u,
      C (-12 * W.b₂ * W.b₆ - 64 * W.b₈) * s ^ 2 + C (8 * W.b₂ * W.b₈ - 32 * W.b₄ * W.b₆) * s * t +
        C (64 * W.b₄ * W.b₈ - 12 * W.b₆ ^ 2) * s * u +
        C (-W.b₂ ^ 2 * W.b₈ + 9 * W.b₂ * W.b₄ * W.b₆ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2) * t ^ 2 +
        C (4 * W.b₂ * W.b₄ * W.b₈ - 4 * W.b₄ ^ 2 * W.b₆ + 48 * W.b₆ * W.b₈) * t * u +
        C (64 * W.b₈ ^ 2) * u ^ 2],
    ![C (-48) * s * u + C (-4 * W.b₂) * t * u +  C (W.b₂ ^ 2 - 32 * W.b₄) * u ^ 2,
      C 6 * s * t + C (-W.b₂) * s * u + C (-5 * W.b₄) * t * u + C (W.b₂ * W.b₄ - 27 * W.b₆) * u ^ 2,
      C (-12) * s ^ 2 + C (4 * W.b₄) * s * u +
        C (-31 * W.b₂ * W.b₆ + 32 * W.b₄^2 + 108 * W.b₈) * u ^ 2]].uncurry

/-- The multipless of the relation `W.b_relation`, which is equivalent to
`4*W.b₈ - W.b₂*W.b₆ + W.b₄^2 = 0`, that we have to add to show the equality in
`addSubMapCoeff_condition` below. -/
noncomputable def bRelationCoeffs : Fin 3 → MvPolynomial (Fin 3) R :=
  ![C (3 * W.b₂ * W.b₈) * s ^ 2 * t * u + C (-8 * W.b₄ ^ 2) * s ^ 3 * u +
      C (-11 * W.b₄ * W.b₆) * s ^ 2 * t * u + C (-3 * W.b₆ ^ 2) * s * t ^ 2 * u +
      C (-24 * W.b₆ * W.b₈) * s * t * u ^ 2 + C (5 * W.b₆ * W.b₈) * t ^ 3 * u +
      C (-24 * W.b₈ ^ 2) * s * u ^ 3 + C (5 * W.b₈ ^ 2) * t ^ 2 * u ^ 2 +
      C (24 * W.b₈) * s ^ 3 * u,
    C (-32 * W.b₄) * s * t ^ 2 * u + C (-12 * W.b₆) * t ^ 3 * u + C (-16 * W.b₈) * t ^ 2 * u ^ 2,
    C (-W.b₂) * t * u ^ 3 + C (-8 * W.b₄) * u ^ 4 + C 96 * s * u ^ 3 + C (-27) * t ^ 2 * u ^ 2]

lemma isHomogeneous_addSubMap (i : Fin 3) : (addSubMap W i).IsHomogeneous 2 := by
  simp only [addSubMap]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero]
  · refine .sub (.sub (.sub (isHomogeneous_X_pow ..) ?_) ?_) (isHomogeneous_C_mul_X_pow ..) <;>
      exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add (.add (.add ?_ ?_) ?_) (isHomogeneous_C_mul_X_pow ..) <;>
      exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · exact .sub (isHomogeneous_X_pow ..) <|
      .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)

lemma isHomogenous_addSubMapCoeff (ij : Fin 3 × Fin 3) :
    (addSubMapCoeff W ij).IsHomogeneous 2 := by
  simp only [addSubMapCoeff]
  fin_cases ij <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.uncurry_apply_pair,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, neg_mul, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Fin.zero_eta]
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact isHomogeneous_C_mul_X_pow ..
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact isHomogeneous_C_mul_X_pow ..
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact isHomogeneous_C_mul_X_pow ..
  · refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact isHomogeneous_C_mul_X_pow ..
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact isHomogeneous_C_mul_X_pow ..
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact isHomogeneous_C_mul_X_pow ..

variable [W.IsElliptic]

lemma addSubMapCoeff_condition (x : Fin 3 → R) (i : Fin 3) :
    ∑ j : Fin 3, (C (↑W.Δ'⁻¹ : R) * addSubMapCoeff W (i, j)).eval x *
      (addSubMap W j).eval x = x i ^ (2 + 2) := by
  have hr : 4 * W.b₈ - W.b₂ * W.b₆ + W.b₄ ^ 2 = 0 := by linear_combination W.b_relation
  simp only [eval_mul, eval_C, mul_assoc]
  rw [← Finset.mul_sum, Units.inv_mul_eq_iff_eq_mul, Fin.sum_univ_three]
  simp only [addSubMap, addSubMapCoeff, Function.uncurry_apply_pair]
  have : -(bRelationCoeffs W i).eval x * (4 * W.b₈ - W.b₂ * W.b₆ + W.b₄ ^ 2) = 0 := by simp [hr]
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, neg_mul, Fin.zero_eta,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, map_add, map_mul, eval_C, map_pow,
      eval_X, map_neg, Fin.reduceFinMk, Matrix.cons_val, Fin.mk_one, coe_Δ', Δ] <;>
    rw [← sub_eq_zero] <;>
    simp [← this, bRelationCoeffs] <;>
    ring

lemma addSubMap_ne_zero [IsDomain R] {x : Fin 3 → R} (hx : x ≠ 0) :
    (fun i ↦ (addSubMap W i).eval x) ≠ 0 := by
  contrapose! hx
  ext i : 1
  replace hx i : (addSubMap W i).eval x = 0 := by
    rw [Pi.zero_def, _root_.funext_iff] at hx
    exact hx i
  simpa [hx] using (addSubMapCoeff_condition W x i).symm

end WeierstrassCurve

end
