/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

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

variable {K : Type*} [Field K] (a b : K)

open MvPolynomial

/-- The polynomial map on coordinate vectors giving
`(x(P) * x(Q) : x(P) + x(Q) : 1) ↦ (x(P+Q) * x(P-Q) : x(P+Q) + x(P-Q) : 1)`
for points `P`, `Q` on the elliptic curve `y² = x³ + a*x + b`. -/
noncomputable def addSubMap : Fin 3 → MvPolynomial (Fin 3) K :=
  letI s := X 0
  letI t := X 1
  letI u := X 2
  ![s ^ 2 - C (2 * a) * s * u - C (4 * b) * t * u + C (a ^ 2) * u ^ 2,
    C 2 * t * s + C (2 * a) * t * u + C (4 * b) * u ^ 2,
    t ^ 2 - C 4 * s * u]

/-- The coefficient polynomials in linear combinations of the polynomials in `addSubMap`
that result in the fourth powers of the variables, multiplied by `32*a^3 + 216*b^2`. -/
noncomputable def addSubMapCoeff : Fin 3 × Fin 3 → MvPolynomial (Fin 3) K :=
  letI s := X (σ := Fin 3) 0
  letI t := X (σ := Fin 3) 1
  letI u := X (σ := Fin 3) 2
  ![![C (-4 * a ^ 2 * b) * t * s + C (12 * a ^ 3 * b + 96 * b ^ 3) * t * u +
        C (32 * a ^ 3 + 216 * b ^ 2) * s ^ 2 + C (24 * a ^ 4 + 176 * a * b ^ 2) * s * u,
      C (5 * a ^ 4 + 32 * a * b ^ 2 ) * t * s + C (-3 * a ^ 5 - 24 * a ^ 2 * b ^ 2) * t * u +
        C (2 * a ^ 2 * b) * s ^ 2 + C (52 * a ^ 3 * b + 384 * b ^ 3) * s * u,
      C (-10 * a ^ 4 - 64 * a * b ^ 2) * s ^ 2 + C (-4 * a ^ 5 - 32 * a ^ 2 * b ^ 2) * s * u +
        C (6 * a ^ 6 + 96 * a ^ 3 * b ^ 2 + 384 * b ^ 4) * u ^ 2],
    ![C (128 * a * b) * t * u - C (128 * a ^ 2) * s * u + C (384 * b ^ 2) * u ^ 2,
      C (16 * a ^ 2) * t * s + C (16 * a ^ 3 + 384 * b ^ 2) * t * u - C (64 * a * b) * s * u -
        C (96 * a ^ 2 * b) * u ^ 2,
      C (32 * a ^ 3 + 216 * b ^ 2) * t ^ 2 - C (32 * a ^ 2) * s ^ 2 +
        C (64 * a ^ 3 + 96 * b ^ 2) * s * u + C (-32 * a ^ 4 - 256 * a * b ^ 2) * u ^ 2],
    ![C 24 * s * u + C (32 * a) * u ^ 2,
      C (-3) * t * s  + C (5 * a) * t * u + C (54 * b) * u ^ 2,
      C 6 * s ^ 2 - C (4 * a) * s * u - C (10 * a ^ 2) * u ^ 2]].uncurry

lemma isHomogeneous_addSubMap (i : Fin 3) : (addSubMap a b i).IsHomogeneous 2 := by
  simp only [addSubMap]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero]
  · refine .add (.sub (.sub (isHomogeneous_X_pow ..) ?_) ?_) (isHomogeneous_C_mul_X_pow ..) <;>
      exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add (.add ?_ ?_) (isHomogeneous_C_mul_X_pow ..) <;>
      exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · exact .sub (isHomogeneous_X_pow ..) <|
      .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)

lemma isHomogenous_addSubMapCoeff (ij : Fin 3 × Fin 3) :
    (addSubMapCoeff a b ij).IsHomogeneous 2 := by
  simp only [addSubMapCoeff]
  fin_cases ij <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.uncurry_apply_pair,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, neg_mul, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Fin.zero_eta]
  · refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact isHomogeneous_C_mul_X_pow ..
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .sub ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .sub ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .sub ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .sub (isHomogeneous_C_mul_X_pow ..) (isHomogeneous_C_mul_X_pow ..)
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .add ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .add ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
  · refine .sub ?_ (isHomogeneous_C_mul_X_pow ..)
    refine .sub ?_ <| .mul (m := 1) (n := 1) (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
    exact isHomogeneous_C_mul_X_pow ..

variable (hab : 32 * a ^ 3 + 216 * b ^ 2 ≠ 0)

variable {a b}

include hab in
lemma addSubMapCoeff_condition (x : Fin 3 → K) (i : Fin 3) :
    ∑ j : Fin 3, (C ((32 * a ^ 3 + 216 * b ^ 2)⁻¹) * addSubMapCoeff a b (i, j)).eval x *
      (addSubMap a b j).eval x = x i ^ (2 + 2) := by
  simp only [eval_mul, eval_C, mul_assoc]
  rw [← Finset.mul_sum, inv_mul_eq_iff_eq_mul₀ hab, Fin.sum_univ_three]
  simp only [addSubMap, addSubMapCoeff, Function.uncurry_apply_pair]
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, neg_mul, Fin.zero_eta,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, map_add, map_mul, eval_C, map_pow,
      eval_X, map_neg, Fin.reduceFinMk, Matrix.cons_val, Fin.mk_one] <;>
    ring

include hab in
lemma addSubMap_ne_zero {x : Fin 3 → K} (hx : x ≠ 0) : (fun i ↦ (addSubMap a b i).eval x) ≠ 0 := by
  contrapose! hx
  ext1 i
  replace hx i : (addSubMap a b i).eval x = 0 := by
    rw [Pi.zero_def, _root_.funext_iff] at hx
    exact hx i
  simpa [hx] using (addSubMapCoeff_condition hab x i).symm

end WeierstrassCurve

end
