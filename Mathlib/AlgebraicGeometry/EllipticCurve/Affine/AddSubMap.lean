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
# The addition-and-subtraction map on x-coordinates

We set up the endomorphism of `ℙ²` that on affine points with affine sum is equal to
```
(x(P) * x(Q) : x(P) + x(Q) : 1) ↦ (x(P+Q) * x(P-Q) : x(P+Q) + x(P-Q) : 1) ;
```
see `WeierstrassCurve.addSubMap` (this is on coordinate vectors).

TODO: We show that the map really does what it is claimed to do.

This will be used to eventually show the approximate parallelogram law:
`∃ C, ∀ P Q : E(K), |h(P+Q) + h(P-Q) - 2*h(P) - 2*h(Q)| ≤ C`,
where `K` is a field with a height and `h` denotes the (logarithmic) naïve height on `E(K)`.
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
        C (2 * W.b₂ * W.b₄ * W.b₈ - 2 * W.b₄ ^ 2 * W.b₆ - 10 * W.b₆ * W.b₈) * s * t +
        C (-W.b₂ * W.b₆ * W.b₈ + W.b₄ * W.b₆ ^ 2) * s * u +
        C (3 * W.b₄ ^ 2 * W.b₈ - 3 * W.b₄ * W.b₆ ^ 2) * t ^ 2 +
        C (3 * W.b₄ * W.b₆ * W.b₈ - 3 * W.b₆ ^ 3) * t * u,
      C (-W.b₂ * W.b₄ * W.b₈ + W.b₄ ^ 2 * W.b₆ + 5 * W.b₆ * W.b₈) * s ^ 2 +
        C (2 * W.b₂ * W.b₆ * W.b₈ - 2 * W.b₄ * W.b₆ ^ 2 - 10 * W.b₈ ^ 2) * s * t +
        C (-W.b₂ * W.b₈ ^ 2 + W.b₄ * W.b₆ * W.b₈) * s * u +
        C (3 * W.b₄ * W.b₆ * W.b₈ - 3 * W.b₆ ^ 3) * t ^ 2 +
        C (3 * W.b₄ * W.b₈ ^ 2 - 3 * W.b₆ ^ 2 * W.b₈) * t * u,
      C (W.b₂ * W.b₆ * W.b₈ - 8 * W.b₄ ^ 2 * W.b₈ + 7 * W.b₄ * W.b₆ ^ 2) * s ^ 2 +
        C (-6 * W.b₄ * W.b₆ * W.b₈ + 6 * W.b₆ ^ 3) * s * t +
        C (-8 * W.b₄ * W.b₈ ^ 2 + 8 * W.b₆ ^ 2 * W.b₈) * s * u],
    ![C (96 * W.b₆) * s * t + C (12 * W.b₂ * W.b₆ - 64 * W.b₈) * t ^ 2 +
        C (16 * W.b₄ * W.b₆) * t * u,
      C (-48 * W.b₆) * s ^ 2 + C (32 * W.b₈) * s * t +
        C (-4 * W.b₂ * W.b₈ + 16 * W.b₄ * W.b₆) * t ^ 2 + C (16 * W.b₄ * W.b₈) * t * u,
      C (-12 * W.b₂ * W.b₆) * s ^ 2 + C (8 * W.b₂ * W.b₈ - 32 * W.b₄ * W.b₆) * s * t +
        C (-12 * W.b₆ ^ 2) * s * u +
        C (-W.b₂ ^ 2 * W.b₈ + 9 * W.b₂ * W.b₄ * W.b₆ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2) * t ^ 2 +
        C (4 * W.b₂ * W.b₄ * W.b₈ - 4 * W.b₂ * W.b₆ ^ 2 ) * t * u],
    ![C (-12) * t ^ 2 + C (-4 * W.b₂) * t * u + C (W.b₂ ^ 2 - 32 * W.b₄) * u ^ 2,
      C 6 * s * t + C (-W.b₂) * s * u + C (-5 * W.b₄) * t * u + C (W.b₂ * W.b₄ - 27 * W.b₆) * u ^ 2,
      C (-8 * W.b₄) * s * u + C (-12 * W.b₆) * t * u + C (W.b₄ ^ 2 - 28 * W.b₈) * u ^ 2]].uncurry

/-- The multiples of the relation `W.b_relation`, which is equivalent to
`4*W.b₈ - W.b₂*W.b₆ + W.b₄^2 = 0`, that we have to add to show the equality in
`addSubMapCoeff_condition` below. -/
noncomputable def bRelationCoeffs : Fin 3 → MvPolynomial (Fin 3) R :=
  ![C (-8 * W.b₄ ^ 2) * s ^ 3 * u + C (5 * W.b₈) * s ^ 2 * t ^ 2 +
      C (3 * W.b₂ * W.b₈ - 11 * W.b₄ * W.b₆) * s ^ 2 * t * u +
      C (-8 * W.b₄ * W.b₈) * s ^ 2 * u ^ 2 + C (3 * W.b₄ * W.b₈ - 3 * W.b₆ ^ 2) * s * t ^ 2 * u,
    C (-32 * W.b₄) * s * t ^ 2 * u + C (16 * W.b₆) * s * t * u ^ 2 + C (-16 * W.b₆) * t ^ 3 * u +
      C (-16 * W.b₈) * t ^ 2 * u ^ 2,
    C (-28) * s * u ^ 3 + C 4 * t ^ 2 * u ^ 2 + C (-W.b₂) * t * u ^ 3 + C (-8 * W.b₄) * u ^ 4]

variable {a} in
private lemma CXX {i : Fin 3} : (C a * X (R := R) i ^ 2).IsHomogeneous 2 :=
    isHomogeneous_C_mul_X_pow ..

variable {a} in
private lemma CXY {i j : Fin 3} : (C a * X (R := R) i * X j).IsHomogeneous 2 :=
    .mul (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)

lemma isHomogeneous_addSubMap (i : Fin 3) : (addSubMap W i).IsHomogeneous 2 := by
  simp only [addSubMap]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero]
  · exact .sub (.sub (.sub (isHomogeneous_X_pow ..) CXY) CXY) CXX
  · exact .add (.add (.add CXY CXY) CXY) CXX
  · exact .sub (isHomogeneous_X_pow ..) CXY

lemma isHomogeneous_addSubMapCoeff (ij : Fin 3 × Fin 3) :
    (addSubMapCoeff W ij).IsHomogeneous 2 := by
  simp only [addSubMapCoeff]
  fin_cases ij <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.uncurry_apply_pair,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, neg_mul, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Fin.zero_eta]
    -- The following works, but is slow (44883 vs. 11592 heartbeats):
    -- <;> repeat first | refine .add ?_ CXY | refine .add ?_ CXX | exact CXX | exact CXY
  · exact .add (.add (.add (.add CXX CXY) CXY) CXX) CXY
  · exact .add (.add (.add (.add CXX CXY) CXY) CXX) CXY
  · exact .add (.add CXX CXY) CXY
  · exact .add (.add CXY CXX) CXY
  · exact .add (.add (.add CXX CXY) CXX) CXY
  · exact .add (.add (.add (.add CXX CXY) CXY) CXX) CXY
  · exact .add (.add CXX CXY) CXX
  · exact .add (.add (.add CXY CXY) CXY) CXX
  · exact .add (.add CXY CXY) CXX

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
    rw [← sub_eq_zero, ← this] <;> simp [bRelationCoeffs] <;> ring

lemma addSubMap_ne_zero [IsDomain R] {x : Fin 3 → R} (hx : x ≠ 0) :
    (fun i ↦ (addSubMap W i).eval x) ≠ 0 := by
  contrapose! hx
  ext i : 1
  replace hx i : (addSubMap W i).eval x = 0 := by
    rw [Pi.zero_def, funext_iff] at hx
    exact hx i
  simpa [hx] using (addSubMapCoeff_condition W x i).symm

end WeierstrassCurve

end
