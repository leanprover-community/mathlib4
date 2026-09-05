/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.Ring.NamePolyVars
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The addition-and-subtraction map on x-coordinates

We set up the endomorphism of `ℙ²` that on affine points with affine sum is equal to

`(x(P) * x(Q) : x(P) + x(Q) : 1) ↦ (x(P+Q) * x(P-Q) : x(P+Q) + x(P-Q) : 1);`

see `WeierstrassCurve.addSubMap` (this is on coordinate vectors).

TODO: Show that the map really does what it is claimed to do.

This will be used to eventually show the approximate parallelogram law for `K`-points
on an elliptic curve `E`:
`∃ C, ∀ P Q : E(K), |h(P+Q) + h(P-Q) - 2*h(P) - 2*h(Q)| ≤ C`,
where `K` is a field with a height and `h` denotes the (logarithmic) naïve height on `E(K)`.
-/

public section

namespace WeierstrassCurve

/-!
### The addition-and-subtraction map on x-coordinates
-/

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

open MvPolynomial

name_poly_vars s, t, u over R

/-- The polynomial map on coordinate vectors giving
`(x(P) * x(Q) : x(P) + x(Q) : 1) ↦ (x(P+Q) * x(P-Q) : x(P+Q) + x(P-Q) : 1)`
for points `P`, `Q` on the Weierstrass curve `W`. -/
@[expose] noncomputable def addSubMap : Fin 3 → MvPolynomial (Fin 3) R :=
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
        C (4 * W.b₂ * W.b₄ * W.b₈ - 4 * W.b₂ * W.b₆ ^ 2) * t * u],
    ![C (-12) * t ^ 2 + C (-4 * W.b₂) * t * u + C (W.b₂ ^ 2 - 32 * W.b₄) * u ^ 2,
      C 6 * s * t + C (-W.b₂) * s * u + C (-5 * W.b₄) * t * u + C (W.b₂ * W.b₄ - 27 * W.b₆) * u ^ 2,
      C (-8 * W.b₄) * s * u + C (-12 * W.b₆) * t * u + C (W.b₄ ^ 2 - 28 * W.b₈) * u ^ 2]].uncurry

private lemma CXX {i : Fin 3} {a : R} : (C a * X (R := R) i ^ 2).IsHomogeneous 2 :=
  isHomogeneous_C_mul_X_pow ..

private lemma CXY {i j : Fin 3} {a : R} : (C a * X (R := R) i * X j).IsHomogeneous 2 :=
  .mul (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)

lemma isHomogeneous_addSubMap (i : Fin 3) : (addSubMap W i).IsHomogeneous 2 := by
  simp only [addSubMap]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero]
  · exact isHomogeneous_X_pow .. |>.sub CXY |>.sub CXY |>.sub CXX
  · exact CXY.add CXY |>.add CXY |>.add CXX
  · exact isHomogeneous_X_pow .. |>.sub CXY

lemma isHomogeneous_addSubMapCoeff (ij : Fin 3 × Fin 3) :
    (addSubMapCoeff W ij).IsHomogeneous 2 := by
  simp only [addSubMapCoeff]
  fin_cases ij <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.uncurry_apply_pair,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, neg_mul, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Fin.zero_eta]
    -- The following works, but is slow (44894 vs. 11717 heartbeats):
    -- <;> repeat first | refine .add ?_ CXY | refine .add ?_ CXX | exact CXX | exact CXY
  · exact CXX.add CXY |>.add CXY |>.add CXX |>.add CXY
  · exact CXX.add CXY |>.add CXY |>.add CXX |>.add CXY
  · exact CXX.add CXY |>.add CXY
  · exact CXY.add CXX |>.add CXY
  · exact CXX.add CXY |>.add CXX |>.add CXY
  · exact CXX.add CXY |>.add CXY |>.add CXX |>.add CXY
  · exact CXX.add CXY |>.add CXX
  · exact CXY.add CXY |>.add CXY |>.add CXX
  · exact CXY.add CXY |>.add CXX

variable [W.IsElliptic]

lemma addSubMapCoeff_condition (x : Fin 3 → R) (i : Fin 3) :
    ∑ j : Fin 3, (C (↑W.Δ'⁻¹ : R) * addSubMapCoeff W (i, j)).eval x *
      (addSubMap W j).eval x = x i ^ 4 := by
  simp only [eval_mul, eval_C, mul_assoc]
  rw [← Finset.mul_sum, Units.inv_mul_eq_iff_eq_mul, Fin.sum_univ_three, addSubMap, addSubMapCoeff,
    Function.uncurry_apply_pair, coe_Δ', Δ]
  fin_cases i <;> simp <;> grind only [b_relation]

lemma addSubMap_ne_zero [IsReduced R] {x : Fin 3 → R} (hx : x ≠ 0) :
    (addSubMap W · |>.eval x) ≠ 0 := by
  contrapose! hx
  ext i
  simpa [congrFun hx] using (addSubMapCoeff_condition W x i).symm

end WeierstrassCurve

/-!
### The symmetric square of the x-coordinate map

We define `Weierstrass.Affine.Point.sym2x`, which sends a pair `P`, `Q` of nonsingular points in
affine coordinates on a Weierstrass curve to a triple projectively equal to
`(x(P)*x(Q), x(P)+x(Q), 1)`, and provide some API.
-/

namespace WeierstrassCurve.Affine.Point

variable {R : Type*} [CommRing R] {W' : Affine R}

/-- This map sends a pair `P`, `Q` of nonsingular points in affine coordinates on `W`
to a triple projectively equivalent to `![x(P) * x(Q), x(P) + x(Q), 1]`.

In more geometric terms, this is the map `Sym² W → Sym² ℙ¹ ≃ ℙ²` induced by `x : W → ℙ¹`. -/
noncomputable def sym2x (P Q : W'.Point) : Fin 3 → R :=
  letI Px := P.xRep
  letI Qx := Q.xRep
  ![Px 0 * Qx 0, Px 0 * Qx 1 + Px 1 * Qx 0, Px 1 * Qx 1]

@[simp]
lemma sym2x_zero_zero : (0 : W'.Point).sym2x 0 = ![1, 0, 0] := by
  simp [sym2x]

@[simp]
lemma sym2x_zero_some {x y : R} (h : W'.Nonsingular x y) :
    (0 : W'.Point).sym2x (some x y h) = ![x, 1, 0] := by
  simp [sym2x]

@[simp]
lemma sym2x_some_zero {x y : R} (h : W'.Nonsingular x y) :
    (some x y h).sym2x 0 = ![x, 1, 0] := by
  simp [sym2x]

@[simp]
lemma sym2x_some_some {x y x' y' : R} (h : W'.Nonsingular x y) (h' : W'.Nonsingular x' y') :
    (some x y h).sym2x (some x' y' h') = ![x * x', x + x', 1] := by
  simp [sym2x]

lemma sym2x_ne_zero [Nontrivial R] (P Q : W'.Point) : P.sym2x Q ≠ 0 := by
  cases P <;> cases Q <;> simp [sym2x, xRep]

lemma sym2x_comm (P Q : W'.Point) : P.sym2x Q = Q.sym2x P := by
  cases P <;> cases Q <;> simp [← zero_def, mul_comm, add_comm]

@[simp]
lemma sym2x_neg_left (P Q : W'.Point) : (-P).sym2x Q = P.sym2x Q := by
  simp [sym2x]

@[simp]
lemma sym2x_neg_right (P Q : W'.Point) : P.sym2x (-Q) = P.sym2x Q := by
  simp [sym2x]

open Nat in
lemma sym2x_self_eq_addSubMap (P : W'.Point) :
    sym2x P P = (addSubMap W' · |>.eval <| sym2x P 0) := by
  match P with
  | 0 => ext i : 1; fin_cases i <;> simp [addSubMap]
  | some .. => ext i : 1; fin_cases i <;> simp [pow_two, two_mul, addSubMap]

section Field

variable {F : Type*} [Field F] {W : Affine F}

/- The explicit evaluation of `addSubMap` on `sym2x` of two nonzero points. -/
lemma addSubMap_sym2x_some_some {xP yP xQ yQ : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) :
    (addSubMap W · |>.eval <| sym2x (some xP yP hP) (some xQ yQ hQ)) =
      ![(xP * xQ) ^ 2 - W.b₄ * (xP * xQ) - W.b₆ * (xP + xQ) - W.b₈,
        2 * (xP + xQ) * (xP * xQ) + W.b₂ * (xP * xQ) + W.b₄ * (xP + xQ) + W.b₆, (xP - xQ) ^ 2] := by
  ext i : 1
  fin_cases i <;> simp [addSubMap]
  ring

/- The explicit evaluation of `addSubMap` on `sym2x` of two equal nonzero points.
The result involves the numerator and denominator of the duplication map on `x`-coordinates. -/
lemma addSubMap_sym2x_some_self {x y : F} (h : W.Nonsingular x y) :
    (addSubMap W · |>.eval <| sym2x (some x y h) (some x y h)) =
      ![x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈,
        4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆, 0] := by
  rw [addSubMap_sym2x_some_some]
  ext i : 1
  fin_cases i <;> dsimp <;> ring

variable [DecidableEq F]

/- This lemma can be deduced easily from the more general result that follows (it is used in its
proof for the special case `P = Q`), so can be private. -/
private lemma sym2x_add_self_zero (P : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + P) 0 = (addSubMap W · |>.eval <| sym2x P P) := by
  match P with
  | 0 => exact ⟨1, one_ne_zero, by ext i : 1; fin_cases i <;> simp [addSubMap]⟩
  | some x y h =>
    have Heq := (W.equation_iff x y).mp h.1
    rw [addSubMap_sym2x_some_self]
    by_cases H : y = W.negY x y
    · have H' := (den_duplication_eq_zero_iff h.1).mpr H
      rw [H', add_self_of_Y_eq H, sym2x_zero_zero]
      refine ⟨_, den_duplication_ne_zero_or_num_duplication_ne_zero h |>.neg_resolve_left H', ?_⟩
      simp
    · have H' := (den_duplication_eq_zero_iff h.1).not.mpr H
      exact ⟨_, H', by simp [sym2x, xRep_add_self_of_Y_ne h H, mul_div_cancel₀ _ H']⟩

/-- `sym2x (P + Q) (P - Q)` is equal, up to scaling by a nonzero constant, to `addSubMap W`
applied to `sym2x P Q`. -/
lemma sym2x_add_sub_eq_addSubMap_sym2x (P Q : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + Q) (P - Q) = (addSubMap W · |>.eval <| sym2x P Q) := by
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using P.sym2x_add_self_zero
  rcases eq_or_ne Q (-P) with rfl | hPQ'
  · simpa [sym2x_comm] using P.sym2x_add_self_zero
  match P, Q with
  | P, 0 =>  exact ⟨1, one_ne_zero, by simpa using P.sym2x_self_eq_addSubMap⟩
  | 0, Q =>
    refine ⟨1, one_ne_zero, ?_⟩
    simpa [sym2x_comm] using Q.sym2x_self_eq_addSubMap
  | some xP yP hP, some xQ yQ hQ =>
    have hxPQ : xP ≠ xQ := fun Heq ↦ by grind only [X_eq_iff.mp Heq]
    refine ⟨(xP - xQ) ^ 2, pow_ne_zero 2 (sub_ne_zero_of_ne hxPQ), ?_⟩
    rw [addSubMap_sym2x_some_some, sym2x, xRep_add_of_X_ne hP hQ hxPQ,
      xRep_sub_of_X_ne hP hQ hxPQ, b₂, b₄, b₆, b₈]
    ext i : 1
    -- The following relations are needed for the `grobner` calls below.
    have HeqP := (W.equation_iff xP yP).mp hP.1
    have HeqQ := (W.equation_iff xQ yQ).mp hQ.1
    fin_cases i <;> simp [field] <;> grobner

end Field

end WeierstrassCurve.Affine.Point

end
