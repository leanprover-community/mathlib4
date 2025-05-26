/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point


/-!

# Tate normal form of elliptic curves

This file defines the Tate normal form of Weierstrass equations of elliptic curves. It
parametrises elliptic curves with a given point `P` with `P, 2P, 3P ≠ 0`.

The equation is $$y^2 + (1-c)xy - by = x^3 - bx^2$$, and the point `P` is moved to `(0, 0)`.

We also have the following formulas:
* `P = (0, 0)`.
* `2P = (b, bc)`.
* `3P = (c, b-c)`.
* `-P = (0, b)`.
* `-2P = (b, 0)`.
* `-3P = (c, c^2)`.

Importantly, we have generalised the results here to work over any commutative ring `R`.

## Main definitions and results

* `IsTateNF W`: A typeclass saying that the Weierstrass curve `W` is in Tate normal form.
* `toTateNF W`: Given a point `P` satisfying the condition `P, 2P, 3P ≠ 0`, this is a variable
change that brings the Weierstrass curve `W` to Tate normal form.

## References

* [James Parson, Moduli of Elliptic Curves](https://math.stanford.edu/~conrad/vigregroup/vigre03/moduli.pdf)
-/

noncomputable section

namespace WeierstrassCurve

@[mk_iff]
class IsTateNF {R : Type*} [Zero R] (W : WeierstrassCurve R) : Prop where
  a₂₃ : W.a₂ = W.a₃
  a₄  : W.a₄ = 0
  a₆  : W.a₆ = 0

namespace Affine.Point

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} (P : W.toAffine.Point)

@[mk_iff]
class NeZero : Prop where
  neZero : P ≠ 0

def X : W.toAffine.Point → R
  | 0 => 0
  | @some _ _ _ x _ _ => x

def Y : W.toAffine.Point → R
  | 0 => 0
  | @some _ _ _ _ y _ => y

variable (W) in
@[simp] lemma not_neZero_zero : ¬(NeZero (0 : W.toAffine.Point)) :=
  fun ⟨h⟩ ↦ h rfl

lemma equation_X_Y [NeZero P] : W.toAffine.Equation P.X P.Y := by
  cases P with
  | zero => exact (not_neZero_zero W).elim (by assumption)
  | some h => exact h.1

lemma equation_X_Y' [NeZero P] : P.Y^2 + W.a₁ * P.X * P.Y + W.a₃ * P.Y
    = P.X^3 + W.a₂ * P.X^2 + W.a₄ * P.X + W.a₆ :=
  (equation_iff ..).1 P.equation_X_Y

/-- ∂W/∂X -/
def pX : R :=
  W.a₁ * P.Y - (3 * P.X ^ 2 + 2 * W.a₂ * P.X + W.a₄)

/-- ∂W/∂Y -/
def pY : R :=
  2 * P.Y + W.a₁ * P.X + W.a₃

/-- The condition `2 • P ≠ 0` on all fibres. -/
@[mk_iff]
class TwiceNeZero : Prop extends P.NeZero where
  twiceNeZero : IsUnit P.pY

lemma isUnit_pY [P.TwiceNeZero] : IsUnit P.pY :=
  TwiceNeZero.twiceNeZero

lemma pY_ne_zero [P.TwiceNeZero] [Nontrivial R] : P.pY ≠ 0 :=
  P.isUnit_pY.ne_zero

def pY_inv [P.TwiceNeZero] : Rˣ :=
  P.isUnit_pY.unit⁻¹

@[simp] lemma pY_mul_inv [P.TwiceNeZero] : P.pY * P.pY_inv = 1 := by
  have : P.isUnit_pY.unit * P.isUnit_pY.unit⁻¹ = 1 := mul_inv_cancel _
  rwa [Units.ext_iff, Units.val_mul, IsUnit.unit_spec] at this

@[simp] lemma pY_inv_mul [P.TwiceNeZero] : P.pY_inv * P.pY = 1 :=
  (mul_comm ..).trans P.pY_mul_inv

@[simp] lemma pY_inv_inv [P.TwiceNeZero] : P.pY_inv⁻¹ = P.pY :=
  by rw [pY_inv, inv_inv]; rfl

def μ [P.TwiceNeZero] : R :=
  W.a₂ + 3 * P.X + P.pX * P.pY_inv * W.a₁ - (P.pX * P.pY_inv) ^ 2

/-- The condition `3 • P ≠ 0` on all fibres. -/
@[mk_iff]
class ThriceNeZero : Prop extends P.NeZero where
  thriceNeZero : IsUnit ((W.a₂ + 3 * P.X) * P.pY ^ 2 + P.pX * W.a₁ * P.pY - P.pX ^ 2)

lemma thriceNeZero_isUnit [P.ThriceNeZero] :
    IsUnit ((W.a₂ + 3 * P.X) * P.pY ^ 2 + P.pX * W.a₁ * P.pY - P.pX ^ 2) :=
  ThriceNeZero.thriceNeZero

lemma isUnit_μ [P.TwiceNeZero] [P.ThriceNeZero] : IsUnit P.μ := by
  convert P.thriceNeZero_isUnit.mul (P.pY_inv ^ 2).isUnit using 1; calc
  _ = (W.a₂ + 3 * P.X) * (P.pY * P.pY_inv) ^ 2
        + P.pX * P.pY_inv * (P.pY * P.pY_inv) * W.a₁ - (P.pX * P.pY_inv) ^ 2 :=
    by rw [P.pY_mul_inv, μ]; simp
  _ = _ :=  by rw [Units.val_pow_eq_pow_val]; ring_nf

def μ_inv [P.TwiceNeZero] [P.ThriceNeZero] : Rˣ :=
  P.isUnit_μ.unit⁻¹

@[simp] lemma μ_mul_inv [P.TwiceNeZero] [P.ThriceNeZero] : P.μ * P.μ_inv = 1 := by
  have : P.isUnit_μ.unit * P.isUnit_μ.unit⁻¹ = 1 := mul_inv_cancel _
  rwa [Units.ext_iff, Units.val_mul, IsUnit.unit_spec] at this

@[simp] lemma μ_inv_mul [P.TwiceNeZero] [P.ThriceNeZero] : P.μ_inv * P.μ = 1 :=
  (mul_comm ..).trans P.μ_mul_inv

@[simp] lemma μ_inv_inv [P.TwiceNeZero] [P.ThriceNeZero] : P.μ_inv⁻¹ = P.μ :=
  by rw [μ_inv, inv_inv]; rfl

end Affine.Point

namespace Affine

variable {R : Type*} [CommRing R] (W : Affine R) (P : W.toAffine.Point)

def ofNeZero : VariableChange R where
  u := 1
  r := P.X
  s := 0
  t := P.Y

@[simp] lemma ofNeZero_a₆ [P.NeZero] : (W.ofNeZero P • W).a₆ = 0 :=
  equation_zero.1 <| (equation_iff_variableChange ..).1 <| P.equation_X_Y

@[simp] lemma ofNeZero_a₄ [P.NeZero] : (W.ofNeZero P • W).a₄ = -P.pX := by
  simp [ofNeZero, Point.pX]; ring_nf

@[simp] lemma ofNeZero_a₃ [P.NeZero] : (W.ofNeZero P • W).a₃ = P.pY := by
  simp [ofNeZero, Point.pY]; ring_nf

@[simp] lemma ofNeZero_a₂ [P.NeZero] : (W.ofNeZero P • W).a₂ = W.a₂ + 3 * P.X := by
  simp [ofNeZero]

@[simp] lemma ofNeZero_a₁ [P.NeZero] : (W.ofNeZero P • W).a₁ = W.a₁ := by
  simp [ofNeZero]

def ofTwiceNeZero_aux [P.TwiceNeZero] : VariableChange R where
  u := 1
  r := 0
  s := -P.pX * P.pY_inv
  t := 0

def ofTwiceNeZero [P.TwiceNeZero] : VariableChange R where
  u := 1
  r := P.X
  s := -P.pX * P.pY_inv
  t := P.Y

lemma ofTwiceNeZero_eq [P.TwiceNeZero] : W.ofTwiceNeZero P =
    W.ofTwiceNeZero_aux P * W.ofNeZero P :=
  by simp [ofTwiceNeZero, ofTwiceNeZero_aux, ofNeZero, VariableChange.mul_def]

@[simp] lemma ofTwiceNeZero_a₆ [P.TwiceNeZero] : (W.ofTwiceNeZero P • W).a₆ = 0 := by
  rw [ofTwiceNeZero_eq, mul_smul, variableChange_a₆, ofTwiceNeZero_aux]
  simp [-variableChange_a₆]

@[simp] lemma ofTwiceNeZero_a₄ [P.TwiceNeZero] : (W.ofTwiceNeZero P • W).a₄ = 0 := calc
  _ = -P.pX + P.pX * P.pY_inv * P.pY := by
    rw [ofTwiceNeZero_eq, mul_smul, variableChange_a₄, ofTwiceNeZero_aux]
    simp [-variableChange_a₄, -variableChange_a₃]
  _ = 0 := by rw [mul_assoc, P.pY_inv_mul, mul_one, neg_add_cancel]

@[simp] lemma ofTwiceNeZero_a₃ [P.TwiceNeZero] : (W.ofTwiceNeZero P • W).a₃ = P.pY := by
    rw [ofTwiceNeZero_eq, mul_smul, variableChange_a₃, ofTwiceNeZero_aux]
    simp [-variableChange_a₃]

@[simp] lemma ofTwiceNeZero_a₂ [P.TwiceNeZero] : (W.ofTwiceNeZero P • W).a₂ = P.μ := by
    rw [ofTwiceNeZero_eq, mul_smul, variableChange_a₂, ofTwiceNeZero_aux, Point.μ]
    simp [-variableChange_a₂, -variableChange_a₁]

def toTateNF [P.TwiceNeZero] [P.ThriceNeZero] : VariableChange R where
  u := P.isUnit_pY.unit * P.μ_inv
  r := P.X
  s := -P.pX * P.pY_inv
  t := P.Y

def toTateNF_aux [P.TwiceNeZero] [P.ThriceNeZero] : VariableChange R where
  u := P.isUnit_pY.unit * P.μ_inv
  r := 0
  s := 0
  t := 0

lemma toTateNF_eq [P.TwiceNeZero] [P.ThriceNeZero] : W.toTateNF P =
    W.toTateNF_aux P * W.ofTwiceNeZero P :=
  by simp [toTateNF, toTateNF_aux, ofTwiceNeZero, VariableChange.mul_def]

lemma toTateNF_a₆ [P.TwiceNeZero] [P.ThriceNeZero] : (W.toTateNF P • W).a₆ = 0 := by
  rw [toTateNF_eq, mul_smul, variableChange_a₆, ofTwiceNeZero_a₆, ofTwiceNeZero_a₄]
  simp [toTateNF_aux]

lemma toTateNF_a₄ [P.TwiceNeZero] [P.ThriceNeZero] : (W.toTateNF P • W).a₄ = 0 := by
  rw [toTateNF_eq, mul_smul, variableChange_a₄, ofTwiceNeZero_a₄]
  simp [toTateNF_aux]

lemma toTateNF_a₂₃ [P.TwiceNeZero] [P.ThriceNeZero] :
    (W.toTateNF P • W).a₂ = (W.toTateNF P • W).a₃ := by
  rw [toTateNF_eq, mul_smul, variableChange_a₂, variableChange_a₃]
  simp [toTateNF_aux, -variableChange_a₃, -variableChange_a₂, -Units.val_inv_eq_inv_val]
  calc (P.μ * P.pY_inv) ^ 2 * P.μ
    = (P.μ * P.pY_inv) ^ 2 * P.μ * (P.pY * P.pY_inv) := by rw [P.pY_mul_inv, mul_one]
  _ = (P.μ * P.pY_inv) ^ 3 * P.pY := by ring_nf

instance [P.TwiceNeZero] [P.ThriceNeZero] : IsTateNF (W.toTateNF P • W) where
  a₂₃ := toTateNF_a₂₃ ..
  a₄  := toTateNF_a₄ ..
  a₆  := toTateNF_a₆ ..

end Affine

end WeierstrassCurve
