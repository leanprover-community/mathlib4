/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The universal elliptic curve

This file defines the universal Weierstrass curve (`Universal.curve`) over the
polynomial ring `ℤ[A₁,A₂,A₃,A₄,A₆]`, and the universal pointed elliptic curve
(`Universal.pointedCurve`) over the universal function field, the field of fractions
(`Universal.Field`) of the universal coordinate ring
`Universal.Ring = Universal.Poly/⟨P⟩ = ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨P⟩`
(where `P` is the Weierstrass polynomial) with distinguished point `(X,Y)`.

Given a Weierstrass curve `W` over a commutative ring `R`, we define the specialization
homomorphism `W.specialize : ℤ[A₁,A₂,A₃,A₄,A₆] →+* R`. If `(x,y)` is a point on the affine plane,
we define `W.polyEval x y : Universal.Poly →+* R`, which factors through
`W.ringEval x y : Universal.Ring →+* R` if `(x,y)` is on `W`.
-/

noncomputable section

@[expose] public section

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

/-- A type whose elements represent the five coefficients `a₁`, `a₂`, `a₃`, `a₄` and `a₆`
of the Weierstrass polynomial. -/
inductive Coeff : Type | A₁ : Coeff | A₂ : Coeff | A₃ : Coeff | A₄ : Coeff | A₆ : Coeff

namespace Universal

open scoped Polynomial
open Coeff

open MvPolynomial (X) in
/-- The universal Weierstrass curve over the universal ring for Weierstrass curves,
which is the polynomial ring in five variables that correspond to
the five coefficients of the Weierstrass polynomial. -/
def curve : WeierstrassCurve (MvPolynomial Coeff ℤ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }

lemma Δ_curve_ne_zero : curve.Δ ≠ 0 := fun h ↦ by
  simp_rw [Δ, b₂, b₄, b₆, b₈, curve] at h
  apply_fun MvPolynomial.eval (Coeff.rec 0 0 0 0 1) at h
  simp at h

/-- The polynomial ring over ℤ in the variables `A₁`, `A₂`, `A₃`, `A₄`, `A₆`, `X` and `Y`,
which is the polynomial ring in two variables over the universal polynomial ring. -/
abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]

/-- The universal coordinate ring, which is the universal ring for **pointed**
Weierstrass curves. -/
protected abbrev Ring : Type := Affine.CoordinateRing curve

/-- The universal function field is the field of fractions of the universal ring. -/
protected abbrev Field : Type := Affine.FunctionField curve

/-- The obvious ring homomorphism from the polynomial ring in 7 variables to the universal
function field. -/
def polyToField : Poly →+* Universal.Field := (algebraMap Universal.Ring _).comp <| AdjoinRoot.mk _

lemma polyToField_apply (p : Poly) :
    polyToField p = algebraMap Universal.Ring _ (AdjoinRoot.mk _ p) := rfl

lemma algebraMap_field_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Field = polyToField.comp (algebraMap ..) := rfl

lemma algebraMap_ring_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Ring = (AdjoinRoot.mk _).comp (algebraMap ..) :=
  rfl

@[simp] lemma polyToField_polynomial : polyToField (Affine.polynomial curve) = 0 := by
  rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]

lemma algebraMap_field_injective :
    Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Universal.Field) :=
  (IsFractionRing.injective Universal.Ring Universal.Field).comp
    (FaithfulSMul.algebraMap_injective ..)

/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `ℤ[A₁,⋯,A₆,X,Y]`. -/
abbrev curvePoly : WeierstrassCurve Poly := curve.baseChange Poly

/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `ℤ[A₁,⋯,A₆,X,Y]/⟨P⟩`
(the universal coordinate ring), where `P` is the Weierstrass polynomial. -/
abbrev curveRing : WeierstrassCurve Universal.Ring := curve.baseChange Universal.Ring

/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `Frac(ℤ[A₁,⋯,A₆,X,Y]/⟨P⟩)`
(the universal function field), where `P` is the Weierstrass polynomial. -/
abbrev curveField : WeierstrassCurve Universal.Field := curve.baseChange Universal.Field

instance : curveField.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr <| by
    simpa only [curveField, baseChange, map_Δ, map_ne_zero_iff _ algebraMap_field_injective]
      using Δ_curve_ne_zero

open Polynomial in
lemma equation_point : Affine.Equation curveField (polyToField (C X)) (polyToField Y) := by
  simp_rw [Affine.Equation, curveField, baseChange,
    algebraMap_field_eq_comp, ← map_map, Affine.map_polynomial, map_mapRingHom_evalEval,
    evalEval, eval_map, eval_C_X_eval₂_map_C_X, polyToField_polynomial]

open Polynomial Affine in
/-- The distinguished point on the universal pointed Weierstrass curve. -/
protected def Affine.point : Affine.Point curveField := .mk equation_point

/-- The distinguished point on the universal curve in Jacobian coordinates. -/
protected def Jacobian.point : Jacobian.Point curveField := .fromAffine Affine.point

open Polynomial (CC)

@[simp] lemma curveField_a₁ : curveField.a₁ = polyToField (CC curve.a₁) := rfl
@[simp] lemma curveField_a₂ : curveField.a₂ = polyToField (CC curve.a₂) := rfl
@[simp] lemma curveField_a₃ : curveField.a₃ = polyToField (CC curve.a₃) := rfl
@[simp] lemma curveField_a₄ : curveField.a₄ = polyToField (CC curve.a₄) := rfl
@[simp] lemma curveField_a₆ : curveField.a₆ = polyToField (CC curve.a₆) := rfl

end Universal

open Universal

variable {R} [CommRing R] (W : WeierstrassCurve R)

/-- The specialization homomorphism from `ℤ[A₁, ⋯, A₆]`
to the ring of definition of the Weierstrass curve. -/
def specialize : MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom

/-- Every Weierstrass curve is a specialization of the universal Weierstrass curve. -/
lemma map_specialize : Universal.curve.map W.specialize = W := by simp [specialize, curve, map]

namespace Universal

variable (x y : R)

open Polynomial (eval₂RingHom) in
/-- A point in the affine plane over `R` together with coefficients of a Weierstrass polynomial
over `R` induces an evaluation homomorphism
from `ℤ[A₁, ⋯, A₆, X, Y]` to `R`. -/
def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y

open Polynomial in
lemma polyEval_apply (p : Poly) :
    polyEval W x y p = (p.map <| mapRingHom W.specialize).evalEval x y :=
  eval₂_eval₂RingHom_apply ..

variable {W x y} (eqn : Affine.Equation W x y)

open Polynomial in
/-- A point on a Weierstrass curve over `R` induces a specialization homomorphism
from the universal coordinate ring to `R`. -/
def ringEval : Universal.Ring →+* R :=
  AdjoinRoot.lift (eval₂RingHom W.specialize x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eval₂RingHom, RingHom.comp_apply, coe_mapRingHom]
    rwa [← Affine.map_polynomial, Affine.map, map_specialize]

lemma ringEval_mk (p : Poly) : ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p :=
  AdjoinRoot.lift_mk _ p

lemma ringEval_comp_mk : (ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y :=
  RingHom.ext (ringEval_mk eqn)

lemma polyEval_comp_eq_specialize : (polyEval W x y).comp (algebraMap ..) = W.specialize := by
  ext <;> simp [polyEval]

lemma ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap ..) = W.specialize := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]

instance : CharZero Universal.Field := charZero_of_injective_algebraMap algebraMap_field_injective

lemma curveRing_map_ringEval : curveRing.map (ringEval eqn) = W := by
  rw [curveRing, baseChange, map_map, ringEval_comp_eq_specialize, map_specialize]

end Universal

end WeierstrassCurve
