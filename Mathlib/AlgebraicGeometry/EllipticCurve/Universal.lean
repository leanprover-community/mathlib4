/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Group

/-!
# The universal elliptic curve

This file defines the universal Weierstrass curve (`Universal.curve`) over the
polynomial ring `ℤ[A₁,A₂,A₃,A₄,A₆]`, and the universal pointed elliptic curve
(`Universal.pointedCurve`) over the field of fractions (`Universal.Field`) of the universal ring
`ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨P⟩ = Universal.Poly/⟨P⟩` (`Universal.Ring`, where `P` is the Weierstrass
polynomial) with distinguished point `(X,Y)`.

Given a Weierstrass curve `W` over a commutative ring `R`, we define the specialization
homomorphism `W.specialize : ℤ[A₁,A₂,A₃,A₄,A₆] →+* R`. If `(x,y)` is a point on the affine plane,
we define `W.polyEval x y : Universal.Poly →+* R`, which factors through
`W.ringEval x y : Universal.Ring →+* R` if `(x,y)` is on `W`.

We also introduce the cusp curve $Y^2 = X^3$, on which is the rational point $(1,1)$,
with the nice property that $ψₙ(1,1) = n$, making it easy to prove nonvanishing of
the universal $ψₙ$ when $n ≠ 0$ by specializing to the cusp curve, which shows that
`(X,Y)` is a point of infinite order on the universal pointed elliptic curve.
-/

noncomputable section

open scoped PolynomialPolynomial

namespace WeierstrassCurve

/-- A type whose elements represent the five coefficients `a₁`, `a₂`, `a₃`, `a₄` and `a₆`
of the Weierstrass polynomial. -/
inductive Coeff : Type | A₁ : Coeff | A₂ : Coeff | A₃ : Coeff | A₄ : Coeff | A₆ : Coeff

namespace Universal

open scoped Polynomial PolynomialPolynomial
open Coeff

open MvPolynomial (X) in
/-- The universal Weierstrass curve over the polynomial ring in five variables
(the **universal polynomial ring** for Weierstrass curves),
corresponding to the five coefficients of the Weierstrass polynomial. -/
def curve : Affine (MvPolynomial Coeff ℤ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }

lemma Δ_curve_ne_zero : curve.Δ ≠ 0 := fun h ↦ by
  simp_rw [Δ, b₂, b₄, b₆, b₈, curve] at h
  apply_fun MvPolynomial.eval (Coeff.rec 0 0 0 0 1) at h
  simp at h

/-- The polynomial ring over ℤ in the variables `A₁`, `A₂`, `A₃`, `A₄`, `A₆`, `X` and `Y`,
which is the polynomial ring in two variables over the universal polynomial ring. -/
abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]
/-- The universal ring for **pointed** Weierstrass curves. -/
protected abbrev Ring : Type := curve.CoordinateRing
/-- The universal field for pointed Weierstrass curves is
the field of fractions of the universal ring. -/
protected abbrev Field : Type := FractionRing Universal.Ring

instance : CommRing Poly := Polynomial.commRing /- why is this not automatic ... -/

lemma Poly.two_ne_zero : (2 : Poly) ≠ 0 :=
  Polynomial.C_ne_zero.mpr <| Polynomial.C_ne_zero.mpr fun h ↦ two_ne_zero' (α := ℤ) <|
    MvPolynomial.C_injective _ _ <| by rwa [← MvPolynomial.C_0] at h

/-- The obvious ring homomorphism from the polynomial ring in 7 variables to the universal field. -/
def polyToField : Poly →+* Universal.Field := (algebraMap Universal.Ring _).comp <| AdjoinRoot.mk _

lemma polyToField_apply (p : Poly) :
    polyToField p = algebraMap Universal.Ring _ (AdjoinRoot.mk _ p) := rfl

lemma algebraMap_field_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Field = polyToField.comp (algebraMap _ _) := rfl

lemma algebraMap_ring_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Ring = (AdjoinRoot.mk _).comp (algebraMap _ _) :=
  rfl

@[simp] lemma polyToField_polynomial : polyToField curve.polynomial = 0 := by
  rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]

lemma algebraMap_field_injective :
    Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Universal.Field) :=
  (IsFractionRing.injective Universal.Ring Universal.Field).comp
    (Affine.CoordinateRing.algebraMap_injective' _)

/-- The universal pointed Weierstrass curve is an elliptic curve
when base-changed to the the universal field. -/
def pointedCurve : EllipticCurve Universal.Field where
  __ := baseChange curve Universal.Field
  Δ' := .mk0 (baseChange curve Universal.Field).Δ <| by
    simpa only [map_Δ, map_ne_zero_iff _ algebraMap_field_injective] using Δ_curve_ne_zero
  coe_Δ' := rfl

open Polynomial in
lemma equation_point : pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y) := by
  simp_rw [Affine.Equation, pointedCurve, baseChange, EllipticCurve.toAffine,
    algebraMap_field_eq_comp, ← map_map, Affine.map_polynomial_eval_C_eval, Affine.map_polynomial,
    eval_map, eval_C_X_eval₂_map_C_X, polyToField_polynomial]

open Polynomial Affine in
/-- The distinguished point on the universal pointed Weierstrass curve. -/
def Affine.point : curve⟮Universal.Field⟯ :=
  .some (EllipticCurve.Affine.nonsingular pointedCurve equation_point)

/-- The distinguished point on the universal curve in Jacobian coordinates. -/
def Jacobian.point : Jacobian.Point (curve.baseChange Universal.Field) :=
  Jacobian.Point.fromAffine Affine.point

open Polynomial (CC)

@[simp] lemma pointedCurve_a₁ : pointedCurve.a₁ = polyToField (CC curve.a₁) := rfl
@[simp] lemma pointedCurve_a₂ : pointedCurve.a₂ = polyToField (CC curve.a₂) := rfl
@[simp] lemma pointedCurve_a₃ : pointedCurve.a₃ = polyToField (CC curve.a₃) := rfl
@[simp] lemma pointedCurve_a₄ : pointedCurve.a₄ = polyToField (CC curve.a₄) := rfl
@[simp] lemma pointedCurve_a₆ : pointedCurve.a₆ = polyToField (CC curve.a₆) := rfl

/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `ℤ[A₁,⋯,A₆,X,Y]`. -/
abbrev curvePoly : WeierstrassCurve Poly := curve.baseChange Poly
/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `ℤ[A₁,⋯,A₆,X,Y]/⟨P⟩`
(the universal ring), where `P` is the Weierstrass polynomial. -/
abbrev curveRing : WeierstrassCurve Universal.Ring := curve.baseChange Universal.Ring
/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `Frac(ℤ[A₁,⋯,A₆,X,Y]/⟨P⟩)`
(the universal field), where `P` is the Weierstrass polynomial. -/
abbrev curveField : WeierstrassCurve Universal.Field := curve.baseChange Universal.Field

lemma curveField_eq : curveField = pointedCurve.toWeierstrassCurve := rfl

end Universal

/-- The cusp curve $Y^2 = X^3$ over ℤ. -/
def cusp : Affine ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }

lemma cusp_equation_one_one : cusp.Equation 1 1 := by
  simp [Affine.Equation, Affine.polynomial, cusp]

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
/-- A point in the affine plane over `R` induces an evaluation homomorphism
from `ℤ[A₁, ⋯, A₆, X, Y]` to `R`. -/
def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y

open Polynomial in
lemma polyEval_apply (p : Poly) :
    polyEval W x y p = (p.map <| mapRingHom W.specialize).evalEval x y :=
  eval₂_eval₂RingHom_apply _ _ _ _

variable {W x y} (eqn : Affine.Equation W x y)

open Polynomial in
/-- A point on a Weierstrass curve over `R` induces a specialization homomorphism
from the universal ring to `R`. -/
def ringEval : Universal.Ring →+* R :=
  AdjoinRoot.lift (eval₂RingHom W.specialize x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eval₂RingHom, RingHom.comp_apply, coe_mapRingHom]
    rwa [← Affine.map_polynomial, map_specialize]

lemma ringEval_mk (p : Poly) : ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p :=
  AdjoinRoot.lift_mk _ p

lemma ringEval_comp_mk : (ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y :=
  RingHom.ext (ringEval_mk eqn)

lemma polyEval_comp_eq_specialize : (polyEval W x y).comp (algebraMap _ _) = W.specialize := by
  ext <;> simp [polyEval]

lemma ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap _ _) = W.specialize := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]

protected lemma Field.two_ne_zero : (2 : Universal.Field) ≠ 0 := by
  rw [← map_ofNat (algebraMap Universal.Ring _), map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  intro h; replace h := congr(ringEval cusp_equation_one_one $h)
  rw [map_ofNat, map_zero] at h; cases h

lemma curveRing_map_ringEval : curveRing.map (ringEval eqn) = W := by
  rw [curveRing, baseChange, map_map, ringEval_comp_eq_specialize, map_specialize]

end Universal

end WeierstrassCurve
