/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Group

/-!
# The universal elliptic curve
-/

noncomputable section

open scoped PolynomialPolynomial

namespace Polynomial /- move this -/

variable {R S} [CommSemiring R] [CommSemiring S]

lemma eval_C_X_comp_eval₂_map_C_X :
    (evalRingHom (C X : R[X][Y])).comp (eval₂RingHom (mapRingHom <| algebraMap R R[X][Y]) (C X)) =
    .id _ := by ext <;> simp

lemma eval_C_X_eval₂_map_C_X {p : R[X][Y]} :
    eval (C X) (eval₂ (mapRingHom <| algebraMap R R[X][Y]) (C X) p) = p :=
  congr($eval_C_X_comp_eval₂_map_C_X p)

lemma eval₂RingHom_eq_evalRingHom_comp_mapRingHom (f : R →+* S) (x y : S) :
    eval₂RingHom (eval₂RingHom f x) y =
      .comp (evalRingHom x) (.comp (evalRingHom <| C y) <| mapRingHom <| mapRingHom f) := by
  ext <;> simp

lemma eval₂RingHom_eval₂RingHom_apply (f : R →+* S) (x y : S) (p : R[X][Y]) :
    eval₂RingHom (eval₂RingHom f x) y p =
      ((p.map <| mapRingHom f).eval <| C y).eval x :=
  congr($(eval₂RingHom_eq_evalRingHom_comp_mapRingHom f x y) p)

end Polynomial

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

lemma algebraMap_field_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Field = polyToField.comp (algebraMap _ _) := rfl

lemma algebraMap_ring_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Ring = (AdjoinRoot.mk _).comp (algebraMap _ _) :=
  rfl

open Polynomial in
lemma equation_point : pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y) := by
  simp_rw [Affine.Equation, pointedCurve, baseChange, EllipticCurve.toAffine,
    algebraMap_field_eq_comp, ← map_map, Affine.map_polynomial_eval_C_eval, Affine.map_polynomial,
    eval_map, eval_C_X_eval₂_map_C_X, polyToField_polynomial]

open Polynomial Affine in
/-- The distinguished point on the universal pointed Weierstrass curve. -/
def point : curve⟮Universal.Field⟯ :=
  .some (EllipticCurve.Affine.nonsingular pointedCurve equation_point)

end Universal

open Universal
variable {R} [CommRing R] (W : WeierstrassCurve R)

/-- The specialization homomorphism from `ℤ[A₁, ⋯, A₆]`
to the ring of definition of the Weierstrass curve. -/
def specialize : MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom

/-- Every Weierstrass curve is a specialization of the universal Weierstrass curve. -/
lemma map_specialize : Universal.curve.map W.specialize = W := by simp [specialize, curve, map]

variable (x y : R)

open Polynomial (eval₂RingHom) in
/-- A point in the affine plane over `R` induces an evaluation homomorphism
from `ℤ[A₁, ⋯, A₆, X, Y]` to `R`. -/
def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y

variable {W x y} (h : Affine.Equation W x y)

open Polynomial in
/-- A point on a Weierstrass curve over `R` induces a specialization homomorphism
from the universal ring to `R`. -/
def ringEval : Universal.Ring →+* R :=
  AdjoinRoot.lift (eval₂RingHom W.specialize x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eq_evalRingHom_comp_mapRingHom, RingHom.comp_apply]
    rwa [coe_mapRingHom, ← Affine.map_polynomial, map_specialize]

lemma ringEval_mk (p : Poly) : ringEval h (AdjoinRoot.mk _ p) = W.polyEval x y p :=
  AdjoinRoot.lift_mk _ p

lemma ringEval_comp_mk : (ringEval h).comp (AdjoinRoot.mk _) = W.polyEval x y :=
  RingHom.ext (ringEval_mk h)

lemma polyEval_comp_eq_specialize : (W.polyEval x y).comp (algebraMap _ _) = W.specialize := by
  ext <;> simp [polyEval]

lemma ringEval_comp_eq_specialize : (ringEval h).comp (algebraMap _ _) = W.specialize := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]

end WeierstrassCurve
