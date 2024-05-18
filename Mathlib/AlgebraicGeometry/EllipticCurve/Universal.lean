/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Group

/-!
# The universal elliptic curve
-/


namespace Polynomial /- move this -/

noncomputable section

variable {R} [CommSemiring R]

lemma eval_C_X_comp_eval₂_map_C_X :
    (evalRingHom (C X : R[X][X])).comp (eval₂RingHom (mapRingHom <| algebraMap R R[X][X]) (C X)) =
    .id _ := by ext <;> simp

lemma eval_C_X_eval₂_map_C_X {p : R[X][X]} :
    eval (C X) (eval₂ (mapRingHom <| algebraMap R R[X][X]) (C X) p) = p :=
  congr($eval_C_X_comp_eval₂_map_C_X p)

end

end Polynomial

namespace WeierstrassCurve.Universal

/-- The coefficients of the Weierstrass polynomial are `A₁`, `A₂`, `A₃`, `A₄`, and `A₆`. -/
inductive Coeff : Type | A₁ : Coeff | A₂ : Coeff | A₃ : Coeff | A₄ : Coeff | A₆ : Coeff

open scoped Polynomial
open Coeff

noncomputable section

open MvPolynomial (X) in
def curve : Affine (MvPolynomial Coeff ℤ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }

lemma Δ_curve_ne_zero : curve.Δ ≠ 0 := fun h ↦ by
  simp_rw [Δ, b₂, b₄, b₆, b₈, curve] at h
  apply_fun MvPolynomial.eval (Coeff.rec 0 0 0 0 1) at h
  simp at h

abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][X]
protected abbrev Ring : Type := curve.CoordinateRing
protected abbrev Field : Type := FractionRing Universal.Ring

instance : CommRing Poly := Polynomial.commRing /- why is this not automatic ... -/

def polyToField : Poly →+* Universal.Field := (algebraMap Universal.Ring _).comp <| AdjoinRoot.mk _

lemma algebraMap_injective :
    Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Universal.Field) :=
  (IsFractionRing.injective Universal.Ring Universal.Field).comp
    (Affine.CoordinateRing.algebraMap_injective' _)

def ellipticCurve : EllipticCurve Universal.Field where
  __ := baseChange curve Universal.Field
  Δ' := .mk0 (baseChange curve Universal.Field).Δ <| by
    simpa only [map_Δ, map_ne_zero_iff _ algebraMap_injective] using Δ_curve_ne_zero
  coe_Δ' := rfl

lemma algebraMap_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Field = polyToField.comp (algebraMap _ _) := rfl

open Polynomial in
lemma equation_point : ellipticCurve.toAffine.Equation (polyToField (C X)) (polyToField X) := by
  simp_rw [Affine.Equation, ellipticCurve, baseChange, EllipticCurve.toAffine, algebraMap_eq_comp,
    ← map_map, Affine.map_polynomial_eval_C_eval, Affine.map_polynomial, eval_map,
    eval_C_X_eval₂_map_C_X, polyToField, RingHom.comp_apply, AdjoinRoot.mk_self, map_zero]

open Polynomial in
def point : curve⟮Universal.Field⟯ :=
  .some (EllipticCurve.Affine.nonsingular ellipticCurve equation_point)

end

end WeierstrassCurve.Universal
