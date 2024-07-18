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
(`Universal.pointedCurve`) over the field of fractions (`Universal.Field`) of
`Universal.Ring = Universal.Poly/⟨P⟩ = ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨P⟩` (where `P` is the Weierstrass
polynomial) with distinguished point `(X,Y)`.

Given a Weierstrass curve `W` over a commutative ring `R`, we define the specialization
homomorphism `W.specialize : ℤ[A₁,A₂,A₃,A₄,A₆] →+* R`. If `(x,y)` is a point on the affine plane,
we define `W.polyEval x y : Universal.Poly →+* R`, which factors through
`W.ringEval x y : Universal.Ring →+* R` if `(x,y)` is on `W`.

We also introduce the cusp curve `Y² = X³`, on which lies the rational point `(1,1)`, with
the nice property that `ψₙ(1,1) = n`, making it easy to prove nonvanishing of the universal `ψₙ`
when `n ≠ 0` by specializing to the cusp curve, which shows that `(X,Y)` is a point of infinite
order on the universal pointed elliptic curve.
-/

noncomputable section

open scoped PolynomialPolynomial

namespace WeierstrassCurve

/-- A type whose elements represent the five coefficients `a₁`, `a₂`, `a₃`, `a₄` and `a₆`
of the Weierstrass polynomial. -/
inductive Coeff : Type | A₁ : Coeff | A₂ : Coeff | A₃ : Coeff | A₄ : Coeff | A₆ : Coeff

namespace Universal

open scoped Polynomial PolynomialPolynomial
open Coeff Affine

open MvPolynomial (X) in
/-- The universal Weierstrass curve over the polynomial ring in five variables
(the universal polynomial ring for Weierstrass curves),
corresponding to the five coefficients of the Weierstrass polynomial. -/
def curve : WeierstrassCurve (MvPolynomial Coeff ℤ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }

lemma Δ_curve_ne_zero : curve.Δ ≠ 0 := fun h ↦ by
  simp_rw [Δ, b₂, b₄, b₆, b₈, curve] at h
  apply_fun MvPolynomial.eval (Coeff.rec 0 0 0 0 1) at h
  simp at h

/-- The polynomial ring over ℤ in the variables `A₁`, `A₂`, `A₃`, `A₄`, `A₆`, `X` and `Y`,
which is the polynomial ring in two variables over the universal polynomial ring. -/
abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]
/-- The universal ring for **pointed** Weierstrass curves. -/
protected abbrev Ring : Type := CoordinateRing curve
/-- The universal field for pointed Weierstrass curves is
the field of fractions of the universal ring. -/
protected abbrev Field : Type := FunctionField curve

--instance : CommRing Poly := Polynomial.commRing /- why is this not automatic ... -/

lemma Field.two_ne_zero : (2 : Universal.Field) ≠ 0 := by
  rw [← map_ofNat (algebraMap (MvPolynomial Coeff ℤ) _), map_ne_zero_iff]
  exacts [two_ne_zero' _, FunctionField.algebraMap_injective' _]

/-- The universal pointed elliptic curve over the field of fractions of the universal ring. -/
def pointedCurve : EllipticCurve Universal.Field :=
  FunctionField.curve curve (mem_nonZeroDivisors_of_ne_zero Δ_curve_ne_zero)

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

open Universal
variable (R) [CommRing R] (W : WeierstrassCurve R)

/-- The cusp curve $Y^2 = X^3$ over a commutative ring. -/
def cusp : WeierstrassCurve R := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }

lemma cusp_equation_one_one : Affine.Equation (cusp R) 1 1 := by
  simp [Affine.Equation, Affine.polynomial, cusp, Polynomial.evalEval]

variable {R}

/-- The specialization homomorphism from `ℤ[A₁, ⋯, A₆]`
to the ring of definition of the Weierstrass curve. -/
def specialize : MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom

/-- Every Weierstrass curve is a specialization of the universal Weierstrass curve. -/
lemma map_specialize : Universal.curve.map W.specialize = W := by simp [specialize, curve, map]

namespace Universal

variable (x y : R)

open Polynomial in
/-- A point in the affine plane over `R` induces an evaluation homomorphism
from `ℤ[A₁, ⋯, A₆, X, Y]` to `R`. -/
@[simps!] def polyEval : Poly →+* R :=
  (evalEvalRingHom x y).comp (mapRingHom <| mapRingHom W.specialize)

open Affine
variable {W x y} (eqn : Equation W x y)

open Polynomial in
/-- A point on a Weierstrass curve over `R` induces a specialization homomorphism
from the universal ring to `R`. -/
def ringEval : Universal.Ring →+* R :=
  (CoordinateRing.eval <| W.map_specialize ▸ eqn).comp (CoordinateRing.map curve W.specialize)

open CoordinateRing in
lemma ringEval_comp_mk : (ringEval eqn).comp (CoordinateRing.mk _) = polyEval W x y := by
  rw [ringEval, RingHom.comp_assoc, map_comp_mk, ← RingHom.comp_assoc, eval_comp_mk, polyEval]

lemma ringEval_mk (p : Poly) : ringEval eqn (CoordinateRing.mk _ p) = polyEval W x y p :=
  congr($(ringEval_comp_mk eqn) p)

lemma polyEval_comp_eq_specialize : (polyEval W x y).comp (algebraMap _ _) = W.specialize := by
  ext <;> simp [polyEval]

lemma ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap _ _) = W.specialize := by
  rwa [ringEval, ← CoordinateRing.mk_comp_algebraMap, ← RingHom.comp_assoc, ← ringEval,
    ringEval_comp_mk, polyEval_comp_eq_specialize]

lemma curveRing_map_ringEval : curveRing.map (ringEval eqn) = W := by
  rw [curveRing, baseChange, map_map, ringEval_comp_eq_specialize, map_specialize]

end Universal

end WeierstrassCurve
