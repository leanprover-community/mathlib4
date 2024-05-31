/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Junyan Xu
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Universal
import Mathlib.Data.Int.Parity
import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Division polynomials for elliptic curves

This file defines division polynomials for elliptic curves and show they give a formula for
scalar multiplication on the group of rational points in Jacobian coordinates.

-/

open scoped PolynomialPolynomial

namespace Polynomial -- move this to Affine?

variable {R : Type*}

noncomputable section

/-- `evalEval x y p` is the evaluation `p(x,y)` of a two-variable polynomial `p : R[X][Y]`. -/
abbrev evalEval [Semiring R] (x y : R) (p : R[X][Y]) : R := eval x (eval (C y) p)

/-- `evalEval x y` as a ring homomorphism. -/
@[simps!] abbrev evalEvalRingHom [CommSemiring R] (x y : R) : R[X][Y] →+* R :=
  (evalRingHom x).comp (evalRingHom <| C y)

/-- A constant viewed as a polynomial in two variables. -/
abbrev CC [Semiring R] (r : R) : R[X][Y] := C (C r)

lemma coe_algebraMap_eq_CC [CommSemiring R] : algebraMap R R[X][Y] = CC (R := R) := rfl
lemma coe_evalEvalRingHom [CommSemiring R] (x y : R) : evalEvalRingHom x y = evalEval x y := rfl

end

end Polynomial

namespace WeierstrassCurve

open Polynomial

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)

noncomputable section

/-- The second division polynomial is simply the derivative of the Weierstrass polynomial
with respect to `Y`. -/
protected abbrev ψ₂ : R[X][Y] := Affine.polynomialY W
/- Implementation note: protect to force the use of dot notation,
   since ψ etc. are common variable names. -/

/-- A single variable polynomial congruent to the square of the second division polynomial
modulo the Weierstrass polynomial. -/
protected def ψ₂Sq : R[X] := 4 * X ^ 3 + C W.b₂ * X ^ 2 + 2 * C W.b₄ * X + C W.b₆

/-- The third division polynomial, in a single variable. -/
protected def ψ₃ : R[X] := 3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈

/-- The complement of the second division polynomial in the fourth, in a single variable. -/
protected def ψc₂ : R[X] := 2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3
  + 10 * C W.b₈ * X ^ 2 + C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)

/-- The "invariant" that is equal to the quotient
`(ψ(n-1)²ψ(n+2)+ψ(n-2)ψ(n+1)²+ψ₂²ψ(n)³)/ψ(n+1)ψ(n)ψ(n-1)` for arbitary `n`
modulo the Weierstrass polynomial. -/
def invar : R[X] := 6 * X ^ 2 + C W.b₂ * X + C W.b₄

/-- The `ψ` family of division polynomials is the normalised EDS given by the initial values
ψ₂, ψ₃, and ψc₂. `ψ n` gives the last (`Z`) coordinate in Jacobian coordinates of the scalar
multiplication by the integer `n` of a point on a Weierstrass curve. -/
protected def ψ : ℤ → R[X][Y] := normEDS W.ψ₂ (C W.ψ₃) (C W.ψc₂)

/-- The `φ` family of division polynomials; `φ n` gives the first (`X`) coordinate in
Jacobian coordinates of the scalar multiplication by `n`. -/
protected def φ (n : ℤ) : R[X][Y] := C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)

/-- The complement of ψ(n) in ψ(2n). -/
def ψc : ℤ → R[X][Y] := compl₂EDS W.ψ₂ (C W.ψ₃) (C W.ψc₂)

lemma isEllSequence_ψ : IsEllSequence W.ψ := IsEllSequence.normEDS

open Affine (polynomial polynomialX polynomialY negPolynomial)
open EllSequence

open WeierstrassCurve (ψc₂ ψ₂ ψ₂Sq ψ₃ ψ φ ψc)

lemma C_ψ₃_eq :
    C W.ψ₃ = (3 * C X + CC W.a₂) * C W.ψ₂Sq - polynomialX W ^ 2
      + CC W.a₁ * W.ψ₂ * polynomialX W - CC W.a₁ ^ 2 * polynomial W := by
  simp_rw [ψ₃, ψ₂Sq, polynomial, polynomialX, polynomialY, b₂, b₄, b₆, b₈, CC]; C_simp; ring

lemma ψ₂_sq : W.ψ₂ ^ 2 = C W.ψ₂Sq + 4 * polynomial W := by
  rw [Affine.polynomial, ψ₂, polynomialY, ψ₂Sq, b₂, b₄, b₆]; C_simp; ring

lemma ψc₂_add_ψ₂Sq_sq : W.ψc₂ + W.ψ₂Sq ^ 2 = W.invar * W.ψ₃ := by
  rw [ψc₂, ψ₂Sq, invar, ψ₃]
  linear_combination (norm := (C_simp; ring_nf)) congr(C $W.b_relation) * (@X R _) ^ 2

lemma ψc₂_add_ψ₂_pow_four :
    C W.ψc₂ + W.ψ₂ ^ 4 = C (W.invar * W.ψ₃) + 8 * polynomial W * (2 * polynomial W + C W.ψ₂Sq) := by
  simp_rw [show 4 = 2 * 2 by rfl, pow_mul, ψ₂_sq, add_sq,
    ← add_assoc, ← C_pow, ← C_add, ψc₂_add_ψ₂Sq_sq]; C_simp; ring

lemma φ_mul_ψ (n : ℤ) : W.φ n * W.ψ n = C X * W.ψ n ^ 3 - invarDenom W.ψ 1 n := by
  rw [φ, invarDenom]; ring

suppress_compilation in
/-- The `ω` family of division polynomials: `ω n` gives the second (`Y`) coordinate in
Jacobian coordinates of the scalar multiplication by `n`. -/
protected def ω (n : ℤ) : R[X][Y] :=
  redInvarDenom W.ψ₂ (C W.ψ₃) (C W.ψc₂) n *
    ((CC W.a₁ * polynomialY W - polynomialX W) * C W.ψ₃
      + 4 * polynomial W * (2 * polynomial W + C W.ψ₂Sq))
  - compl₂EDSAux W.ψ₂ (C W.ψ₃) (C W.ψc₂) n + negPolynomial W * W.ψ n ^ 3

open WeierstrassCurve (ω)
lemma ω_spec (n : ℤ) :
    2 * W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = W.ψc n := by
  rw [ψc, compl₂EDS_eq_redInvarNum_sub, redInvar_normEDS, ψc₂_add_ψ₂_pow_four, mul_assoc (C _),
    φ_mul_ψ, ψ, invarDenom_eq_redInvarDenom_mul, ω, ← ψ, invar, b₂, b₄, ψ₂,
    polynomialY, polynomialX, negPolynomial]
  C_simp; ring

lemma two_mul_ω (n : ℤ) :
    2 * W.ω n = W.ψc n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 := by
  rw [← ω_spec]; abel

lemma ψc_spec (n : ℤ) : W.ψ n * W.ψc n = W.ψ (2 * n) := normEDS_mul_compl₂EDS _ _ _ _

@[simp] lemma ψ_zero : W.ψ 0 = 0 := by simp [ψ]
@[simp] lemma ψ_one : W.ψ 1 = 1 := by simp [ψ]
@[simp] lemma ψ_two : W.ψ 2 = W.ψ₂ := by simp [ψ]
@[simp] lemma ψ_three : W.ψ 3 = C W.ψ₃ := by simp [ψ]
@[simp] lemma ψ_four : W.ψ 4 = C W.ψc₂ * W.ψ₂ := by simp [ψ]
@[simp] lemma φ_zero : W.φ 0 = 1 := by simp [φ, ψ]
@[simp] lemma φ_one : W.φ 1 = C X := by simp [φ, ψ]
@[simp] lemma φ_two : W.φ 2 = C X * W.ψ₂ ^ 2 - C W.ψ₃ := by simp [φ]
@[simp] lemma ω_zero : W.ω 0 = 1 := by simp [ω]
@[simp] lemma ω_one : W.ω 1 = Y := by simp [ω, ← Affine.Y_sub_polynomialY]

@[simp] lemma ψ_neg (n : ℤ) : W.ψ (-n) = -W.ψ n := by simp [ψ]
@[simp] lemma ψc_neg (n : ℤ) : W.ψc (-n) = W.ψc n := by simp [ψc]

@[simp] lemma φ_neg (n : ℤ) : W.φ (-n) = W.φ n := by
  rw [φ, φ, neg_add_eq_sub, ← neg_sub n, ← neg_add', ψ_neg, ψ_neg, ψ_neg]; ring

@[simp] lemma map_ψ₂ : (W.map f).ψ₂ = W.ψ₂.map (mapRingHom f) := by simp [ψ₂, polynomialY]
@[simp] lemma map_ψ₃ : (W.map f).ψ₃ = W.ψ₃.map f := by simp [ψ₃]
@[simp] lemma map_ψc₂ : (W.map f).ψc₂ = W.ψc₂.map f := by simp [ψc₂]
@[simp] lemma map_ψ₂Sq : (W.map f).ψ₂Sq = W.ψ₂Sq.map f := by simp [ψ₂Sq]

@[simp] lemma map_ψ (n : ℤ) : (W.map f).ψ n = (W.ψ n).map (mapRingHom f) := by
  simp_rw [ψ, ← coe_mapRingHom, map_normEDS]; simp

@[simp] lemma map_φ (n : ℤ) : (W.map f).φ n = (W.φ n).map (mapRingHom f) := by simp [φ]

open Affine in
@[simp] lemma map_ω (n : ℤ) : (W.map f).ω n = (W.ω n).map (mapRingHom f) := by
  simp_rw [ω, ← coe_mapRingHom, map_add, map_sub, map_mul, map_redInvarDenom, map_compl₂EDSAux,
    map_polynomial, map_polynomialX, map_polynomialY, map_negPolynomial]; simp

private lemma universal_ω_neg (n : ℤ) : letI W := Universal.curve
    W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 := by
  rw [← mul_cancel_left_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero Universal.Poly.two_ne_zero)]
  simp_rw [left_distrib, two_mul_ω, ψc_neg, ψ_neg, φ_neg]; ring

lemma ω_neg (n : ℤ) : W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 := by
  rw [← W.map_specialize, map_ω, universal_ω_neg]; simp

variable {x y : R}

namespace Universal

lemma evalEval_ψ₂ : W.ψ₂.evalEval x y = W.polyEval x y curve.ψ₂ := by
  simp_rw [polyEval, eval₂RingHom_eval₂RingHom_apply, ← map_ψ₂, map_specialize]

lemma evalEval_ψ₃ : (C W.ψ₃).evalEval x y = W.polyEval x y (C curve.ψ₃) := by
  simp_rw [polyEval, eval₂RingHom_eval₂RingHom_apply,
    map_C, coe_mapRingHom, ← map_ψ₃, map_specialize]

lemma evalEval_ψc₂ : (C W.ψc₂).evalEval x y = W.polyEval x y (C curve.ψc₂) := by
  simp_rw [polyEval, eval₂RingHom_eval₂RingHom_apply,
    map_C, coe_mapRingHom, ← map_ψc₂, map_specialize]

variable {m n : ℤ}

lemma evalEval_ψ : (W.ψ n).evalEval x y = W.polyEval x y (curve.ψ n) := by
  simp_rw [polyEval, eval₂RingHom_eval₂RingHom_apply, ← map_ψ, map_specialize]

lemma evalEval_φ : (W.φ n).evalEval x y = W.polyEval x y (curve.φ n) := by
  simp_rw [polyEval, eval₂RingHom_eval₂RingHom_apply, ← map_φ, map_specialize]

lemma evalEval_ω : (W.ω n).evalEval x y = W.polyEval x y (curve.ω n) := by
  simp_rw [polyEval, eval₂RingHom_eval₂RingHom_apply, ← map_ω, map_specialize]

@[simp] lemma pointedCurve_a₁ : pointedCurve.a₁ = polyToField (CC curve.a₁) := rfl
@[simp] lemma pointedCurve_a₂ : pointedCurve.a₂ = polyToField (CC curve.a₂) := rfl
@[simp] lemma pointedCurve_a₃ : pointedCurve.a₃ = polyToField (CC curve.a₃) := rfl
@[simp] lemma pointedCurve_a₄ : pointedCurve.a₄ = polyToField (CC curve.a₄) := rfl
@[simp] lemma pointedCurve_a₆ : pointedCurve.a₆ = polyToField (CC curve.a₆) := rfl

/-- The cusp curve $Y^2 = X^3$ over ℤ. -/
def cusp : Affine ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }

lemma cusp_equation_one_one : cusp.Equation 1 1 := by simp [Affine.Equation, polynomial, cusp]
lemma cusp_ψ₂ : cusp.ψ₂ = 2 * Y := by simp [cusp, ψ₂, polynomialY]
lemma cusp_ψ₃ : cusp.ψ₃ = 3 * X ^ 4 := by simp [cusp, ψ₃, b₂, b₄, b₆, b₈]
lemma cusp_ψc₂ : cusp.ψc₂ = 2 * X ^ 6 := by simp [cusp, ψc₂, b₂, b₄, b₆, b₈]

lemma polyEval_cusp_ψ : cusp.polyEval 1 1 (curve.ψ n) = n := by
  rw [ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_ψ₃, ← evalEval_ψc₂, cusp_ψ₂, cusp_ψ₃, cusp_ψc₂]
  simp [evalEval, normEDS_two_three_two]

lemma polyEval_cusp_φ : cusp.polyEval 1 1 (curve.φ n) = 1 := by
  simp_rw [φ, map_sub, map_mul, map_pow, polyEval_cusp_ψ, polyEval]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X]; ring

lemma polyEval_cusp_ψc : cusp.polyEval 1 1 (curve.ψc n) = 2 := by
  rw [ψc, map_compl₂EDS, ← evalEval_ψ₂, ← evalEval_ψ₃, ← evalEval_ψc₂, cusp_ψ₂, cusp_ψ₃, cusp_ψc₂]
  simp [evalEval, compl₂EDS_two_three_two]

lemma polyEval_cusp_ω : cusp.polyEval 1 1 (curve.ω n) = 1 := by
  have := congr(cusp.polyEval 1 1 $(curve.two_mul_ω n))
  simp_rw [map_sub, map_mul, map_ofNat, polyEval_cusp_ψc] at this
  simpa [cusp, polyEval, specialize, curve] using this

protected lemma Field.two_ne_zero : (2 : Universal.Field) ≠ 0 := by
  rw [← map_ofNat (algebraMap Universal.Ring _), map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  intro h; replace h := congr(cusp.ringEval cusp_equation_one_one $h)
  rw [map_ofNat, map_zero] at h; cases h

/-- The `ψ` family of division polynomials as elements in the universal field. -/
abbrev ψᵤ (n : ℤ) : Universal.Field := polyToField (curve.ψ n)

lemma ψᵤ_eq_normEDS :
    ψᵤ = normEDS
      (polyToField curve.ψ₂) (polyToField <| C curve.ψ₃) (polyToField <| C curve.ψc₂) := by
  ext; rw [← map_normEDS]; rfl

lemma isEllSequence_ψᵤ : IsEllSequence ψᵤ := by rw [ψᵤ_eq_normEDS]; exact IsEllSequence.normEDS
lemma net_ψᵤ (p q r s) : net ψᵤ p q r s = 0 := by rw [ψᵤ_eq_normEDS]; apply net_normEDS

lemma ψᵤ_ne_zero (h0 : n ≠ 0) : ψᵤ n ≠ 0 := fun h ↦ by
  rw [ψᵤ, polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(cusp.ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_ψ, map_zero] at h
  exact h0 h

lemma polyToField_φ_ne_zero : polyToField (curve.φ n) ≠ 0 := fun h ↦ by
  rw [polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(cusp.ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_φ, map_zero] at h
  exact one_ne_zero h

lemma polyToField_ψ₂Sq : polyToField (C curve.ψ₂Sq) = ψᵤ 2 ^ 2 := by
  rw [← map_pow, ψ_two, ψ₂_sq, map_add, map_mul, polyToField_polynomial, mul_zero, add_zero]

namespace Affine

variable (n)
/-- The rational function φₙ/ψₙ², which we will show to be the `X`-coordinate
of the point `n • (X, Y)` on the universal curve. -/
def smulX : Universal.Field := polyToField (curve.φ n) / (ψᵤ n) ^ 2

/-- The rational function ωₙ/ψₙ³, which we will show to be the `Y`-coordinate
of the point `n • (X, Y)` on the universal curve. -/
def smulY : Universal.Field := polyToField (curve.ω n) / (ψᵤ n) ^ 3
variable {n}

@[simp] lemma smulX_zero : smulX 0 = 0 := by simp [smulX, ψᵤ]
@[simp] lemma smulY_zero : smulY 0 = 0 := by simp [smulY, ψᵤ]
@[simp] lemma smulX_one : smulX 1 = polyToField (C X) := by simp [smulX, ψᵤ]
@[simp] lemma smulY_one : smulY 1 = polyToField Y := by simp [smulY, ψᵤ]

lemma smulX_eq (hn : n ≠ 0) :
    smulX n = smulX 1 - ψᵤ (n + 1) * ψᵤ (n - 1) / (ψᵤ n) ^ 2 := by
  rw [smulX, smulX_one, φ, map_sub, sub_div, map_mul, map_pow, mul_div_cancel_right₀, map_mul]
  exact pow_ne_zero _ (ψᵤ_ne_zero hn)

lemma smulX_two : smulX 2 = smulX 1 - ψᵤ 3 / (ψᵤ 2) ^ 2 := by
  simp [smulX_eq two_ne_zero, ψᵤ]

lemma smulX_sub_smulX (hm : m ≠ 0) (hn : n ≠ 0) :
    smulX m - smulX n = (ψᵤ (n + m) * ψᵤ (n - m)) / (ψᵤ n * ψᵤ m) ^ 2 := by
  rw [smulX_eq hm, smulX_eq hn, sub_sub_sub_cancel_left, div_sub_div]
  · rw [mul_pow]; congr; convert (isEllSequence_ψᵤ n m 1).symm using 1
    · ring
    · simp [ψᵤ]
  all_goals exact pow_ne_zero _ (ψᵤ_ne_zero <| by assumption)

lemma smulX_sub_sub_smulX_add (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulX (n - m) - smulX (n + m) = (ψᵤ (2 * n) * ψᵤ (2 * m)) / (ψᵤ (n + m) * ψᵤ (n - m)) ^ 2 := by
  rw [smulX_sub_smulX sub_ne add_ne]; ring_nf

lemma smulX_neg : smulX (-n) = smulX n := by simp_rw [smulX, φ_neg, ψᵤ, ψ_neg, ← map_pow, neg_sq]

lemma smulX_ne_zero (h0 : n ≠ 0) : smulX n ≠ 0 :=
  div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| ψᵤ_ne_zero h0)

lemma smulX_ne_smulX (ne : m ≠ n) (ne_neg : m ≠ -n) : smulX m ≠ smulX n := by
  obtain rfl | hm := eq_or_ne m 0
  · rw [smulX_zero]; exact (smulX_ne_zero ne.symm).symm
  obtain rfl | hn := eq_or_ne n 0
  · rw [smulX_zero]; exact smulX_ne_zero ne
  rw [← sub_ne_zero, smulX_sub_smulX hm hn]
  rw [ne_comm, ← sub_ne_zero] at ne
  rw [Ne, ← add_eq_zero_iff_eq_neg, add_comm] at ne_neg
  refine div_ne_zero (mul_ne_zero ?_ ?_) (pow_ne_zero _ <| mul_ne_zero ?_ ?_) <;>
    apply ψᵤ_ne_zero <;> assumption

lemma smulX_eq_smulX_iff : smulX m = smulX n ↔ m = n ∨ m = -n := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · contrapose! h; exact smulX_ne_smulX h.1 h.2
  · rintro (rfl|rfl); exacts [rfl, smulX_neg]

private lemma smulY_sub_negY_aux {F} [Field F] {a₁ a₃ x y z : F} (h0 : z ≠ 0) :
    y / z ^ 3 - (-(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃) =
      z * (2 * y + a₁ * x * z + a₃ * z ^ 3) / z ^ 4 := by
  field_simp; ring

lemma smulY_sub_negY (h0 : n ≠ 0) :
    smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n) = ψᵤ (2 * n) / (ψᵤ n) ^ 4 := by
  simp_rw [Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, smulY, ψᵤ, ← ψc_spec, ← ω_spec,
    map_mul, map_add, map_mul, map_pow, map_ofNat]
  exact smulY_sub_negY_aux (ψᵤ_ne_zero h0)

lemma smulY_one_sub_negY :
    smulY 1 - pointedCurve.toAffine.negY (smulX 1) (smulY 1) = ψᵤ 2 := by
  rw [smulY_sub_negY one_ne_zero, mul_one, ψᵤ, ψᵤ, ψ_one, map_one, one_pow, div_one]

lemma smulY_one_ne_negY : smulY 1 ≠ pointedCurve.toAffine.negY (smulX 1) (smulY 1) := by
  rw [← sub_ne_zero, smulY_one_sub_negY]; exact ψᵤ_ne_zero two_ne_zero

/-- The slope of the tangent line at the point (X,Y) on the universal curve. -/
def slopeOne : Universal.Field :=
  pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)

lemma slopeOne_eq_neg_div :
    slopeOne = -polyToField curve.polynomialX / ψᵤ 2 := by
  rw [slopeOne, Affine.slope_of_Yne rfl smulY_one_ne_negY, smulY_one_sub_negY, polynomialX]
  congr; simp

private lemma addX_smul_one_smul_one_aux {F} [Field F] {a₁ a₂ x dx dy : F} (h0 : dy ≠ 0) :
  (-dx / dy) ^ 2 + a₁ * (-dx / dy) - a₂ - x - x - x =
    (dx ^ 2 - a₁ * dx * dy - (3 * x + a₂) * dy ^ 2) / dy ^ 2 := by
  -- extracted lemma to make field_simp faster
  field_simp; ring

lemma addX_smul_one_smul_one :
    pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2 := .symm <| by
  rw [smulX_two, Affine.addX, sub_eq_neg_add, ← eq_sub_iff_add_eq, ← neg_div _ (polyToField _),
    slopeOne_eq_neg_div, addX_smul_one_smul_one_aux (ψᵤ_ne_zero two_ne_zero)]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, polyToField_ψ₂Sq, ψᵤ,
    ψ_two, ψ_three, C_ψ₃_eq, polyToField_polynomial, pointedCurve_a₁, pointedCurve_a₂, smulX_one]
  ring

private lemma addY_smul_one_smul_one_aux {F} [Field F] {a₁ a₃ dx dy x y ψ₃ t : F} (h0 : dy ≠ 0) :
    ((a₁ * dy - dx) * ψ₃ + 0 * t + (-y - (a₁ * x + a₃)) * dy ^ 3) / dy ^ 3 =
      -(-dx / dy * (x - ψ₃ / dy ^ 2 - x) + y) - a₁ * (x - ψ₃ / dy ^ 2) - a₃ := by
  field_simp; ring

lemma addY_smul_one_smul_one :
    pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2 := .symm <| by
  rw [smulY, ω, redInvarDenom_two, one_mul, compl₂EDSAux_two, sub_zero, Affine.addY, Affine.addY',
    addX_smul_one_smul_one, smulX_two, Affine.negY, negPolynomial, slopeOne_eq_neg_div,
    ← ψ₂, ← ψ_two, smulX_one, smulY_one, ψᵤ, ψᵤ, ψ_three]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, polyToField_polynomial, mul_zero]
  exact addY_smul_one_smul_one_aux (ψᵤ_ne_zero two_ne_zero)

private lemma smulY_neg_aux {F} [Field F] {a₁ a₃ x y z : F} (hz : z ≠ 0) :
    (y + a₁ * x * z + a₃ * z ^ 3) / (-z) ^ 3 = -(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃ := by
  rw [neg_pow]; field_simp; ring

lemma smulY_neg (h0 : n ≠ 0) :
    smulY (-n) = pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  simp only [Affine.negY, smulX, smulY, ψ_neg, ω_neg, map_add, map_neg, map_mul, map_pow, ψᵤ]
  exact smulY_neg_aux (ψᵤ_ne_zero h0)

private lemma smulX_add_aux {F} [Field F] {m n m₂ n₂ a s : F}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    n₂ / n ^ 4 * (m₂ / m ^ 4) / (a * s / (n * m) ^ 2) ^ 2 = n₂ * m₂ / (a * s) ^ 2 := by
  field_simp; ring

lemma smulX_add (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    smulX (n + m) = smulX (n - m) -
      ψ₂ (smulX n) (smulY n) * ψ₂ (smulX m) (smulY m) / (smulX m - smulX n) ^ 2 := by
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', smulX_sub_sub_smulX_add add_ne sub_ne]
  simp_rw [smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hm hn]
  apply smulX_add_aux <;> apply ψᵤ_ne_zero <;> assumption

private lemma smulY_add_sub_negY_aux {F} [Field F] {m n m₂ n₂ a s am an : F}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    (m₂ / m ^ 4 * (an * m / (a * n) ^ 2) - n₂ / n ^ 4 * (am * n / (a * m) ^ 2))
      / (a * s / (n * m) ^ 2)
      = (an * m₂ * n - am * n₂ * m) * a / (s * n * m) / a ^ 4 := by
  field_simp (config := {maxDischargeDepth := 9}); ring

lemma smulY_add_sub_negY (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    ψ₂ (smulX (n + m)) (smulY (n + m)) =
      (ψ₂ (smulX m) (smulY m) * (smulX n - smulX (n + m))
        - ψ₂ (smulX n) (smulY n) * (smulX m - smulX (n + m))) / (smulX m - smulX n) := by
  simp_rw [smulY_sub_negY add_ne, smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hn add_ne,
    smulX_sub_smulX hm add_ne, smulX_sub_smulX hm hn, add_sub_cancel_left, add_sub_cancel_right]
  rw [smulY_add_sub_negY_aux]
  · congr; rw [eq_div_iff]
    · linear_combination (norm := ring_nf) (net_add_sub_iff _ n m).mp (net_ψᵤ _ _ _ _)
    apply_rules [mul_ne_zero, ψᵤ_ne_zero]
  all_goals apply ψᵤ_ne_zero; assumption

open Affine.Point

instance : AddGroup (curve⟮Universal.Field⟯) := inferInstance -- Lean needs a reminder at add_zsmul
theorem zsmul_eq_quotient_divisionPolynomial : n ≠ 0 →
    ∃ h : Affine.Nonsingular _ (smulX n) (smulY n), n • Universal.point = .some h := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih h0 ↦ ?_
    obtain _|_|_|n := n
    · exact (h0 rfl).elim
    · simp_rw [zero_add, Nat.cast_one, one_zsmul, smulX_one, smulY_one]
      exact ⟨EllipticCurve.Affine.nonsingular pointedCurve equation_point, rfl⟩
    all_goals obtain ⟨ns, eq⟩ := ih 1 (by omega) one_ne_zero
    · erw [← addX_smul_one_smul_one, ← addY_smul_one_smul_one, zero_add, add_zsmul _ 1 1, eq]
      exact ⟨Affine.nonsingular_add ns ns fun _ ↦ smulY_one_ne_negY,
        dif_neg fun h ↦ smulY_one_ne_negY h.2⟩
    set n2 := n + 1 + 1
    obtain ⟨ns1, eq1⟩ := ih (n + 1) (by omega) (by omega)
    obtain ⟨ns2, eq2⟩ := ih n2 (by omega) (by omega)
    have ne : smulX n2 ≠ smulX 1 := smulX_ne_smulX (by omega) (by omega)
    simp_rw [show (n + 1 : ℕ) = n2 + (-1 : ℤ) by omega, add_zsmul, neg_smul] at eq1
    let _U := pointedCurve.toAffine
    erw [eq2, eq, some_add_some_of_Xne ne, some_eq_some_iff] at eq1
    let L := _U.slope (smulX n2) (smulX 1) (smulY n2) (smulY 1)
    have X_eq : smulX (n2 + 1 : ℕ) = _U.addX (smulX n2) (smulX 1) L := by
      rw [Nat.cast_add, Nat.cast_one, smulX_add one_ne_zero (by omega) (by omega) (by omega),
        Affine.addX_eq_subX_sub _ _ ne, sub_eq_add_neg (n2 : ℤ), ← eq1.1]; rfl
    have Y_eq : smulY (n2 + 1 : ℕ) = _U.addY (smulX n2) (smulX 1) (smulY n2) L := by
      rw [← mul_cancel_left_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero Field.two_ne_zero),
        ← add_right_cancel_iff (a := _U.a₁ * smulX (n2 + 1 : ℕ) + _U.a₃)]
      convert smulY_add_sub_negY (n := n2) one_ne_zero (by omega) (by omega) (by omega) using 1
      · simp_rw [Affine.negY, Nat.cast_add]; ring_nf
      convert _U.addY_sub_negY (smulY n2) (smulY 1) ne using 1
      · rw [Affine.negY, ← X_eq]; ring
      · rw [← X_eq]; rfl
    rw [X_eq, Y_eq, n2.cast_add, add_zsmul, eq, eq2]
    exact ⟨Affine.nonsingular_add ns2 ns (ne · |>.elim), some_add_some_of_Xne ne⟩
  | neg n hn =>
    rw [neg_ne_zero]; intro h0
    obtain ⟨ns, eq⟩ := hn h0
    simp_rw [smulX_neg, smulY_neg h0, neg_smul, eq, neg_some]
    exact ⟨Affine.nonsingular_neg ns, trivial⟩

lemma smul_point_ne_zero (h0 : n ≠ 0) : n • Universal.point ≠ 0 := by
  obtain ⟨ns, eq⟩ := zsmul_eq_quotient_divisionPolynomial h0
  rw [eq]; exact Affine.Point.some_ne_zero ns

end Affine

namespace Jacobian

open WeierstrassCurve.Jacobian

/-- The distinguished point on the universal curve in Jacobian coordinates. -/
protected def point : Jacobian.Point (curve.baseChange Universal.Field) :=
  Jacobian.Point.fromAffine Universal.point

lemma smul_point_ne_zero (h0 : n ≠ 0) : n • Jacobian.point ≠ 0 := by
  rw [Jacobian.point, ← Point.toAffineAddEquiv_symm_apply, ← map_zsmul, Ne,
    map_eq_zero_iff _ Point.toAffineAddEquiv.symm.injective]
  exact Affine.smul_point_ne_zero h0

lemma smul_point_ne (h : m ≠ n) : m • Jacobian.point ≠ n • Jacobian.point := by
  rw [← sub_ne_zero, sub_eq_add_neg, ← sub_zsmul]
  exact smul_point_ne_zero (sub_ne_zero.mpr h)

lemma point_point : Jacobian.point.point = ⟦![polyToField (C X), polyToField Y, 1]⟧ := rfl

/-- The base change of the universal curve from `ℤ[a₁,⋯,a₆]` to `ℤ[a₁,⋯,a₆,X,Y]`. -/
abbrev curvePoly : WeierstrassCurve Poly := curve.baseChange Poly
/-- The base change of the universal curve from `ℤ[a₁,⋯,a₆]` to `ℤ[a₁,⋯,a₆,X,Y]/⟨P⟩`
(the universal ring), where `P` is the Weierstrass polynomial. -/
abbrev curveRing : WeierstrassCurve Universal.Ring := curve.baseChange Universal.Ring
/-- The base change of the universal curve from `ℤ[a₁,⋯,a₆]` to `Frac(ℤ[a₁,⋯,a₆,X,Y]/⟨P⟩)`
(the universal field), where `P` is the Weierstrass polynomial. -/
abbrev curveField : WeierstrassCurve Universal.Field := curve.baseChange Universal.Field
/-- The three families of division polynomials as a 3-tuple. -/
abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, curve.ω n, curve.ψ n]
/-- The three families of division polynomials as elements in the universal ring. -/
abbrev smulRing (n : ℤ) : Fin 3 → Universal.Ring := AdjoinRoot.mk _ ∘ smulPoly n
/-- The three families of division polynomials as elements in the universal field. -/
abbrev smulField (n : ℤ) : Fin 3 → Universal.Field := polyToField ∘ smulPoly n

lemma algebraMap_comp_smulRing (n : ℤ) : algebraMap _ _ ∘ smulRing n = smulField n := by
  ext i; fin_cases i <;> rfl

lemma curveField_eq : curveField = pointedCurve.toWeierstrassCurve := rfl

theorem zsmul_eq_divisionPolynomial : (n • Jacobian.point).point = ⟦smulField n⟧ := by
  rw [← fin3_def (smulField n), smulField, smulPoly]
  simp_rw [Function.comp, fin3_def_ext]
  obtain rfl | hn := eq_or_ne n 0
  · simp_rw [zero_zsmul, φ_zero, ω_zero, ψ_zero, map_zero, map_one]; rfl
  obtain ⟨ns, eq⟩ := Affine.zsmul_eq_quotient_divisionPolynomial hn
  change (n • Jacobian.Point.toAffineAddEquiv.symm Universal.point).point = _
  rw [← map_zsmul, eq]
  have := ψᵤ_ne_zero hn
  refine Quotient.sound ⟨.mk0 _ (inv_ne_zero this), ?_⟩
  simp_rw [Units.smul_def, Jacobian.smul_fin3']
  ext i; fin_cases i <;> field_simp [Affine.smulX, Affine.smulY, this]

lemma dblZ_smulPoly : dblZ curvePoly (smulPoly n) = curve.ψ (2 * n) := by
  simp_rw [dblZ, smulPoly, negY, fin3_def_ext, curvePoly, baseChange, map, coe_algebraMap_eq_CC]
  rw [← ψc_spec _ n]; congr; convert curve.ω_spec n using 1; ring

lemma nonsingular_smulField : Nonsingular curveField (smulField n) := by
  simpa only [zsmul_eq_divisionPolynomial] using (n • Jacobian.point).nonsingular

lemma dblXYZ_smulField : dblXYZ curveField (smulField n) = smulField (2 * n) := by
  obtain rfl | hn := eq_or_ne n 0
  · norm_num [dblXYZ, dblX, dblY, dblZ, negY, dblY', smulField, smulPoly, curveField, ← fin3_def]
  erw [← equiv_iff_eq_of_Z_eq _ (ψᵤ_ne_zero <| mul_ne_zero two_ne_zero hn),
    ← Quotient.eq, ← zsmul_eq_divisionPolynomial, mul_zsmul,
    Point.two_smul_point zsmul_eq_divisionPolynomial]
  · rfl
  simp only [smulField, smulPoly, fin3_def_ext, Function.comp, ← dblZ_smulPoly, ← map_dblZ]; rfl

lemma dblXYZ_smulRing : dblXYZ curveRing (smulRing n) = smulRing (2 * n) :=
  (IsFractionRing.injective _ Universal.Field).comp_left <| by
    simp_rw [← map_dblXYZ]; exact dblXYZ_smulField

lemma addZ_smulPoly : addZ (smulPoly m) (smulPoly n) = curve.ψ (n + m) * curve.ψ (n - m) := by
  simp_rw [addZ, smulPoly, φ]; convert (curve.isEllSequence_ψ n m 1).symm using 1
  · simp only [fin3_def_ext]; ring
  · rw [ψ_one]; ring

lemma ω_neg_eq_neg_negY : curve.ω (-n) = -negY curvePoly (smulPoly n) := by
  simp_rw [ω_neg, negY, smulPoly, fin3_def_ext, curvePoly, baseChange, map, coe_algebraMap_eq_CC]
  ring

lemma smulPoly_neg : smulPoly (-n) = (-1 : Poly) • neg curvePoly (smulPoly n) := by
  simp [smulPoly, ω_neg_eq_neg_negY, neg, smul_fin3', (show Odd 3 by decide).neg_pow]

lemma smulRing_neg : smulRing (-n) = (-1 : Universal.Ring) • neg curveRing (smulRing n) := by
  simp_rw [smulRing, smulPoly_neg, Jacobian.map_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl

lemma smulField_neg : smulField (-n) = (-1 : Universal.Field) • neg curveField (smulField n) := by
  simp_rw [smulField, smulPoly_neg, Jacobian.map_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl

lemma smulPoly_zero : smulPoly 0 = ![1, 1, 0] := by simp [smulPoly]
lemma smulField_zero : smulField 0 = ![1, 1, 0] := by simp [smulField, smulPoly_zero, comp_fin3]

lemma addXYZ_smulField :
    addXYZ curveField (smulField m) (smulField n) =
      polyToField (curve.ψ (n - m)) • smulField (n + m) := by
  obtain rfl | h := eq_or_ne m n
  · rw [sub_self, ψ_zero, map_zero, smul_fin3,
      addXYZ_self nonsingular_smulField.1, zero_pow two_ne_zero, zero_pow (by decide)]
    simp_rw [zero_mul]
  obtain rfl | ne_neg := eq_or_ne n (-m)
  · rw [← one_smul (M := Universal.Field) (smulField m), smulField_neg, add_left_neg,
      addXYZ_smul, one_mul, neg_one_sq (R := Universal.Field), addXYZ_neg nonsingular_smulField.1,
      one_smul, ← neg_add', ← two_mul, ψ_neg, map_neg, ← dblZ_smulPoly, ← map_dblZ, smulField_zero]
    rfl
  erw [← equiv_iff_eq_of_Z_eq, ← Quotient.eq, ← Units.smul_mk0 (ψᵤ_ne_zero <|
    sub_ne_zero_of_ne h.symm), smul_eq, ← zsmul_eq_divisionPolynomial, add_comm, add_zsmul,
    Point.add_point_of_ne zsmul_eq_divisionPolynomial zsmul_eq_divisionPolynomial (smul_point_ne h)]
  · rfl
  · conv_rhs => rw [smulField, comp_fin3, smul_fin3', (fin3_def_ext _ _ _).2.2, mul_comm]
    simp_rw [addXYZ, fin3_def_ext, ← map_mul, ← addZ_smulPoly, ← map_addZ]
  · apply mul_ne_zero <;> apply ψᵤ_ne_zero <;> omega

lemma addXYZ_smulRing :
    addXYZ curveRing (smulRing m) (smulRing n) =
      AdjoinRoot.mk curve.polynomial (curve.ψ (n - m)) • smulRing (n + m) :=
  (IsFractionRing.injective Universal.Ring Universal.Field).comp_left <| by
    simp_rw [← map_addXYZ, Jacobian.map_smul]; exact addXYZ_smulField

lemma addXYZ_smulField₁ :
    addXYZ curveField (smulField n) (smulField (n + 1)) = smulField (2 * n + 1) := by
  rw [addXYZ_smulField, add_sub_cancel_left, ψ_one, map_one, one_smul, two_mul, add_comm, add_assoc]

lemma addXYZ_smulRing₁ :
    addXYZ curveRing (smulRing n) (smulRing (n + 1)) = smulRing (2 * n + 1) := by
  rw [addXYZ_smulRing, add_sub_cancel_left, ψ_one, map_one, one_smul, two_mul, add_comm, add_assoc]

end Jacobian

end Universal

variable (x y) in
/-- The evaluation of the division polynomials at a point `(x,y)`, equal to the
Jacobian coordinates of `n • (x,y)` (see `smul_eq_divisionPolynomial_eval`). -/
abbrev smulEval (n : ℤ) : Fin 3 → R := evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]

variable {W} (eqn : W.toAffine.Equation x y)

open Universal.Jacobian

lemma ringEval_comp_smulRing (n : ℤ) : ringEval eqn ∘ smulRing n = smulEval W x y n := by
  conv_rhs => rw [smulEval, ← W.map_specialize, map_φ, map_ω, map_ψ, ← coe_mapRingHom,
    ← Jacobian.comp_fin3, ← Function.comp.assoc, ← smulPoly, ← coe_evalEvalRingHom]
  simp_rw [smulRing, ← Function.comp.assoc, ← RingHom.coe_comp, ringEval_comp_mk]
  congr!; ext <;> simp [polyEval]

lemma ringEval_ψ (n : ℤ) :
    ringEval eqn (AdjoinRoot.mk _ <| Universal.curve.ψ n) = evalEval x y (W.ψ n) :=
  congr_fun (ringEval_comp_smulRing eqn n) 2

lemma curveRing_map_ringEval : curveRing.map (ringEval eqn) = W := by
  rw [curveRing, baseChange, map_map, ringEval_comp_eq_specialize, map_specialize]

open Jacobian

lemma dblXYZ_smul (n : ℤ) : dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← dblXYZ_smulRing, ← map_dblXYZ, curveRing_map_ringEval]

lemma addXYZ_smul (m n : ℤ) :
    addXYZ W (smulEval W x y m) (smulEval W x y n) =
      evalEval x y (W.ψ (n - m)) • smulEval W x y (n + m) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← ringEval_ψ eqn]
  rw [← Jacobian.map_smul, ← addXYZ_smulRing, ← map_addXYZ, curveRing_map_ringEval]

lemma addXYZ_smul₁ (n : ℤ) :
    addXYZ W (smulEval W x y n) (smulEval W x y (n + 1)) =
      smulEval W x y (2 * n + 1) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← addXYZ_smulRing₁, ← map_addXYZ, curveRing_map_ringEval]

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

open Universal

-- move this
local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow])

theorem smul_eq_divisionPolynomial_eval {x y : F} (h : Affine.Nonsingular W x y) (n : ℤ) :
    (n • Point.fromAffine (Affine.Point.some h)).point = ⟦smulEval W x y n⟧ := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    obtain _|_|n := n
    · rw [Nat.cast_zero, zero_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    · rw [Nat.cast_one, one_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    obtain ⟨n, rfl|rfl⟩ := n.even_or_odd'
    · rw [add_assoc, ← two_mul, ← left_distrib, Nat.cast_mul, mul_smul, natCast_zsmul,
        Point.two_smul_point (ih _ <| by omega), dblXYZ_smul h.1]; rfl
    · rw [show 2 * n + 1 + 1 + 1 = (n + 1) + (n + 1 + 1) by omega, Nat.cast_add, add_smul,
        Point.add_point_of_ne (ih _ <| by omega) (ih _ <| by omega), Nat.cast_add (n + 1),
        Nat.cast_one, addXYZ_smul₁ h.1, ← add_assoc, two_mul]
      simp_rw [Nat.cast_add]
      rw [ne_comm, ← sub_ne_zero, ← sub_smul, add_sub_cancel_left, Nat.cast_one, one_smul]
      apply Point.fromAffine_ne_zero
  | neg n hn =>
    simp_rw [neg_smul, Point.neg_point, hn, eq_comm]
    refine Quotient.sound ⟨-1, ?_⟩
    simp_rw [← ringEval_comp_smulRing h.1, smulRing_neg, Jacobian.map_smul, ← Jacobian.map_neg,
      curveRing_map_ringEval, map_neg, map_one]
    rfl

end

end WeierstrassCurve
