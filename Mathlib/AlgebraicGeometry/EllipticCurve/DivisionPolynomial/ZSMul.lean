/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Integer multiples of a rational point on a elliptic curve in terms of division polynomials

This file proves the formula `WeierstrassCurve.zsmul_eq_smulEval`, which says that
`n • P = (φₙ(x,y) : ωₙ(x,y), ψₙ(x,y))` in Jacobian coordinates for any integer `n`
and any nonsingular rational point `P : W.Point` in affine coordinates `(x,y)`
on a Weierstrass curve `W` over a field.

It is easy to deduce the formula for `(-n) • P` from the formula for `n • P`, and the
`n = 0` and `n = 1` cases are trivially verified. The formula for `n > 1` is proved by
even-odd induction on `n`. If `n = 2 * m`, we use the doubling formula to write `n • P`
as `Jacobian.dblXYZ (m • P)`, while if `n = 2 * m + 1`, we use the addition formula to write it
as `Jacobian.addXYZ (m • P) ((m + 1) • P)`. By induction hypothesis, `m • P` and `(m + 1) • P` are
given by evaluation of division polynomials, so our task reduces to proving certain polynomial
identities (`dblXYZ_smulEval` and `addXYZ_smulEval₁`), namely that the polynomials
`dblXYZ` and `addXYZ`, when applied to `(φₘ, ωₘ, ψₘ)` and `(φₘ₊₁, ωₘ₊₁, ψₘ₊₁)`, yields
`(φ₂ₘ, ω₂ₘ, ψ₂ₘ)` and `(φ₂ₘ₊₁, ω₂ₘ₊₁, ψ₂ₘ₊₁)`, modulo the Weierstrass polynomial.
It is crucial that two formulas (`dblXYZ` for doubling, `addXYZ` for addition of two different
points) suffice to cover all cases of the group law in Jacobian coordinates.
Since `P = (x,y) ≠ O`, `m • P` is never equal to `(m + 1) • P`, so `addXYZ` always apply
in the `2 * m + 1` case (it gives `(0,0,0)` when applied to two equal points),
and `dblXYZ` always applies in the `2 * m` case.

Since `dblXYZ`, `addXYZ` and the division polynomials are all compatible with ring homomorphisms,
it suffices to prove the universal division polynomials satisfy these identities
(`dblXYZ_smulRing` and `addXYZ_smulRing`). Since the ring homomorphism from the universal ring
to the universal field is injective, it suffices to prove these identities in the universal field
(`dblXYZ_smulField` and `addXYZ_smulField`), which amounts to the universal case of the identities
`dblXYZ (φₘ, ωₘ, ψₘ) = (φ₂ₘ, ω₂ₘ, ψ₂ₘ)` and
`addXYZ (φₘ, ωₘ, ψₘ) (φₘ₊₁, ωₘ₊₁, ψₘ₊₁) = (φ₂ₘ₊₁, ω₂ₘ₊₁, ψ₂ₘ₊₁)`, with `P = (X,Y)` the
universal point on the universal curve. It is easy to show the Z-coordinates are equal
even in the polynomial ring (`dblZ_smulPoly` and `addZ_smulPoly`), without passing to the quotient.

Since `ψₙ` is nonzero when `n` is, to show that the other coordinates are also equal, it suffices
to show the two sides, when interpreted as Jacobian coordinates, represent the same point on the
universal curve, according to `Jacobian.equiv_iff_eq_of_Z_eq`. If we can show the universal
case of the multiplication formula `n • P = ⟦(φₘ, ωₙ, ψₙ)⟧` with `P = (X,Y) = ⟦(X, Y, 1)⟧`
(`Universal.Jacobian.zsmul_point_eq_smulField`), then the two desired identities become
`dblXYZ (m • P) = (2 * m) • P` and `addXYZ (m • P) ((m + 1) • P) = (2 * m + 1) • P`,
which are true by the validity of the doubling and addition formulas.

Equivalently, we aim to prove the formula in affine coordinates: `n • (X,Y) = (φₘ/ψₙ², ωₙ/ψₙ³)`
for `n ≠ 0` (`Universal.Affine.zsmul_point_eq_smulX_smulY`), but this time it is easier to use
vanilla induction on `n` rather than the even-odd induction, because we have formulas expressing
the affine coordinates of `(n+1) • P` in terms of those of `P`, `n • P` and `(n-1) • P`
(`Affine.addX_eq_subX_sub`, `Affine.addY_sub_negY`).
We only need to verify the base cases `n = 1` and `n = 2`, and the induction step is handled
by fancy identities of division polynomials and elliptic divisibility sequences
(`smulX_sub_sub_smulX_add`, `smulX_add` and `smulY_add_sub_negY`).
-/

open scoped PolynomialPolynomial

namespace WeierstrassCurve

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)

noncomputable section

variable {x y : R}

namespace Universal

lemma evalEval_ψ₂ : W.ψ₂.evalEval x y = polyEval W x y curve.ψ₂ := by
  simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]

lemma evalEval_Ψ₃ : (C W.Ψ₃).evalEval x y = polyEval W x y (C curve.Ψ₃) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_Ψ₃, map_specialize]

lemma evalEval_preΨ₄ : (C W.preΨ₄).evalEval x y = polyEval W x y (C curve.preΨ₄) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]

variable {m n : ℤ}

lemma evalEval_ψ : (W.ψ n).evalEval x y = polyEval W x y (curve.ψ n) := by
  simp_rw [polyEval_apply, ← map_ψ, map_specialize]

lemma evalEval_φ : (W.φ n).evalEval x y = polyEval W x y (curve.φ n) := by
  simp_rw [polyEval_apply, ← map_φ, map_specialize]

lemma evalEval_ω : (W.ω n).evalEval x y =  polyEval W x y (curve.ω n) := by
  simp_rw [polyEval_apply, ← map_ω, map_specialize]

open WeierstrassCurve (ψ φ ω)

lemma cusp_ψ₂ : cusp.ψ₂ = 2 * Y := by simp [cusp, ψ₂, Affine.polynomialY]
lemma cusp_Ψ₃ : cusp.Ψ₃ = 3 * X ^ 4 := by simp [cusp, Ψ₃, b₂, b₄, b₆, b₈]
lemma cusp_preΨ₄ : cusp.preΨ₄ = 2 * X ^ 6 := by simp [cusp, preΨ₄, b₂, b₄, b₆, b₈]

lemma polyEval_cusp_ψ : polyEval cusp 1 1 (curve.ψ n) = n := by
  rw [ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄, cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]
  simp [evalEval, normEDS_two_three_two]

lemma polyEval_cusp_φ : polyEval cusp 1 1 (curve.φ n) = 1 := by
  simp_rw [φ, map_sub, map_mul, map_pow, polyEval_cusp_ψ, polyEval]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X]; ring

lemma polyEval_cusp_ψc : polyEval cusp 1 1 (curve.ψc n) = 2 := by
  rw [ψc, map_compl₂EDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄]
  simp [cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄, evalEval, compl₂EDS_two_three_two]

lemma polyEval_cusp_ω : polyEval cusp 1 1 (curve.ω n) = 1 := by
  have := congr(polyEval cusp 1 1 $(curve.two_mul_ω n))
  simp_rw [map_sub, map_mul, map_ofNat, polyEval_cusp_ψc] at this
  simpa [cusp, polyEval, specialize, curve] using this

/-- The `ψ` family of division polynomials as elements in the universal field. -/
abbrev ψᵤ (n : ℤ) : Universal.Field := polyToField (curve.ψ n)

lemma ψᵤ_eq_normEDS :
    ψᵤ = normEDS
      (polyToField curve.ψ₂) (polyToField <| C curve.Ψ₃) (polyToField <| C curve.preΨ₄) := by
  ext; rw [← map_normEDS]; rfl

lemma isEllSequence_ψᵤ : IsEllSequence ψᵤ := by rw [ψᵤ_eq_normEDS]; exact IsEllSequence.normEDS
lemma net_ψᵤ (p q r s) : EllSequence.net ψᵤ p q r s = 0 := by rw [ψᵤ_eq_normEDS]; apply net_normEDS

lemma ψᵤ_ne_zero (h0 : n ≠ 0) : ψᵤ n ≠ 0 := fun h ↦ by
  rw [ψᵤ, polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_ψ, map_zero] at h
  exact h0 h

lemma polyToField_φ_ne_zero : polyToField (curve.φ n) ≠ 0 := fun h ↦ by
  rw [polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_φ, map_zero] at h
  exact one_ne_zero h

lemma polyToField_ψ₂Sq : polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2 := by
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

lemma slopeOne_eq_neg_div : slopeOne = -polyToField curve.polynomialX / ψᵤ 2 := by
  rw [slopeOne, Affine.slope_of_Y_ne rfl smulY_one_ne_negY, smulY_one_sub_negY, Affine.polynomialX]
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
    ψ_two, ψ_three, C_Ψ₃_eq, polyToField_polynomial, pointedCurve_a₁, pointedCurve_a₂, smulX_one]
  ring

private lemma addY_smul_one_smul_one_aux {F} [Field F] {a₁ a₃ dx dy x y ψ₃ t : F} (h0 : dy ≠ 0) :
    ((a₁ * dy - dx) * ψ₃ + 0 * t + (-y - (a₁ * x + a₃)) * dy ^ 3) / dy ^ 3 =
      -(-dx / dy * (x - ψ₃ / dy ^ 2 - x) + y) - a₁ * (x - ψ₃ / dy ^ 2) - a₃ := by
  field_simp; ring

open EllSequence in
lemma addY_smul_one_smul_one :
    pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2 := .symm <| by
  rw [smulY, ω, redInvarDenom_two, one_mul, compl₂EDSAux_two, sub_zero, Affine.addY,
    Affine.negAddY, addX_smul_one_smul_one, smulX_two, Affine.negY, Affine.negPolynomial,
    slopeOne_eq_neg_div, ← ψ₂, ← ψ_two, smulX_one, smulY_one, ψᵤ, ψᵤ, ψ_three]
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
    · linear_combination (norm := ring_nf) (EllSequence.net_add_sub_iff _ n m).mp (net_ψᵤ _ _ _ _)
    apply_rules [mul_ne_zero, ψᵤ_ne_zero]
  all_goals apply ψᵤ_ne_zero; assumption

open Affine.Point

open WeierstrassCurve.Affine in
instance : AddGroup (curve⟮Universal.Field⟯) := inferInstance -- Lean needs a reminder at add_zsmul

/-- The affine coordinates of `n • Universal.Affine.point` is given by `(smulX n, smulY n)`. -/
theorem zsmul_point_eq_smulX_smulY : n ≠ 0 →
    ∃ h : Affine.Nonsingular _ (smulX n) (smulY n), n • Affine.point = .some h := by
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
    erw [eq2, eq, add_of_X_ne ne, some_eq_some_iff] at eq1
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
    exact ⟨Affine.nonsingular_add ns2 ns (ne · |>.elim), add_of_X_ne ne⟩
  | neg n hn =>
    rw [neg_ne_zero]; intro h0
    obtain ⟨ns, eq⟩ := hn h0
    simp_rw [smulX_neg, smulY_neg h0, neg_smul, eq, neg_some]
    exact ⟨Affine.nonsingular_neg ns, trivial⟩

lemma nonsingular_smulX_smulY (hn : n ≠ 0) : Affine.Nonsingular curveField (smulX n) (smulY n) :=
  (zsmul_point_eq_smulX_smulY hn).1

/-- The distinguished point `(X,Y)` on the universal curve is not torsion. -/
lemma zsmul_point_ne_zero (h0 : n ≠ 0) : n • Affine.point ≠ 0 := by
  obtain ⟨ns, eq⟩ := zsmul_point_eq_smulX_smulY h0
  rw [eq]; exact Affine.Point.some_ne_zero ns

end Affine

namespace Jacobian

open WeierstrassCurve.Jacobian

open Point in
lemma zsmul_point_ne_zero (h0 : n ≠ 0) : n • Jacobian.point ≠ 0 := by
  rw [Jacobian.point, ← toAffineAddEquiv_symm_apply, ← map_zsmul (toAffineAddEquiv _).symm,
    Ne, map_eq_zero_iff _ (toAffineAddEquiv _).symm.injective]
  exact Affine.zsmul_point_ne_zero h0

lemma zsmul_point_ne (h : m ≠ n) : m • Jacobian.point ≠ n • Jacobian.point := by
  rw [← sub_ne_zero, sub_eq_add_neg, ← sub_zsmul]
  exact zsmul_point_ne_zero (sub_ne_zero.mpr h)

lemma point_point : Jacobian.point.point = ⟦![polyToField (C X), polyToField Y, 1]⟧ := rfl

/-- The three families of universal division polynomials as a 3-tuple. -/
abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, curve.ω n, curve.ψ n]
/-- The three families of division polynomials as elements in the universal ring. -/
abbrev smulRing (n : ℤ) : Fin 3 → Universal.Ring := AdjoinRoot.mk _ ∘ smulPoly n
/-- The three families of division polynomials as elements in the universal field. -/
abbrev smulField (n : ℤ) : Fin 3 → Universal.Field := polyToField ∘ smulPoly n

lemma algebraMap_comp_smulRing (n : ℤ) : algebraMap _ _ ∘ smulRing n = smulField n := by
  ext i; fin_cases i <;> rfl

/-- The Jacobian coordinates of `n • Universal.Jacobian.point` is given by `smulField n`. -/
theorem zsmul_point_eq_smulField : (n • Jacobian.point).point = ⟦smulField n⟧ := by
  rw [← fin3_def (smulField n), smulField, smulPoly]
  simp_rw [Function.comp, fin3_def_ext]
  obtain rfl | hn := eq_or_ne n 0
  · simp_rw [zero_zsmul, φ_zero, ω_zero, ψ_zero, map_zero, map_one]; rfl
  obtain ⟨ns, eq⟩ := Affine.zsmul_point_eq_smulX_smulY hn
  change (n • (Point.toAffineAddEquiv _).symm Affine.point).point = _
  rw [← map_zsmul, eq]
  have := ψᵤ_ne_zero hn
  refine Quotient.sound ⟨.mk0 _ (inv_ne_zero this), ?_⟩
  simp_rw [Units.smul_def, Jacobian.smul_fin3]
  ext i; fin_cases i <;> field_simp [Affine.smulX, Affine.smulY, this]

lemma dblZ_smulPoly : dblZ curvePoly (smulPoly n) = curve.ψ (2 * n) := by
  simp_rw [dblZ, smulPoly, negY, fin3_def_ext, curvePoly, baseChange, map, coe_algebraMap_eq_CC]
  rw [← ψc_spec _ n]; congr; convert curve.ω_spec n using 1; ring

lemma nonsingular_smulField : Nonsingular curveField (smulField n) := by
  simpa only [zsmul_point_eq_smulField] using (n • Jacobian.point).nonsingular

lemma dblXYZ_smulField : dblXYZ curveField (smulField n) = smulField (2 * n) := by
  obtain rfl | hn := eq_or_ne n 0
  · norm_num [dblXYZ, dblX, dblY, dblZ, dblU_eq, negY, negDblY,
      smulField, smulPoly, curveField, ← fin3_def]
  erw [← equiv_iff_eq_of_Z_eq _ (ψᵤ_ne_zero <| mul_ne_zero two_ne_zero hn),
    ← Quotient.eq, ← zsmul_point_eq_smulField,
    mul_zsmul (α := Point <| baseChange curve Universal.Field),
    Point.two_zsmul_point zsmul_point_eq_smulField]
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
  simp [smulPoly, ω_neg_eq_neg_negY, neg, smul_fin3, (show Odd 3 by decide).neg_pow]

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
  erw [← equiv_iff_eq_of_Z_eq, ← Quotient.eq, smul_eq _ (ψᵤ_ne_zero <|
    sub_ne_zero_of_ne h.symm).isUnit, ← zsmul_point_eq_smulField, add_comm, add_zsmul,
    Point.add_point_of_ne zsmul_point_eq_smulField zsmul_point_eq_smulField (zsmul_point_ne h)]
  · rfl
  · conv_rhs => rw [smulField, comp_fin3, smul_fin3, (fin3_def_ext _ _ _).2.2, mul_comm]
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

open Universal Jacobian

lemma ringEval_comp_smulRing (n : ℤ) : ringEval eqn ∘ smulRing n = smulEval W x y n := by
  conv_rhs => rw [smulEval, ← W.map_specialize, map_φ, map_ω, map_ψ, ← coe_mapRingHom,
    ← Jacobian.comp_fin3, ← Function.comp.assoc, ← smulPoly, ← coe_evalEvalRingHom,
    ← RingHom.coe_comp, ← eval₂RingHom_eval₂RingHom]
  rw [smulRing, ← Function.comp.assoc, ← RingHom.coe_comp, ringEval_comp_mk, polyEval]

lemma ringEval_ψ (n : ℤ) :
    ringEval eqn (AdjoinRoot.mk _ <| curve.ψ n) = evalEval x y (W.ψ n) :=
  congr_fun (ringEval_comp_smulRing eqn n) 2

lemma dblXYZ_smulEval (n : ℤ) : dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← dblXYZ_smulRing, ← map_dblXYZ, curveRing_map_ringEval]

lemma addXYZ_smulEval (m n : ℤ) :
    addXYZ W (smulEval W x y m) (smulEval W x y n) =
      evalEval x y (W.ψ (n - m)) • smulEval W x y (n + m) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← ringEval_ψ eqn]
  rw [← Jacobian.map_smul, ← addXYZ_smulRing, ← map_addXYZ, curveRing_map_ringEval]

lemma addXYZ_smulEval₁ (n : ℤ) :
    addXYZ W (smulEval W x y n) (smulEval W x y (n + 1)) = smulEval W x y (2 * n + 1) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← addXYZ_smulRing₁, ← map_addXYZ, curveRing_map_ringEval]

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

open Universal

/-- The integer multiples of a nonsingular rational point `(x,y)` on a Weierstrass curve
is given by `smulEval` in Jacobian coordinates. -/
theorem zsmul_eq_smulEval {x y : F} (h : Affine.Nonsingular W x y) (n : ℤ) :
    (n • Point.fromAffine (Affine.Point.some h)).point = ⟦smulEval W x y n⟧ := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    obtain _|_|n := n
    · rw [Nat.cast_zero, zero_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    · rw [Nat.cast_one, one_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    obtain ⟨n, rfl|rfl⟩ := n.even_or_odd'
    · rw [add_assoc, ← two_mul, ← left_distrib, Nat.cast_mul, mul_smul, natCast_zsmul,
        Point.two_zsmul_point (ih _ <| by omega), dblXYZ_smulEval h.1]; rfl
    · rw [show 2 * n + 1 + 1 + 1 = (n + 1) + (n + 1 + 1) by omega, Nat.cast_add, add_smul,
        Point.add_point_of_ne (ih _ <| by omega) (ih _ <| by omega), Nat.cast_add (n + 1),
        Nat.cast_one, addXYZ_smulEval₁ h.1, ← add_assoc, two_mul]
      simp_rw [Nat.cast_add]
      rw [ne_comm, ← sub_ne_zero, ← sub_smul, add_sub_cancel_left, Nat.cast_one, one_smul]
      apply Point.fromAffine_ne_zero
  | neg n hn =>
    simp_rw [_root_.neg_smul, Point.neg_point, hn, eq_comm]
    refine Quotient.sound ⟨-1, ?_⟩
    simp_rw [← ringEval_comp_smulRing h.1, smulRing_neg, Jacobian.map_smul, ← Jacobian.map_neg,
      curveRing_map_ringEval, map_neg, map_one]
    rfl

end

end WeierstrassCurve
