/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Division polynomials of Weierstrass curves

This file defines certain polynomials associated to division polynomials of Weierstrass curves.
These are defined in terms of the auxiliary sequences for normalised elliptic divisibility sequences
(EDS) as defined in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.

## Mathematical background

Let `W` be a Weierstrass curve over a commutative ring `R`. The sequence of `n`-division polynomials
`ψₙ ∈ R[X, Y]` of `W` is the normalised EDS with initial values
* `ψ₀ := 0`,
* `ψ₁ := 1`,
* `ψ₂ := 2Y + a₁X + a₃`,
* `ψ₃ := 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`, and
* `ψ₄ := ψ₂ ⬝ (2X⁶ + b₂X⁵ + 5b₄X⁴ + 10b₆X³ + 10b₈X² + (b₂b₈ - b₄b₆)X + (b₄b₈ - b₆²))`.

Furthermore, define the associated sequences `φₙ, ωₙ ∈ R[X, Y]` by
* `φₙ := Xψₙ² - ψₙ₊₁ ⬝ ψₙ₋₁`, and
* `ωₙ := (ψ₂ₙ / ψₙ - ψₙ ⬝ (a₁φₙ + a₃ψₙ²)) / 2`.

Note that `ωₙ` is always well-defined as a polynomial in `R[X, Y]`. As a start, it can be shown by
induction that `ψₙ` always divides `ψ₂ₙ` in `R[X, Y]`, so that `ψ₂ₙ / ψₙ` is always well-defined as
a polynomial, while division by `2` is well-defined when `R` has characteristic different from `2`.
In general, it can be shown that `2` always divides the polynomial `ψ₂ₙ / ψₙ - ψₙ ⬝ (a₁φₙ + a₃ψₙ²)`
in the characteristic `0` universal ring `𝓡[X, Y] := ℤ[A₁, A₂, A₃, A₄, A₆][X, Y]` of `W`, where the
`Aᵢ` are indeterminates. Then `ωₙ` can be equivalently defined as the image of this division under
the associated universal morphism `𝓡[X, Y] → R[X, Y]` mapping `Aᵢ` to `aᵢ`.

Now, in the coordinate ring `R[W]`, note that `ψ₂²` is congruent to the polynomial
`Ψ₂Sq := 4X³ + b₂X² + 2b₄X + b₆ ∈ R[X]`. As such, the recurrences of a normalised EDS show that
`ψₙ / ψ₂` are congruent to certain polynomials in `R[W]`. In particular, define `preΨₙ ∈ R[X]` as
the auxiliary sequence for a normalised EDS with extra parameter `Ψ₂Sq²` and initial values
* `preΨ₀ := 0`,
* `preΨ₁ := 1`,
* `preΨ₂ := 1`,
* `preΨ₃ := ψ₃`, and
* `preΨ₄ := ψ₄ / ψ₂`.

The corresponding normalised EDS `Ψₙ ∈ R[X, Y]` is then given by
* `Ψₙ := preΨₙ ⬝ ψ₂` if `n` is even, and
* `Ψₙ := preΨₙ` if `n` is odd.

Furthermore, define the associated sequences `ΨSqₙ, Φₙ ∈ R[X]` by
* `ΨSqₙ := preΨₙ² ⬝ Ψ₂Sq` if `n` is even,
* `ΨSqₙ := preΨₙ²` if `n` is odd,
* `Φₙ := XΨSqₙ - preΨₙ₊₁ ⬝ preΨₙ₋₁` if `n` is even, and
* `Φₙ := XΨSqₙ - preΨₙ₊₁ ⬝ preΨₙ₋₁ ⬝ Ψ₂Sq` if `n` is odd.

With these definitions, `ψₙ ∈ R[X, Y]` and `φₙ ∈ R[X, Y]` are congruent in `R[W]` to `Ψₙ ∈ R[X, Y]`
and `Φₙ ∈ R[X]` respectively, which are defined in terms of `Ψ₂Sq ∈ R[X]` and `preΨₙ ∈ R[X]`.

## Main definitions

* `WeierstrassCurve.preΨ`: the univariate polynomials `preΨₙ`.
* `WeierstrassCurve.ΨSq`: the univariate polynomials `ΨSqₙ`.
* `WeierstrassCurve.Ψ`: the bivariate polynomials `Ψₙ`.
* `WeierstrassCurve.Φ`: the univariate polynomials `Φₙ`.
* `WeierstrassCurve.ψ`: the bivariate `n`-division polynomials `ψₙ`.
* `WeierstrassCurve.φ`: the bivariate polynomials `φₙ`.
* TODO: the bivariate polynomials `ωₙ`.

## Implementation notes

Analogously to `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, the bivariate polynomials
`Ψₙ` are defined in terms of the univariate polynomials `preΨₙ`. This is done partially to avoid
ring division, but more crucially to allow the definition of `ΨSqₙ` and `Φₙ` as univariate
polynomials without needing to work under the coordinate ring, and to allow the computation of their
leading terms without ambiguity. Furthermore, evaluating these polynomials at a rational point on
`W` recovers their original definition up to linear combinations of the Weierstrass equation of `W`,
hence also avoiding the need to work in the coordinate ring.

TODO: implementation notes for the definition of `ωₙ`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point
-/

open Polynomial
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀,
    Polynomial.map_ofNat, Polynomial.map_one, map_C, map_X, Polynomial.map_neg, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_div, coe_mapRingHom,
    apply_ite <| mapRingHom _, WeierstrassCurve.map])

universe r s u v

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

section Ψ₂Sq

/-! ### The univariate polynomial `Ψ₂Sq` -/

/-- The `2`-division polynomial `ψ₂ = Ψ₂`. -/
noncomputable def ψ₂ : R[X][Y] :=
  W.toAffine.polynomialY

/-- The univariate polynomial `Ψ₂Sq` congruent to `ψ₂²`. -/
noncomputable def Ψ₂Sq : R[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

lemma C_Ψ₂Sq : C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial := by
  rw [Ψ₂Sq, ψ₂, b₂, b₄, b₆, Affine.polynomialY, Affine.polynomial]
  C_simp
  ring1

lemma ψ₂_sq : W.ψ₂ ^ 2 = C W.Ψ₂Sq + 4 * W.toAffine.polynomial := by
  rw [C_Ψ₂Sq, sub_add_cancel]

lemma Affine.CoordinateRing.mk_ψ₂_sq : mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq) := by
  rw [C_Ψ₂Sq, map_sub, map_mul, AdjoinRoot.mk_self, mul_zero, sub_zero, map_pow]

-- TODO: remove `twoTorsionPolynomial` in favour of `Ψ₂Sq`
lemma Ψ₂Sq_eq : W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly :=
  rfl

end Ψ₂Sq

section preΨ'

/-! ### The univariate polynomials `preΨₙ` for `n ∈ ℕ` -/

/-- The `3`-division polynomial `ψ₃ = Ψ₃`. -/
noncomputable def Ψ₃ : R[X] :=
  3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈

/-- The univariate polynomial `preΨ₄`, which is auxiliary to the 4-division polynomial
`ψ₄ = Ψ₄ = preΨ₄ψ₂`. -/
noncomputable def preΨ₄ : R[X] :=
  2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)

/-- The univariate polynomials `preΨₙ` for `n ∈ ℕ`, which are auxiliary to the bivariate polynomials
`Ψₙ` congruent to the bivariate `n`-division polynomials `ψₙ`. -/
noncomputable def preΨ' (n : ℕ) : R[X] :=
  preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n

@[simp]
lemma preΨ'_zero : W.preΨ' 0 = 0 :=
  preNormEDS'_zero ..

@[simp]
lemma preΨ'_one : W.preΨ' 1 = 1 :=
  preNormEDS'_one ..

@[simp]
lemma preΨ'_two : W.preΨ' 2 = 1 :=
  preNormEDS'_two ..

@[simp]
lemma preΨ'_three : W.preΨ' 3 = W.Ψ₃ :=
  preNormEDS'_three ..

@[simp]
lemma preΨ'_four : W.preΨ' 4 = W.preΨ₄ :=
  preNormEDS'_four ..

lemma preΨ'_even (m : ℕ) : W.preΨ' (2 * (m + 3)) =
    W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 3) * W.preΨ' (m + 5) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) * W.preΨ' (m + 4) ^ 2 :=
  preNormEDS'_even ..

lemma preΨ'_odd (m : ℕ) : W.preΨ' (2 * (m + 2) + 1) =
    W.preΨ' (m + 4) * W.preΨ' (m + 2) ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=
  preNormEDS'_odd ..

end preΨ'

section preΨ

/-! ### The univariate polynomials `preΨₙ` for `n ∈ ℤ` -/

/-- The univariate polynomials `preΨₙ` for `n ∈ ℤ`, which are auxiliary to the bivariate polynomials
`Ψₙ` congruent to the bivariate `n`-division polynomials `ψₙ`. -/
noncomputable def preΨ (n : ℤ) : R[X] :=
  preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n

@[simp]
lemma preΨ_ofNat (n : ℕ) : W.preΨ n = W.preΨ' n :=
  preNormEDS_ofNat ..

@[simp]
lemma preΨ_zero : W.preΨ 0 = 0 :=
  preNormEDS_zero ..

@[simp]
lemma preΨ_one : W.preΨ 1 = 1 :=
  preNormEDS_one ..

@[simp]
lemma preΨ_two : W.preΨ 2 = 1 :=
  preNormEDS_two ..

@[simp]
lemma preΨ_three : W.preΨ 3 = W.Ψ₃ :=
  preNormEDS_three ..

@[simp]
lemma preΨ_four : W.preΨ 4 = W.preΨ₄ :=
  preNormEDS_four ..

lemma preΨ_even_ofNat (m : ℕ) : W.preΨ (2 * (m + 3)) =
    W.preΨ (m + 2) ^ 2 * W.preΨ (m + 3) * W.preΨ (m + 5) -
      W.preΨ (m + 1) * W.preΨ (m + 3) * W.preΨ (m + 4) ^ 2 :=
  preNormEDS_even_ofNat ..

lemma preΨ_odd_ofNat (m : ℕ) : W.preΨ (2 * (m + 2) + 1) =
    W.preΨ (m + 4) * W.preΨ (m + 2) ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ (m + 1) * W.preΨ (m + 3) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=
  preNormEDS_odd_ofNat ..

@[simp]
lemma preΨ_neg (n : ℤ) : W.preΨ (-n) = -W.preΨ n :=
  preNormEDS_neg ..

lemma preΨ_even (m : ℤ) : W.preΨ (2 * m) =
    W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -
      W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2 :=
  preNormEDS_even ..

lemma preΨ_odd (m : ℤ) : W.preΨ (2 * m + 1) =
    W.preΨ (m + 2) * W.preΨ m ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=
  preNormEDS_odd ..

end preΨ

section ΨSq

/-! ### The univariate polynomials `ΨSqₙ` -/

/-- The univariate polynomials `ΨSqₙ` congruent to `ψₙ²`. -/
noncomputable def ΨSq (n : ℤ) : R[X] :=
  W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1

@[simp]
lemma ΨSq_ofNat (n : ℕ) : W.ΨSq n = W.preΨ' n ^ 2 * if Even n then W.Ψ₂Sq else 1 := by
  simp only [ΨSq, preΨ_ofNat, Int.even_coe_nat]

@[simp]
lemma ΨSq_zero : W.ΨSq 0 = 0 := by
  rw [← Nat.cast_zero, ΨSq_ofNat, preΨ'_zero, zero_pow two_ne_zero, zero_mul]

@[simp]
lemma ΨSq_one : W.ΨSq 1 = 1 := by
  rw [← Nat.cast_one, ΨSq_ofNat, preΨ'_one, one_pow, one_mul, if_neg Nat.not_even_one]

@[simp]
lemma ΨSq_two : W.ΨSq 2 = W.Ψ₂Sq := by
  rw [← Nat.cast_two, ΨSq_ofNat, preΨ'_two, one_pow, one_mul, if_pos even_two]

@[simp]
lemma ΨSq_three : W.ΨSq 3 = W.Ψ₃ ^ 2 := by
  rw [← Nat.cast_three, ΨSq_ofNat, preΨ'_three, if_neg <| by decide, mul_one]

@[simp]
lemma ΨSq_four : W.ΨSq 4 = W.preΨ₄ ^ 2 * W.Ψ₂Sq := by
  rw [← Nat.cast_four, ΨSq_ofNat, preΨ'_four, if_pos <| by decide]

lemma ΨSq_even_ofNat (m : ℕ) : W.ΨSq (2 * (m + 3)) =
    (W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 3) * W.preΨ' (m + 5) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) * W.preΨ' (m + 4) ^ 2) ^ 2 * W.Ψ₂Sq := by
  rw_mod_cast [ΨSq_ofNat, preΨ'_even, if_pos <| even_two_mul _]

lemma ΨSq_odd_ofNat (m : ℕ) : W.ΨSq (2 * (m + 2) + 1) =
    (W.preΨ' (m + 4) * W.preΨ' (m + 2) ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2)) ^ 2 := by
  rw_mod_cast [ΨSq_ofNat, preΨ'_odd, if_neg (m + 2).not_even_two_mul_add_one, mul_one]

@[simp]
lemma ΨSq_neg (n : ℤ) : W.ΨSq (-n) = W.ΨSq n := by
  simp only [ΨSq, preΨ_neg, neg_sq, even_neg]

lemma ΨSq_even (m : ℤ) : W.ΨSq (2 * m) =
    (W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -
      W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2) ^ 2 * W.Ψ₂Sq := by
  rw [ΨSq, preΨ_even, if_pos <| even_two_mul _]

lemma ΨSq_odd (m : ℤ) : W.ΨSq (2 * m + 1) =
    (W.preΨ (m + 2) * W.preΨ m ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2)) ^ 2 := by
  rw [ΨSq, preΨ_odd, if_neg m.not_even_two_mul_add_one, mul_one]

end ΨSq

section Ψ

/-! ### The bivariate polynomials `Ψₙ` -/

/-- The bivariate polynomials `Ψₙ` congruent to the `n`-division polynomials `ψₙ`. -/
protected noncomputable def Ψ (n : ℤ) : R[X][Y] :=
  C (W.preΨ n) * if Even n then W.ψ₂ else 1

open WeierstrassCurve (Ψ)

@[simp]
lemma Ψ_ofNat (n : ℕ) : W.Ψ n = C (W.preΨ' n) * if Even n then W.ψ₂ else 1 := by
  simp only [Ψ, preΨ_ofNat, Int.even_coe_nat]

@[simp]
lemma Ψ_zero : W.Ψ 0 = 0 := by
  rw [← Nat.cast_zero, Ψ_ofNat, preΨ'_zero, C_0, zero_mul]

@[simp]
lemma Ψ_one : W.Ψ 1 = 1 := by
  rw [← Nat.cast_one, Ψ_ofNat, preΨ'_one, C_1, if_neg Nat.not_even_one, mul_one]

@[simp]
lemma Ψ_two : W.Ψ 2 = W.ψ₂ := by
  rw [← Nat.cast_two, Ψ_ofNat, preΨ'_two, C_1, one_mul, if_pos even_two]

@[simp]
lemma Ψ_three : W.Ψ 3 = C W.Ψ₃ := by
  rw [← Nat.cast_three, Ψ_ofNat, preΨ'_three, if_neg <| by decide, mul_one]

@[simp]
lemma Ψ_four : W.Ψ 4 = C W.preΨ₄ * W.ψ₂ := by
  rw [← Nat.cast_four, Ψ_ofNat, preΨ'_four, if_pos <| by decide]

lemma Ψ_even_ofNat (m : ℕ) : W.Ψ (2 * (m + 3)) * W.ψ₂ =
    W.Ψ (m + 2) ^ 2 * W.Ψ (m + 3) * W.Ψ (m + 5) - W.Ψ (m + 1) * W.Ψ (m + 3) * W.Ψ (m + 4) ^ 2 := by
  repeat rw_mod_cast [Ψ_ofNat]
  simp_rw [preΨ'_even, if_pos <| even_two_mul _, Nat.even_add_one, ite_not]
  split_ifs <;> C_simp <;> ring1

lemma Ψ_odd_ofNat (m : ℕ) : W.Ψ (2 * (m + 2) + 1) =
    W.Ψ (m + 4) * W.Ψ (m + 2) ^ 3 - W.Ψ (m + 1) * W.Ψ (m + 3) ^ 3 +
      W.toAffine.polynomial * (16 * W.toAffine.polynomial - 8 * W.ψ₂ ^ 2) *
        C (if Even m then W.preΨ' (m + 4) * W.preΨ' (m + 2) ^ 3
            else -W.preΨ' (m + 1) * W.preΨ' (m + 3) ^ 3) := by
  repeat rw_mod_cast [Ψ_ofNat]
  simp_rw [preΨ'_odd, if_neg (m + 2).not_even_two_mul_add_one, Nat.even_add_one, ite_not]
  split_ifs <;> C_simp <;> rw [C_Ψ₂Sq] <;> ring1

@[simp]
lemma Ψ_neg (n : ℤ) : W.Ψ (-n) = -W.Ψ n := by
  simp only [Ψ, preΨ_neg, C_neg, neg_mul (α := R[X][Y]), even_neg]

lemma Ψ_even (m : ℤ) : W.Ψ (2 * m) * W.ψ₂ =
    W.Ψ (m - 1) ^ 2 * W.Ψ m * W.Ψ (m + 2) - W.Ψ (m - 2) * W.Ψ m * W.Ψ (m + 1) ^ 2 := by
  repeat rw [Ψ]
  simp_rw [preΨ_even, if_pos <| even_two_mul _, Int.even_add_one, show m + 2 = m + 1 + 1 by ring1,
    Int.even_add_one, show m - 2 = m - 1 - 1 by ring1, Int.even_sub_one, ite_not]
  split_ifs <;> C_simp <;> ring1

lemma Ψ_odd (m : ℤ) : W.Ψ (2 * m + 1) =
    W.Ψ (m + 2) * W.Ψ m ^ 3 - W.Ψ (m - 1) * W.Ψ (m + 1) ^ 3 +
      W.toAffine.polynomial * (16 * W.toAffine.polynomial - 8 * W.ψ₂ ^ 2) *
        C (if Even m then W.preΨ (m + 2) * W.preΨ m ^ 3
            else -W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3) := by
  repeat rw [Ψ]
  simp_rw [preΨ_odd, if_neg m.not_even_two_mul_add_one, show m + 2 = m + 1 + 1 by ring1,
    Int.even_add_one, Int.even_sub_one, ite_not]
  split_ifs <;> C_simp <;> rw [C_Ψ₂Sq] <;> ring1

lemma Affine.CoordinateRing.mk_Ψ_sq (n : ℤ) : mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n) := by
  simp only [Ψ, ΨSq, map_one, map_mul, map_pow, one_pow, mul_pow, ite_pow, apply_ite C,
    apply_ite <| mk W, mk_ψ₂_sq]

end Ψ

section Φ

/-! ### The univariate polynomials `Φₙ` -/

/-- The univariate polynomials `Φₙ` congruent to `φₙ`. -/
protected noncomputable def Φ (n : ℤ) : R[X] :=
  X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq

open WeierstrassCurve (Φ)

@[simp]
lemma Φ_ofNat (n : ℕ) : W.Φ (n + 1) =
    X * W.preΨ' (n + 1) ^ 2 * (if Even n then 1 else W.Ψ₂Sq) -
      W.preΨ' (n + 2) * W.preΨ' n * (if Even n then W.Ψ₂Sq else 1) := by
  rw [Φ, ← Nat.cast_one, ← Nat.cast_add, ΨSq_ofNat, ← mul_assoc, ← Nat.cast_add, preΨ_ofNat,
    Nat.cast_add, add_sub_cancel_right, preΨ_ofNat, ← Nat.cast_add]
  simp only [Nat.even_add_one, Int.even_add_one, Int.even_coe_nat, ite_not]

@[simp]
lemma Φ_zero : W.Φ 0 = 1 := by
  rw [Φ, ΨSq_zero, mul_zero, zero_sub, zero_add, preΨ_one, one_mul, zero_sub, preΨ_neg, preΨ_one,
    neg_one_mul, neg_neg, if_pos Even.zero]

@[simp]
lemma Φ_one : W.Φ 1 = X := by
  rw [show 1 = ((0 : ℕ) + 1 : ℤ) by rfl, Φ_ofNat, preΨ'_one, one_pow, mul_one, if_pos Even.zero,
    mul_one, preΨ'_zero, mul_zero, zero_mul, sub_zero]

@[simp]
lemma Φ_two : W.Φ 2 = X ^ 4 - C W.b₄ * X ^ 2 - C (2 * W.b₆) * X - C W.b₈ := by
  rw [show 2 = ((1 : ℕ) + 1 : ℤ) by rfl, Φ_ofNat, preΨ'_two, if_neg Nat.not_even_one, Ψ₂Sq,
    preΨ'_three, preΨ'_one, if_neg Nat.not_even_one, Ψ₃]
  C_simp
  ring1

@[simp]
lemma Φ_three : W.Φ 3 = X * W.Ψ₃ ^ 2 - W.preΨ₄ * W.Ψ₂Sq := by
  rw [show 3 = ((2 : ℕ) + 1 : ℤ) by rfl, Φ_ofNat, preΨ'_three, if_pos <| by decide, mul_one,
    preΨ'_four, preΨ'_two, mul_one, if_pos even_two]

@[simp]
lemma Φ_four : W.Φ 4 = X * W.preΨ₄ ^ 2 * W.Ψ₂Sq - W.Ψ₃ * (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) := by
  rw [show 4 = ((3 : ℕ) + 1 : ℤ) by rfl, Φ_ofNat, preΨ'_four, if_neg <| by decide,
    show 3 + 2 = 2 * 2 + 1 by rfl, preΨ'_odd, preΨ'_four, preΨ'_two, if_pos Even.zero, preΨ'_one,
    preΨ'_three, if_pos Even.zero, if_neg <| by decide]
  ring1

@[simp]
lemma Φ_neg (n : ℤ) : W.Φ (-n) = W.Φ n := by
  simp only [Φ, ΨSq_neg, neg_add_eq_sub, ← neg_sub n, preΨ_neg, ← neg_add', preΨ_neg, neg_mul_neg,
    mul_comm <| W.preΨ <| n - 1, even_neg]

end Φ

section ψ

/-! ### The bivariate polynomials `ψₙ` -/

/-- The bivariate `n`-division polynomials `ψₙ`. -/
protected noncomputable def ψ (n : ℤ) : R[X][Y] :=
  normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

open WeierstrassCurve (Ψ ψ)

@[simp]
lemma ψ_zero : W.ψ 0 = 0 :=
  normEDS_zero ..

@[simp]
lemma ψ_one : W.ψ 1 = 1 :=
  normEDS_one ..

@[simp]
lemma ψ_two : W.ψ 2 = W.ψ₂ :=
  normEDS_two ..

@[simp]
lemma ψ_three : W.ψ 3 = C W.Ψ₃ :=
  normEDS_three ..

@[simp]
lemma ψ_four : W.ψ 4 = C W.preΨ₄ * W.ψ₂ :=
  normEDS_four ..

lemma ψ_even_ofNat (m : ℕ) : W.ψ (2 * (m + 3)) * W.ψ₂ =
    W.ψ (m + 2) ^ 2 * W.ψ (m + 3) * W.ψ (m + 5) - W.ψ (m + 1) * W.ψ (m + 3) * W.ψ (m + 4) ^ 2 :=
  normEDS_even_ofNat ..

lemma ψ_odd_ofNat (m : ℕ) : W.ψ (2 * (m + 2) + 1) =
    W.ψ (m + 4) * W.ψ (m + 2) ^ 3 - W.ψ (m + 1) * W.ψ (m + 3) ^ 3 :=
  normEDS_odd_ofNat ..

@[simp]
lemma ψ_neg (n : ℤ) : W.ψ (-n) = -W.ψ n :=
  normEDS_neg ..

lemma ψ_even (m : ℤ) : W.ψ (2 * m) * W.ψ₂ =
    W.ψ (m - 1) ^ 2 * W.ψ m * W.ψ (m + 2) - W.ψ (m - 2) * W.ψ m * W.ψ (m + 1) ^ 2 :=
  normEDS_even ..

lemma ψ_odd (m : ℤ) : W.ψ (2 * m + 1) =
    W.ψ (m + 2) * W.ψ m ^ 3 - W.ψ (m - 1) * W.ψ (m + 1) ^ 3 :=
  normEDS_odd ..

lemma Affine.CoordinateRing.mk_ψ (n : ℤ) : mk W (W.ψ n) = mk W (W.Ψ n) := by
  simp only [ψ, normEDS, Ψ, preΨ, map_mul, map_pow, map_preNormEDS, ← mk_ψ₂_sq, ← pow_mul]

end ψ

section φ

/-! ### The bivariate polynomials `φₙ` -/

/-- The bivariate polynomials `φₙ`. -/
protected noncomputable def φ (n : ℤ) : R[X][Y] :=
  C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)

open WeierstrassCurve (Ψ Φ φ)

@[simp]
lemma φ_zero : W.φ 0 = 1 := by
  rw [φ, ψ_zero, zero_pow two_ne_zero, mul_zero, zero_sub, zero_add, ψ_one, one_mul, zero_sub,
    ψ_neg, neg_neg, ψ_one]

@[simp]
lemma φ_one : W.φ 1 = C X := by
  rw [φ, ψ_one, one_pow, mul_one, sub_self, ψ_zero, mul_zero, sub_zero]

@[simp]
lemma φ_two : W.φ 2 = C X * W.ψ₂ ^ 2 - C W.Ψ₃ := by
  rw [φ, ψ_two, two_add_one_eq_three, ψ_three, show (2 - 1 : ℤ) = 1 by rfl, ψ_one, mul_one]

@[simp]
lemma φ_three : W.φ 3 = C X * C W.Ψ₃ ^ 2 - C W.preΨ₄ * W.ψ₂ ^ 2 := by
  rw [φ, ψ_three, three_add_one_eq_four, ψ_four, mul_assoc, show (3 - 1 : ℤ) = 2 by rfl, ψ_two,
    ← sq]

@[simp]
lemma φ_four :
    W.φ 4 = C X * C W.preΨ₄ ^ 2 * W.ψ₂ ^ 2 - C W.preΨ₄ * W.ψ₂ ^ 4 * C W.Ψ₃ + C W.Ψ₃ ^ 4 := by
  rw [φ, ψ_four, show (4 + 1 : ℤ) = 2 * 2 + 1 by rfl, ψ_odd, two_add_two_eq_four, ψ_four,
    show (2 - 1 : ℤ) = 1 by rfl, ψ_two, ψ_one, two_add_one_eq_three, show (4 - 1 : ℤ) = 3 by rfl,
    ψ_three]
  ring1

@[simp]
lemma φ_neg (n : ℤ) : W.φ (-n) = W.φ n := by
  rw [φ, ψ_neg, neg_sq (R := R[X][Y]), neg_add_eq_sub, ← neg_sub n, ψ_neg, ← neg_add', ψ_neg,
    neg_mul_neg (α := R[X][Y]), mul_comm <| W.ψ _, φ]

lemma Affine.CoordinateRing.mk_φ (n : ℤ) : mk W (W.φ n) = mk W (C <| W.Φ n) := by
  simp_rw [φ, Φ, map_sub, map_mul, map_pow, mk_ψ, mk_Ψ_sq, Ψ, map_mul,
    mul_mul_mul_comm _ <| mk W <| ite .., Int.even_add_one, Int.even_sub_one, ← sq, ite_not,
    apply_ite C, apply_ite <| mk W, ite_pow, map_one, one_pow, mk_ψ₂_sq]

end φ

section Map

/-! ### Maps across ring homomorphisms -/

open WeierstrassCurve (Ψ Φ ψ φ)

variable (f : R →+* S)

lemma map_ψ₂ : (W.map f).ψ₂ = W.ψ₂.map (mapRingHom f) := by
  simp only [ψ₂, Affine.map_polynomialY]

lemma map_Ψ₂Sq : (W.map f).Ψ₂Sq = W.Ψ₂Sq.map f := by
  simp only [Ψ₂Sq, map_b₂, map_b₄, map_b₆]
  map_simp

lemma map_Ψ₃ : (W.map f).Ψ₃ = W.Ψ₃.map f := by
  simp only [Ψ₃, map_b₂, map_b₄, map_b₆, map_b₈]
  map_simp

lemma map_preΨ₄ : (W.map f).preΨ₄ = W.preΨ₄.map f := by
  simp only [preΨ₄, map_b₂, map_b₄, map_b₆, map_b₈]
  map_simp

lemma map_preΨ' (n : ℕ) : (W.map f).preΨ' n = (W.preΨ' n).map f := by
  simp only [preΨ', map_Ψ₂Sq, map_Ψ₃, map_preΨ₄, ← coe_mapRingHom, map_preNormEDS']
  map_simp

lemma map_preΨ (n : ℤ) : (W.map f).preΨ n = (W.preΨ n).map f := by
  simp only [preΨ, map_Ψ₂Sq, map_Ψ₃, map_preΨ₄, ← coe_mapRingHom, map_preNormEDS]
  map_simp

lemma map_ΨSq (n : ℤ) : (W.map f).ΨSq n = (W.ΨSq n).map f := by
  simp only [ΨSq, map_preΨ, map_Ψ₂Sq, ← coe_mapRingHom]
  map_simp

lemma map_Ψ (n : ℤ) : (W.map f).Ψ n = (W.Ψ n).map (mapRingHom f) := by
  simp only [Ψ, map_preΨ, map_ψ₂, ← coe_mapRingHom]
  map_simp

lemma map_Φ (n : ℤ) : (W.map f).Φ n = (W.Φ n).map f := by
  simp only [Φ, map_ΨSq, map_preΨ, map_Ψ₂Sq, ← coe_mapRingHom]
  map_simp

lemma map_ψ (n : ℤ) : (W.map f).ψ n = (W.ψ n).map (mapRingHom f) := by
  simp only [ψ, map_ψ₂, map_Ψ₃, map_preΨ₄, ← coe_mapRingHom, map_normEDS]
  map_simp

lemma map_φ (n : ℤ) : (W.map f).φ n = (W.φ n).map (mapRingHom f) := by
  simp only [φ, map_ψ]
  map_simp

end Map

section BaseChange

/-! ### Base changes across algebra homomorphisms -/

variable [Algebra R S] {A : Type u} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  {B : Type v} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[S] B)

lemma baseChange_ψ₂ : (W.baseChange B).ψ₂ = (W.baseChange A).ψ₂.map (mapRingHom f) := by
  rw [← map_ψ₂, map_baseChange]

lemma baseChange_Ψ₂Sq : (W.baseChange B).Ψ₂Sq = (W.baseChange A).Ψ₂Sq.map f := by
  rw [← map_Ψ₂Sq, map_baseChange]

lemma baseChange_Ψ₃ : (W.baseChange B).Ψ₃ = (W.baseChange A).Ψ₃.map f := by
  rw [← map_Ψ₃, map_baseChange]

lemma baseChange_preΨ₄ : (W.baseChange B).preΨ₄ = (W.baseChange A).preΨ₄.map f := by
  rw [← map_preΨ₄, map_baseChange]

lemma baseChange_preΨ' (n : ℕ) : (W.baseChange B).preΨ' n = ((W.baseChange A).preΨ' n).map f := by
  rw [← map_preΨ', map_baseChange]

lemma baseChange_preΨ (n : ℤ) : (W.baseChange B).preΨ n = ((W.baseChange A).preΨ n).map f := by
  rw [← map_preΨ, map_baseChange]

lemma baseChange_ΨSq (n : ℤ) : (W.baseChange B).ΨSq n = ((W.baseChange A).ΨSq n).map f := by
  rw [← map_ΨSq, map_baseChange]

lemma baseChange_Ψ (n : ℤ) : (W.baseChange B).Ψ n = ((W.baseChange A).Ψ n).map (mapRingHom f) := by
  rw [← map_Ψ, map_baseChange]

lemma baseChange_Φ (n : ℤ) : (W.baseChange B).Φ n = ((W.baseChange A).Φ n).map f := by
  rw [← map_Φ, map_baseChange]

lemma baseChange_ψ (n : ℤ) : (W.baseChange B).ψ n = ((W.baseChange A).ψ n).map (mapRingHom f) := by
  rw [← map_ψ, map_baseChange]

lemma baseChange_φ (n : ℤ) : (W.baseChange B).φ n = ((W.baseChange A).φ n).map (mapRingHom f) := by
  rw [← map_φ, map_baseChange]

end BaseChange

end WeierstrassCurve
