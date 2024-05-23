/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.Data.Int.Parity
import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Division polynomials of Weierstrass curves

This file defines certain polynomials associated to division polynomials of Weierstrass curves and
computes their leading terms. These are defined in terms of the auxiliary sequences of normalised
elliptic divisibility sequences defined in `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

## Mathematical background

Let $W$ be a Weierstrass curve over a commutative ring $R$. The sequence of $n$-division polynomials
of $W$ is a normalised elliptic divisibility sequence $\psi_n \in R[X][Y]$ with initial values
 * $\psi_0 = 0$,
 * $\psi_1 = 1$,
 * $\psi_2 = 2Y + a_1X + a_3$,
 * $\psi_3 = 3X^4 + b_2X^3 + 3b_4X ^ 2 + 3b_6X + b_8$, and
 * $\psi_4 = \psi_2 \cdot
    (2X^6 + b_2X^5 + 5b_4X^4 + 10b_6X^3 + 10b_8X^2 + (b_2b_8 - b_4b_6)X + (b_4b_8 - b_6^2))$.
Furthermore, define associated sequences $\phi_n, \omega_n, \widetilde{\psi_n} \in R[X][Y]$ by
 * $\phi_n := x\psi_n^2 - \psi_{n + 1}\psi_{n - 1}$,
 * $\omega_n := \tfrac{1}{2\psi_n} \cdot (\psi_{2n} - \psi_n^2(a_1\phi_n + a_3\psi_n^2)$, and
 * $\tilde{\psi}_n := \psi_n / \psi_2$ if $n$ is even and $\tilde{\psi}_n := \psi_n$ otherwise.
Under the coordinate ring $R[W]$ of $W$, the $2$-division polynomial $\psi_2$ satisfies the identity
$\psi_2^2 \equiv 4X^3 + b_2X^2 + 2b_4X + b_6$, so that $\phi_n, \psi_n^2, \tilde{\psi}_n \in R[X]$.
Furthermore, their leading terms can be computed via induction to be $\phi_n = X^{n^2} + \dots$
and $\psi_n^2 = n^2X^{n^2 - 1} + \dots$, and $\tilde{\psi}_n = nX^{\tfrac{n^2 - 4}{2}} + \dots$
if $n$ is even or $\tilde{\psi}_n = nX^{\tfrac{n^2 - 1}{2}} + \dots$ otherwise.

## Main definitions

 * `WeierstrassCurve.divisionPolynomial2Sq`: $\psi_2^2$ viewed as a univariate polynomial.
 * `WeierstrassCurve.divisionPolynomial`: $\tilde{\psi}_n$ viewed as a univariate polynomial.
 * `WeierstrassCurve.divisionPolynomialZSq`: $\psi_n^2$ viewed as a univariate polynomial.
 * `WeierstrassCurve.divisionPolynomialX`: $\phi_n$ viewed as a univariate polynomial.
 * `WeierstrassCurve.divisionPolynomialZ`: $\psi_n$ viewed as a bivariate polynomial.
 * TODO: $\omega$ viewed as a bivariate polynomial.

## Implementation notes

Analogously to `Mathlib.NumberTheory.EllipticDivisibilitySequence`, the $n$-division bivariate
polynomials $\psi_n$ are defined in terms of the univariate polynomials $\tilde{\psi}_n$. This is
done partially to avoid ring division, but more crucially to allow the definition of $\phi_n$ and
$\psi_n^2$ as univariate polynomials without needing to work under the coordinate ring, and to allow
the computation of their leading terms without ambiguity. Furthermore, evaluating these polynomials
at a rational point $(x, y)$ on $W$ recovers their original definition up to linear combinations of
the Weierstrass equation of $W$, hence also avoiding the need to work under the coordinate ring.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point
-/

open Polynomial PolynomialPolynomial

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-! ### The univariate polynomial congruent to $\psi_2^2$ -/

/-- The polynomial $4X^3 + b_2X^2 + 2b_4X + b_6$ congruent to the square $\psi_2^2$ of the
$2$-division polynomial $\psi_2 = 2Y + a_1X + a_3$ under $R[W]$. -/
noncomputable def divisionPolynomial2Sq : R[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

-- TODO: remove `twoTorsionPolynomial` in favour of `divisionPolynomial2Sq`
lemma divisionPolynomial2Sq_eq : W.divisionPolynomial2Sq = W.twoTorsionPolynomial.toPoly :=
  rfl

/-! ### The univariate polynomials congruent to $\tilde{\psi}_n$ for $n \in \mathbb{N}$ -/

/-- The univariate polynomials congruent under $R[W]$ to the bivariate auxiliary polynomials
$\tilde{\psi}_n$ associated to the $n$-division polynomials $\psi_n$ for $n \in \mathbb{N}$. -/
noncomputable def divisionPolynomial' (n : ℕ) : R[X] :=
  preNormEDS' (W.divisionPolynomial2Sq ^ 2)
    (3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈)
    (2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
      C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)) n

@[simp]
lemma divisionPolynomial'_zero : W.divisionPolynomial' 0 = 0 :=
  preNormEDS'_zero ..

@[simp]
lemma divisionPolynomial'_one : W.divisionPolynomial' 1 = 1 :=
  preNormEDS'_one ..

@[simp]
lemma divisionPolynomial'_two : W.divisionPolynomial' 2 = 1 :=
  preNormEDS'_two ..

@[simp]
lemma divisionPolynomial'_three : W.divisionPolynomial' 3 =
    3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈ :=
  preNormEDS'_three ..

@[simp]
lemma divisionPolynomial'_four : W.divisionPolynomial' 4 =
    2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
      C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2) :=
  preNormEDS'_four ..

lemma divisionPolynomial'_odd (m : ℕ) : W.divisionPolynomial' (2 * (m + 2) + 1) =
    W.divisionPolynomial' (m + 4) * W.divisionPolynomial' (m + 2) ^ 3 *
      (if Even m then W.divisionPolynomial2Sq ^ 2 else 1) -
    W.divisionPolynomial' (m + 1) * W.divisionPolynomial' (m + 3) ^ 3 *
      (if Even m then 1 else W.divisionPolynomial2Sq ^ 2) :=
  preNormEDS'_odd ..

lemma divisionPolynomial'_even (m : ℕ) : W.divisionPolynomial' (2 * (m + 3)) =
    W.divisionPolynomial' (m + 2) ^ 2 * W.divisionPolynomial' (m + 3) *
      W.divisionPolynomial' (m + 5) -
    W.divisionPolynomial' (m + 1) * W.divisionPolynomial' (m + 3) *
      W.divisionPolynomial' (m + 4) ^ 2 :=
  preNormEDS'_even ..

/-! ### The univariate polynomials congruent to $\tilde{\psi}_n$ for $n \in \mathbb{Z}$ -/

/-- The univariate polynomials congruent under $R[W]$ to the bivariate auxiliary polynomials
$\tilde{\psi}_n$ associated to the $n$-division polynomials $\psi_n$ for $n \in \mathbb{Z}$. -/
noncomputable def divisionPolynomial (n : ℤ) : R[X] :=
  n.sign * W.divisionPolynomial' n.natAbs

@[simp]
lemma divisionPolynomial_ofNat (n : ℕ) : W.divisionPolynomial n = W.divisionPolynomial' n :=
  preNormEDS_ofNat ..

@[simp]
lemma divisionPolynomial_zero : W.divisionPolynomial 0 = 0 :=
  preNormEDS_zero ..

@[simp]
lemma divisionPolynomial_one : W.divisionPolynomial 1 = 1 :=
  preNormEDS_one ..

@[simp]
lemma divisionPolynomial_two : W.divisionPolynomial 2 = 1 :=
  preNormEDS_two ..

@[simp]
lemma divisionPolynomial_three : W.divisionPolynomial 3 = W.divisionPolynomial' 3 :=
  preNormEDS_three ..

@[simp]
lemma divisionPolynomial_four : W.divisionPolynomial 4 = W.divisionPolynomial' 4 :=
  preNormEDS_four ..

lemma divisionPolynomial_odd (m : ℕ) : W.divisionPolynomial (2 * (m + 2) + 1) =
    W.divisionPolynomial (m + 4) * W.divisionPolynomial (m + 2) ^ 3 *
      (if Even m then W.divisionPolynomial2Sq ^ 2 else 1) -
    W.divisionPolynomial (m + 1) * W.divisionPolynomial (m + 3) ^ 3 *
      (if Even m then 1 else W.divisionPolynomial2Sq ^ 2) :=
  preNormEDS_odd ..

lemma divisionPolynomial_even (m : ℕ) : W.divisionPolynomial (2 * (m + 3)) =
    W.divisionPolynomial (m + 2) ^ 2 * W.divisionPolynomial (m + 3) *
      W.divisionPolynomial (m + 5) -
    W.divisionPolynomial (m + 1) * W.divisionPolynomial (m + 3) *
      W.divisionPolynomial (m + 4) ^ 2 :=
  preNormEDS_even ..

@[simp]
lemma divisionPolynomial_neg (n : ℤ) : W.divisionPolynomial (-n) = -W.divisionPolynomial n :=
  preNormEDS_neg ..

/-! ### The univariate polynomials congruent to $\psi_n^2$ for $n \in \mathbb{Z}$ -/

/-- The univariate polynomials congruent under $R[W]$ to the bivariate squares $\psi_n^2$ of the
$n$-division polynomials $\psi_n$ for $n \in \mathbb{Z}$. -/
noncomputable def divisionPolynomialZSq (n : ℤ) : R[X] :=
  W.divisionPolynomial n ^ 2 * if Even n.natAbs then W.divisionPolynomial2Sq else 1

@[simp]
lemma divisionPolynomialZSq_ofNat (n : ℕ) : W.divisionPolynomialZSq n =
    W.divisionPolynomial' n ^ 2 * if Even n then W.divisionPolynomial2Sq else 1 := by
  rw [divisionPolynomialZSq, divisionPolynomial_ofNat, Int.natAbs_cast]

@[simp]
lemma divisionPolynomialZSq_zero : W.divisionPolynomialZSq 0 = 0 := by
  erw [divisionPolynomialZSq_ofNat, zero_pow two_ne_zero, zero_mul]

@[simp]
lemma divisionPolynomialZSq_one : W.divisionPolynomialZSq 1 = 1 := by
  erw [divisionPolynomialZSq_ofNat, one_pow, mul_one]

@[simp]
lemma divisionPolynomialZSq_two : W.divisionPolynomialZSq 2 = W.divisionPolynomial2Sq := by
  erw [divisionPolynomialZSq_ofNat, one_pow, one_mul, if_pos even_two]

@[simp]
lemma divisionPolynomialZSq_three : W.divisionPolynomialZSq 3 = W.divisionPolynomial' 3 ^ 2 := by
  erw [divisionPolynomialZSq_ofNat, mul_one]

@[simp]
lemma divisionPolynomialZSq_four : W.divisionPolynomialZSq 4 =
    W.divisionPolynomial' 4 ^ 2 * W.divisionPolynomial2Sq := by
  erw [divisionPolynomialZSq_ofNat, if_pos <| by decide]

@[simp]
lemma divisionPolynomialZSq_neg (n : ℤ) :
    W.divisionPolynomialZSq (-n) = W.divisionPolynomialZSq n := by
  rw [divisionPolynomialZSq, divisionPolynomial_neg, neg_sq, Int.natAbs_neg, divisionPolynomialZSq]

/-! ### The univariate polynomials congruent to $\phi_n$ for $n \in \mathbb{Z}$ -/

/-- The univariate polynomials congruent under $R[W]$ to the bivariate polynomials $\phi_n$ defined
in terms of the $n$-division polynomials $\psi_n$ for $n \in \mathbb{Z}$. -/
noncomputable def divisionPolynomialX (n : ℤ) : R[X] :=
  X * W.divisionPolynomialZSq n - W.divisionPolynomial (n + 1) * W.divisionPolynomial (n - 1) *
    if Even n.natAbs then 1 else W.divisionPolynomial2Sq

@[simp]
lemma divisionPolynomialX_ofNat (n : ℕ) : W.divisionPolynomialX (n + 1) =
    X * W.divisionPolynomial' (n + 1) ^ 2 *
      (if Even n then 1 else W.divisionPolynomial2Sq) -
    W.divisionPolynomial' (n + 2) * W.divisionPolynomial' n *
      (if Even n then W.divisionPolynomial2Sq else 1) := by
  erw [divisionPolynomialX, divisionPolynomialZSq_ofNat, ← mul_assoc, divisionPolynomial_ofNat,
    add_sub_cancel_right, divisionPolynomial_ofNat, Int.natAbs_cast]
  simp only [Nat.even_add_one, ite_not]

@[simp]
lemma divisionPolynomialX_zero : W.divisionPolynomialX 0 = 1 := by
  rw [divisionPolynomialX, divisionPolynomialZSq_zero, mul_zero, zero_sub, zero_add,
    divisionPolynomial_one, one_mul, zero_sub, divisionPolynomial_neg, divisionPolynomial_one,
    neg_one_mul, neg_neg, if_pos even_zero.natAbs]

@[simp]
lemma divisionPolynomialX_one : W.divisionPolynomialX 1 = X := by
  erw [divisionPolynomialX_ofNat, one_pow, mul_one, mul_one, mul_zero, zero_mul, sub_zero]

@[simp]
lemma divisionPolynomialX_two : W.divisionPolynomialX 2 =
    X ^ 4 - C W.b₄ * X ^ 2 - C (2 * W.b₆) * X - C W.b₈ := by
  erw [divisionPolynomialX_ofNat, divisionPolynomial'_two, if_neg Nat.not_even_one,
    divisionPolynomial2Sq, divisionPolynomial'_three, if_neg Nat.not_even_one]
  C_simp
  ring1

@[simp]
lemma divisionPolynomialX_three : W.divisionPolynomialX 3 =
    X * W.divisionPolynomial' 3 ^ 2 - W.divisionPolynomial' 4 * W.divisionPolynomial2Sq := by
  erw [divisionPolynomialX_ofNat, divisionPolynomial'_three, mul_one, mul_one, if_pos even_two]

@[simp]
lemma divisionPolynomialX_four : W.divisionPolynomialX 4 =
    X * W.divisionPolynomial' 4 ^ 2 * W.divisionPolynomial2Sq - W.divisionPolynomial' 3 *
      (W.divisionPolynomial' 4 * W.divisionPolynomial2Sq ^ 2 - W.divisionPolynomial' 3 ^ 3) := by
  erw [divisionPolynomialX_ofNat, if_neg <| by decide, if_neg <| by decide,
    show 3 + 2 = 2 * 2 + 1 by rfl, divisionPolynomial'_odd, divisionPolynomial'_two,
    if_pos even_zero, if_pos even_zero]
  ring1

@[simp]
lemma divisionPolynomialX_neg (n : ℤ) : W.divisionPolynomialX (-n) = W.divisionPolynomialX n := by
  rw [divisionPolynomialX, divisionPolynomialZSq_neg, neg_add_eq_sub, ← neg_sub n,
    divisionPolynomial_neg, ← neg_add', divisionPolynomial_neg, neg_mul_neg,
    mul_comm <| W.divisionPolynomial _, Int.natAbs_neg, divisionPolynomialX]

/-! ### The bivariate $n$-division polynomials $\psi_n$ for $n \in \mathbb{Z}$ -/

/-- The bivariate $n$-division polynomials $\psi_n$ for $n \in \mathbb{Z}$. -/
noncomputable def divisionPolynomialZ (n : ℤ) : R[X][Y] :=
  C (W.divisionPolynomial n) * if Even n.natAbs then Y - W.toAffine.negPolynomial else 1

@[simp]
lemma divisionPolynomialZ_ofNat (n : ℕ) : W.divisionPolynomialZ n =
    C (W.divisionPolynomial' n) * if Even n then Y - W.toAffine.negPolynomial else 1 := by
  rw [divisionPolynomialZ, divisionPolynomial_ofNat, Int.natAbs_cast]

@[simp]
lemma divisionPolynomialZ_zero : W.divisionPolynomialZ 0 = 0 := by
  erw [divisionPolynomialZ_ofNat, C_0, zero_mul]

@[simp]
lemma divisionPolynomialZ_one : W.divisionPolynomialZ 1 = 1 := by
  erw [divisionPolynomialZ_ofNat, C_1, mul_one]

@[simp]
lemma divisionPolynomialZ_two : W.divisionPolynomialZ 2 = Y - W.toAffine.negPolynomial := by
  erw [divisionPolynomialZ_ofNat, one_mul, if_pos even_two]

@[simp]
lemma divisionPolynomialZ_three : W.divisionPolynomialZ 3 = C (W.divisionPolynomial' 3) := by
  erw [divisionPolynomialZ_ofNat, mul_one]

@[simp]
lemma divisionPolynomialZ_four : W.divisionPolynomialZ 4 =
    C (W.divisionPolynomial' 4) * (Y - W.toAffine.negPolynomial) := by
  erw [divisionPolynomialZ_ofNat, if_pos <| by decide]

@[simp]
lemma divisionPolynomialZ_neg (n : ℤ) : W.divisionPolynomialZ (-n) = -W.divisionPolynomialZ n := by
  rw [divisionPolynomialZ, divisionPolynomial_neg, C_neg, neg_mul (α := R[X][Y]), Int.natAbs_neg,
    divisionPolynomialZ]

end WeierstrassCurve
