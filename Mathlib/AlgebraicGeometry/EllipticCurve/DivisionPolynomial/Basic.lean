/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Division polynomials of Weierstrass curves

This file defines certain polynomials associated to division polynomials of Weierstrass curves.
These are defined in terms of the auxiliary sequences of normalised elliptic divisibility sequences
defined in `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

## Mathematical background

Let $W$ be a Weierstrass curve over a commutative ring $R$. The sequence of $n$-division polynomials
$\psi_n \in R[X, Y]$ of $W$ is the normalised elliptic divisibility sequence with initial values
 * $\psi_0 := 0$,
 * $\psi_1 := 1$,
 * $\psi_2 := 2Y + a_1X + a_3$,
 * $\psi_3 := 3X^4 + b_2X^3 + 3b_4X ^ 2 + 3b_6X + b_8$, and
 * $\psi_4 := \psi_2 \cdot
    (2X^6 + b_2X^5 + 5b_4X^4 + 10b_6X^3 + 10b_8X^2 + (b_2b_8 - b_4b_6)X + (b_4b_8 - b_6^2))$.

Furthermore, define the associated sequences $\phi_n, \omega_n \in R[X, Y]$ by
 * $\phi_n := X\psi_n^2 - \psi_{n + 1}\psi_{n - 1}$, and
 * $\omega_n := \tfrac{1}{2} \cdot (\psi_{2n} / \psi_n - \psi_n(a_1\phi_n + a_3\psi_n^2))$.

Note that $\omega_n$ is always well-defined as a polynomial. As a start, it can be shown by
induction that $\psi_n$ always divides $\psi_{2n}$, so that $\psi_{2n} / \psi_n$ is always
well-defined as a polynomial, while division by 2 is well-defined when $R$ has characteristic
different from 2. In general, it can be shown that 2 always divides the polynomial
$\psi_{2n} / \psi_n - \psi_n(a_1\phi_n + a_3\psi_n^2)$ in the characteristic zero universal ring
$\mathbb{Z}[A_i][X, Y]$ of $W$, where $A_i$ are indeterminates. Then $\omega_n$ can be equivalently
defined as its image under the associated universal morphism $\mathbb{Z}[A_i][X, Y] \to R[X, Y]$.

Now, in the coordinate ring $R[W]$, note that $\psi_2^2$ is congruent to the polynomial
$\Psi_2^{[2]} := 4X^3 + b_2X^2 + 2b_4X + b_6 \in R[X]$. As such, in $R[W]$, the recurrences
associated to a normalised elliptic divisibility sequence show that $\psi_n / \psi_2$ are congruent
to certain polynomials in $R[X]$. In particular, define $\tilde{\Psi}_n \in R[X]$ as the auxiliary
sequence for a normalised elliptic divisibility sequence with initial values
 * $\tilde{\Psi}_0 := 0$,
 * $\tilde{\Psi}_1 := 1$,
 * $\tilde{\Psi}_2 := 1$,
 * $\tilde{\Psi}_3 := \psi_3$, and
 * $\tilde{\Psi}_4 := \psi_4 / \psi_2$.

The corresponding normalised elliptic divisibility sequence $\Psi_n \in R[X, Y]$ is then given by
 * $\Psi_n := \tilde{\Psi}_n\psi_2$ if $n$ is even, and
 * $\Psi_n := \tilde{\Psi}_n$ if $n$ is odd.

Furthermore, define the associated sequences $\Psi_n^{[2]}, \Phi_n \in R[X]$ by
 * $\Psi_n^{[2]} := \tilde{\Psi}_n^2\Psi_2^{[2]}$ if $n$ is even,
 * $\Psi_n^{[2]} := \tilde{\Psi}_n^2$ if $n$ is odd,
 * $\Phi_n := X\Psi_n^{[2]} - \tilde{\Psi}_{n + 1}\tilde{\Psi}_{n - 1}$ if $n$ is even, and
 * $\Phi_n := X\Psi_n^{[2]} - \tilde{\Psi}_{n + 1}\tilde{\Psi}_{n - 1}\Psi_2^{[2]}$ if $n$ is odd.

With these definitions in mind, $\psi_n \in R[X, Y]$ and $\phi_n \in R[X, Y]$ are congruent in
$R[W]$ to $\Psi_n \in R[X, Y]$ and $\Phi_n \in R[X]$ respectively, which are defined in terms of
$\Psi_2^{[2]} \in R[X]$ and $\tilde{\Psi}_n \in R[X]$.

## Main definitions

 * `WeierstrassCurve.preΨ`: the univariate polynomials $\tilde{\Psi}_n$.
 * `WeierstrassCurve.ΨSq`: the univariate polynomials $\Psi_n^{[2]}$.
 * `WeierstrassCurve.Ψ`: the bivariate polynomials $\Psi_n$.
 * `WeierstrassCurve.Φ`: the univariate polynomials $\Phi_n$.
 * `WeierstrassCurve.ψ`: the bivariate $n$-division polynomials $\psi_n$.
 * `WeierstrassCurve.φ`: the bivariate polynomials $\phi_n$.
 * TODO: the bivariate polynomials $\omega_n$.

## Implementation notes

Analogously to `Mathlib.NumberTheory.EllipticDivisibilitySequence`, the $n$-division bivariate
polynomials $\Psi_n$ are defined in terms of the univariate polynomials $\tilde{\Psi}_n$. This is
done partially to avoid ring division, but more crucially to allow the definition of $\Psi_n^{[2]}$
and $\Phi_n$ as univariate polynomials without needing to work under the coordinate ring, and to
allow the computation of their leading terms without ambiguity. Furthermore, evaluating these
polynomials at a rational point on $W$ recovers their original definition up to linear combinations
of the Weierstrass equation of $W$, hence also avoiding the need to work under the coordinate ring.

TODO: implementation notes for the definition of $\omega_n$.

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

section Ψ₂Sq

/-! ### The univariate polynomial $\Psi_2^{[2]}$ -/

/-- The $2$-division polynomial $\psi_2 = \Psi_2$. -/
noncomputable def ψ₂ : R[X][Y] :=
  W.toAffine.polynomialY

/-- The univariate polynomial $\Psi_2^{[2]}$ congruent to $\psi_2^2$. -/
noncomputable def Ψ₂Sq : R[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

lemma C_Ψ₂Sq_eq : C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial := by
  rw [Ψ₂Sq, ψ₂, b₂, b₄, b₆, Affine.polynomialY, Affine.polynomial]
  C_simp
  ring1

-- TODO: remove `twoTorsionPolynomial` in favour of `Ψ₂Sq`
lemma Ψ₂Sq_eq : W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly :=
  rfl

end Ψ₂Sq

section preΨ'

/-! ### The univariate polynomials $\tilde{\Psi}_n$ for $n \in \mathbb{N}$ -/

/-- The $3$-division polynomial $\psi_3 = \Psi_3$. -/
noncomputable def Ψ₃ : R[X] :=
  3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈

/-- The univariate polynomial $\tilde{\Psi}_4$, which is auxiliary to the $4$-division polynomial
$\psi_4 = \Psi_4 = \tilde{\Psi}_4\psi_2$. -/
noncomputable def preΨ₄ : R[X] :=
  2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)

/-- The univariate polynomials $\tilde{\Psi}_n$ for $n \in \mathbb{N}$, which are auxiliary to the
bivariate polynomials $\Psi_n$ congruent to the bivariate $n$-division polynomials $\psi_n$. -/
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

lemma preΨ'_odd (m : ℕ) : W.preΨ' (2 * (m + 2) + 1) =
    W.preΨ' (m + 4) * W.preΨ' (m + 2) ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=
  preNormEDS'_odd ..

lemma preΨ'_even (m : ℕ) : W.preΨ' (2 * (m + 3)) =
    W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 3) * W.preΨ' (m + 5) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) * W.preΨ' (m + 4) ^ 2 :=
  preNormEDS'_even ..

end preΨ'

section preΨ

/-! ### The univariate polynomials $\tilde{\Psi}_n$ for $n \in \mathbb{Z}$ -/

/-- The univariate polynomials $\tilde{\Psi}_n$ for $n \in \mathbb{Z}$, which are auxiliary to the
bivariate polynomials $\Psi_n$ congruent to the bivariate $n$-division polynomials $\psi_n$. -/
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

lemma preΨ_odd (m : ℕ) : W.preΨ (2 * (m + 2) + 1) =
    W.preΨ (m + 4) * W.preΨ (m + 2) ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ (m + 1) * W.preΨ (m + 3) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=
  preNormEDS_odd ..

lemma preΨ_even (m : ℕ) : W.preΨ (2 * (m + 3)) =
    W.preΨ (m + 2) ^ 2 * W.preΨ (m + 3) * W.preΨ (m + 5) -
      W.preΨ (m + 1) * W.preΨ (m + 3) * W.preΨ (m + 4) ^ 2 :=
  preNormEDS_even ..

@[simp]
lemma preΨ_neg (n : ℤ) : W.preΨ (-n) = -W.preΨ n :=
  preNormEDS_neg ..

end preΨ

section ΨSq

/-! ### The univariate polynomials $\Psi_n^{[2]}$ -/

/-- The univariate polynomials $\Psi_n^{[2]}$ congruent to $\psi_n^2$. -/
noncomputable def ΨSq (n : ℤ) : R[X] :=
  W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1

@[simp]
lemma ΨSq_ofNat (n : ℕ) : W.ΨSq n = W.preΨ' n ^ 2 * if Even n then W.Ψ₂Sq else 1 := by
  simp only [ΨSq, preΨ_ofNat, Int.even_coe_nat]

@[simp]
lemma ΨSq_zero : W.ΨSq 0 = 0 := by
  erw [ΨSq_ofNat, preΨ'_zero, zero_pow two_ne_zero, zero_mul]

@[simp]
lemma ΨSq_one : W.ΨSq 1 = 1 := by
  erw [ΨSq_ofNat, preΨ'_one, one_pow, mul_one]

@[simp]
lemma ΨSq_two : W.ΨSq 2 = W.Ψ₂Sq := by
  erw [ΨSq_ofNat, preΨ'_two, one_pow, one_mul, if_pos even_two]

@[simp]
lemma ΨSq_three : W.ΨSq 3 = W.Ψ₃ ^ 2 := by
  erw [ΨSq_ofNat, preΨ'_three, mul_one]

@[simp]
lemma ΨSq_four : W.ΨSq 4 = W.preΨ₄ ^ 2 * W.Ψ₂Sq := by
  erw [ΨSq_ofNat, preΨ'_four, if_pos <| by decide]

lemma ΨSq_odd (m : ℕ) : W.ΨSq (2 * (m + 2) + 1) =
    (W.preΨ' (m + 4) * W.preΨ' (m + 2) ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2)) ^ 2 := by
  erw [ΨSq_ofNat, preΨ'_odd, if_neg (m + 2).not_even_two_mul_add_one, mul_one]

lemma ΨSq_even (m : ℕ) : W.ΨSq (2 * (m + 3)) =
    (W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 3) * W.preΨ' (m + 5) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) * W.preΨ' (m + 4) ^ 2) ^ 2 * W.Ψ₂Sq := by
  erw [ΨSq_ofNat, preΨ'_even, if_pos <| even_two_mul _]

@[simp]
lemma ΨSq_neg (n : ℤ) : W.ΨSq (-n) = W.ΨSq n := by
  simp only [ΨSq, preΨ_neg, neg_sq, even_neg]

end ΨSq

section Ψ

/-! ### The bivariate polynomials $\Psi_n$ -/

/-- The bivariate polynomials $\Psi_n$ congruent to the $n$-division polynomials $\psi_n$. -/
protected noncomputable def Ψ (n : ℤ) : R[X][Y] :=
  C (W.preΨ n) * if Even n then W.ψ₂ else 1

open WeierstrassCurve (Ψ)

@[simp]
lemma Ψ_ofNat (n : ℕ) : W.Ψ n = C (W.preΨ' n) * if Even n then W.ψ₂ else 1 := by
  simp only [Ψ, preΨ_ofNat, Int.even_coe_nat]

@[simp]
lemma Ψ_zero : W.Ψ 0 = 0 := by
  erw [Ψ_ofNat, preΨ'_zero, C_0, zero_mul]

@[simp]
lemma Ψ_one : W.Ψ 1 = 1 := by
  erw [Ψ_ofNat, preΨ'_one, C_1, mul_one]

@[simp]
lemma Ψ_two : W.Ψ 2 = W.ψ₂ := by
  erw [Ψ_ofNat, preΨ'_two, one_mul, if_pos even_two]

@[simp]
lemma Ψ_three : W.Ψ 3 = C W.Ψ₃ := by
  erw [Ψ_ofNat, preΨ'_three, mul_one]

@[simp]
lemma Ψ_four : W.Ψ 4 = C W.preΨ₄ * W.ψ₂ := by
  erw [Ψ_ofNat, preΨ'_four, if_pos <| by decide]

lemma Ψ_odd (m : ℕ) : W.Ψ (2 * (m + 2) + 1) =
    W.Ψ (m + 4) * W.Ψ (m + 2) ^ 3 - W.Ψ (m + 1) * W.Ψ (m + 3) ^ 3 +
      W.toAffine.polynomial * (16 * W.toAffine.polynomial - 8 * W.ψ₂ ^ 2) * C
        (if Even m then W.preΨ' (m + 4) * W.preΨ' (m + 2) ^ 3
          else -W.preΨ' (m + 1) * W.preΨ' (m + 3) ^ 3) := by
  repeat erw [Ψ_ofNat]
  simp_rw [preΨ'_odd, if_neg (m + 2).not_even_two_mul_add_one, Nat.even_add_one, ite_not]
  split_ifs <;> C_simp <;> rw [C_Ψ₂Sq_eq] <;> ring1

lemma Ψ_even (m : ℕ) : W.Ψ (2 * (m + 3)) * W.ψ₂ =
    W.Ψ (m + 2) ^ 2 * W.Ψ (m + 3) * W.Ψ (m + 5) - W.Ψ (m + 1) * W.Ψ (m + 3) * W.Ψ (m + 4) ^ 2 := by
  repeat erw [Ψ_ofNat]
  simp_rw [preΨ'_even, if_pos <| even_two_mul _, Nat.even_add_one, ite_not]
  split_ifs <;> C_simp <;> ring1

@[simp]
lemma Ψ_neg (n : ℤ) : W.Ψ (-n) = -W.Ψ n := by
  simp only [Ψ, preΨ_neg, C_neg, neg_mul (α := R[X][Y]), even_neg]

end Ψ

section Φ

/-! ### The univariate polynomials $\Phi_n$ -/

/-- The univariate polynomials $\Phi_n$ congruent to $\phi_n$. -/
protected noncomputable def Φ (n : ℤ) : R[X] :=
  X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq

open WeierstrassCurve (Φ)

@[simp]
lemma Φ_ofNat (n : ℕ) : W.Φ (n + 1) =
    X * W.preΨ' (n + 1) ^ 2 * (if Even n then 1 else W.Ψ₂Sq) -
      W.preΨ' (n + 2) * W.preΨ' n * (if Even n then W.Ψ₂Sq else 1) := by
  erw [Φ, ΨSq_ofNat, ← mul_assoc, preΨ_ofNat, add_sub_cancel_right, preΨ_ofNat]
  simp only [Nat.even_add_one, Int.even_add_one, Int.even_coe_nat, ite_not]

@[simp]
lemma Φ_zero : W.Φ 0 = 1 := by
  rw [Φ, ΨSq_zero, mul_zero, zero_sub, zero_add, preΨ_one, one_mul, zero_sub, preΨ_neg, preΨ_one,
    neg_one_mul, neg_neg, if_pos even_zero]

@[simp]
lemma Φ_one : W.Φ 1 = X := by
  erw [Φ_ofNat, preΨ'_one, one_pow, mul_one, mul_one, preΨ'_zero, mul_zero, zero_mul, sub_zero]

@[simp]
lemma Φ_two : W.Φ 2 = X ^ 4 - C W.b₄ * X ^ 2 - C (2 * W.b₆) * X - C W.b₈ := by
  erw [Φ_ofNat, preΨ'_two, if_neg Nat.not_even_one, Ψ₂Sq, preΨ'_three, preΨ'_one, mul_one, Ψ₃]
  C_simp
  ring1

@[simp]
lemma Φ_three : W.Φ 3 = X * W.Ψ₃ ^ 2 - W.preΨ₄ * W.Ψ₂Sq := by
  erw [Φ_ofNat, preΨ'_three, mul_one, preΨ'_four, preΨ'_two, mul_one, if_pos even_two]

@[simp]
lemma Φ_four : W.Φ 4 = X * W.preΨ₄ ^ 2 * W.Ψ₂Sq - W.Ψ₃ * (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) := by
  erw [Φ_ofNat, preΨ'_four, if_neg <| by decide, show 3 + 2 = 2 * 2 + 1 by rfl, preΨ'_odd,
    preΨ'_four, preΨ'_two, if_pos even_zero, preΨ'_one, preΨ'_three, if_pos even_zero]
  ring1

@[simp]
lemma Φ_neg (n : ℤ) : W.Φ (-n) = W.Φ n := by
  simp only [Φ, ΨSq_neg, neg_add_eq_sub, ← neg_sub n, preΨ_neg, ← neg_add', preΨ_neg, neg_mul_neg,
    mul_comm <| W.preΨ <| n - 1, even_neg]

end Φ

section ψ

/-! ### The bivariate polynomials $\psi_n$ -/

/-- The bivariate $n$-division polynomials $\psi_n$. -/
protected noncomputable def ψ (n : ℤ) : R[X][Y] :=
  normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

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

lemma ψ_odd (m : ℕ) : W.ψ (2 * (m + 2) + 1) =
    W.ψ (m + 4) * W.ψ (m + 2) ^ 3 - W.ψ (m + 1) * W.ψ (m + 3) ^ 3 :=
  normEDS_odd ..

lemma ψ_even (m : ℕ) : W.ψ (2 * (m + 3)) * W.ψ₂ =
    W.ψ (m + 2) ^ 2 * W.ψ (m + 3) * W.ψ (m + 5) - W.ψ (m + 1) * W.ψ (m + 3) * W.ψ (m + 4) ^ 2 :=
  normEDS_even ..

@[simp]
lemma ψ_neg (n : ℤ) : W.ψ (-n) = -W.ψ n :=
  normEDS_neg ..

end ψ

section φ

/-! ### The bivariate polynomials $\phi_n$ -/

/-- The bivariate polynomials $\phi_n$. -/
protected noncomputable def φ (n : ℤ) : R[X][Y] :=
  C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)

open WeierstrassCurve (φ)

@[simp]
lemma φ_zero : W.φ 0 = 1 := by
  erw [φ, ψ_zero, zero_pow two_ne_zero, mul_zero, zero_sub, ψ_one, one_mul,
    zero_sub, ψ_neg, neg_neg, ψ_one]

@[simp]
lemma φ_one : W.φ 1 = C X := by
  erw [φ, ψ_one, one_pow, mul_one, ψ_zero, mul_zero, sub_zero]

@[simp]
lemma φ_two : W.φ 2 = C X * W.ψ₂ ^ 2 - C W.Ψ₃ := by
  erw [φ, ψ_two, ψ_three, ψ_one, mul_one]

@[simp]
lemma φ_three : W.φ 3 = C X * C W.Ψ₃ ^ 2 - C W.preΨ₄ * W.ψ₂ ^ 2 := by
  erw [φ, ψ_three, ψ_four, mul_assoc, ψ_two, ← sq]

@[simp]
lemma φ_four :
    W.φ 4 = C X * C W.preΨ₄ ^ 2 * W.ψ₂ ^ 2 - C W.preΨ₄ * W.ψ₂ ^ 4 * C W.Ψ₃ + C W.Ψ₃ ^ 4 := by
  erw [φ, ψ_four, show (4 + 1 : ℤ) = 2 * 2 + 1 by rfl, ψ_odd, ψ_four, ψ_two, ψ_one, ψ_three]
  ring1

@[simp]
lemma φ_neg (n : ℤ) : W.φ (-n) = W.φ n := by
  rw [φ, ψ_neg, neg_sq (R := R[X][Y]), neg_add_eq_sub, ← neg_sub n, ψ_neg, ← neg_add', ψ_neg,
    neg_mul_neg (α := R[X][Y]), mul_comm <| W.ψ _, φ]

end φ

end WeierstrassCurve
