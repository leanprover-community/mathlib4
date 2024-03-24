/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.Data.Int.Parity
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic.ComputeDegree

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

## Main statements

 * `WeierstrassCurve.natDegree_divisionPolynomial2Sq`: the degree of $\psi_2^2$.
 * `WeierstrassCurve.coeff_divisionPolynomial2Sq`: the leading coefficient of $\psi_2^2$.
 * `WeierstrassCurve.natDegree_divisionPolynomial`: the degree of $\tilde{\psi}_n$.
 * `WeierstrassCurve.coeff_divisionPolynomial`: the leading coefficient of $\tilde{\psi}_n$.
 * `WeierstrassCurve.natDegree_divisionPolynomialX`: the degree of $\phi_n$.
 * `WeierstrassCurve.coeff_divisionPolynomialX`: the leading coefficient of $\phi_n$.
 * `WeierstrassCurve.natDegree_divisionPolynomialZSq`: the degree of $\psi_n^2$.
 * `WeierstrassCurve.coeff_divisionPolynomialZSq`: the leading coefficient of $\psi_n^2$.

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
@[pp_dot]
noncomputable def divisionPolynomial2Sq : R[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

-- TODO: remove `twoTorsionPolynomial` in favour of `divisionPolynomial2Sq`
lemma divisionPolynomial2Sq_eq : W.divisionPolynomial2Sq = W.twoTorsionPolynomial.toPoly :=
  rfl

lemma natDegree_divisionPolynomial2Sq : W.divisionPolynomial2Sq.natDegree ≤ 3 := by
  rw [divisionPolynomial2Sq]
  compute_degree

@[simp]
lemma coeff_divisionPolynomial2Sq : W.divisionPolynomial2Sq.coeff 3 = 4 := by
  rw [divisionPolynomial2Sq]
  compute_degree!

/-! ### The univariate polynomials congruent to $\tilde{\psi}_n$ for $n \in \mathbb{N}$ -/

/-- The univariate polynomials congruent under $R[W]$ to the bivariate auxiliary polynomials
$\tilde{\psi}_n$ associated to the $n$-division polynomials $\psi_n$ for $n \in \mathbb{N}$. -/
@[pp_dot]
noncomputable def divisionPolynomial' (n : ℕ) : R[X] :=
  preNormEDS' (W.divisionPolynomial2Sq ^ 2)
    (C 3 * X ^ 4 + C W.b₂ * X ^ 3 + C (3 * W.b₄) * X ^ 2 + C (3 * W.b₆) * X + C W.b₈)
    (C 2 * X ^ 6 + C W.b₂ * X ^ 5 + C (5 * W.b₄) * X ^ 4 + C (10 * W.b₆) * X ^ 3
      + C (10 * W.b₈) * X ^ 2 + C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)) n

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
    C 3 * X ^ 4 + C W.b₂ * X ^ 3 + C (3 * W.b₄) * X ^ 2 + C (3 * W.b₆) * X + C W.b₈ :=
  preNormEDS'_three ..

@[simp]
lemma divisionPolynomial'_four : W.divisionPolynomial' 4 =
    C 2 * X ^ 6 + C W.b₂ * X ^ 5 + C (5 * W.b₄) * X ^ 4 + C (10 * W.b₆) * X ^ 3
      + C (10 * W.b₈) * X ^ 2 + C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2) :=
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

private lemma natDegree_divisionPolynomial'_zero : (W.divisionPolynomial' 0).natDegree = 0 := by
  rw [divisionPolynomial'_zero, natDegree_zero]

private lemma coeff_divisionPolynomial'_zero : (W.divisionPolynomial' 0).coeff 0 = 0 := by
  rw [divisionPolynomial'_zero, coeff_zero]

private lemma natDegree_divisionPolynomial'_one : (W.divisionPolynomial' 1).natDegree = 0 := by
  rw [divisionPolynomial'_one, natDegree_one]

private lemma coeff_divisionPolynomial'_one : (W.divisionPolynomial' 1).coeff 0 = 1 := by
  rw [divisionPolynomial'_one, coeff_one_zero]

private lemma natDegree_divisionPolynomial'_two : (W.divisionPolynomial' 2).natDegree = 0 := by
  rw [divisionPolynomial'_two, natDegree_one]

private lemma coeff_divisionPolynomial'_two : (W.divisionPolynomial' 2).coeff 0 = 1 := by
  rw [divisionPolynomial'_two, coeff_one_zero]

private lemma natDegree_divisionPolynomial'_three : (W.divisionPolynomial' 3).natDegree ≤ 4 := by
  rw [divisionPolynomial'_three]
  compute_degree

private lemma coeff_divisionPolynomial'_three : (W.divisionPolynomial' 3).coeff 4 = 3 := by
  rw [divisionPolynomial'_three]
  compute_degree!

private lemma natDegree_divisionPolynomial'_four : (W.divisionPolynomial' 4).natDegree ≤ 6 := by
  rw [divisionPolynomial'_four]
  compute_degree

private lemma coeff_divisionPolynomial'_four : (W.divisionPolynomial' 4).coeff 6 = 2 := by
  rw [divisionPolynomial'_four]
  compute_degree!

private lemma natDegree_divisionPolynomial'_five : (W.divisionPolynomial' 5).natDegree ≤ 12 := by
  rw [show 5 = 2 * 2 + 1 by rfl, divisionPolynomial'_odd, divisionPolynomial2Sq]
  simp
  compute_degree

private lemma coeff_divisionPolynomial'_five : (W.divisionPolynomial' 5).coeff 12 = 5 := by
  rw [show 5 = 2 * 2 + 1 by rfl, divisionPolynomial'_odd, divisionPolynomial2Sq]
  simp [-coeff_sub]
  compute_degree!

private lemma natDegree_divisionPolynomial'_six : (W.divisionPolynomial' 6).natDegree ≤ 16 := by
  rw [show 6 = 2 * 3 by rfl, divisionPolynomial'_even, show 0 + 5 = 2 * 2 + 1 by rfl,
    divisionPolynomial'_odd, divisionPolynomial2Sq]
  simp
  compute_degree

private lemma coeff_divisionPolynomial'_six : (W.divisionPolynomial' 6).coeff 16 = 3 := by
  rw [show 6 = 2 * 3 by rfl, divisionPolynomial'_even, show 0 + 5 = 2 * 2 + 1 by rfl,
    divisionPolynomial'_odd, divisionPolynomial2Sq]
  simp [-coeff_sub]
  compute_degree!

private lemma natDegree_divisionPolynomial'_eight : (W.divisionPolynomial' 8).natDegree ≤ 30 := by
  rw [show 8 = 2 * 4 by rfl, divisionPolynomial'_even, show 1 + 5 = 2 * 3 by rfl,
    divisionPolynomial'_even, show 0 + 5 = 2 * 2 + 1 by rfl, divisionPolynomial'_odd,
    divisionPolynomial2Sq]
  simp
  compute_degree

private lemma coeff_divisionPolynomial'_eight : (W.divisionPolynomial' 8).coeff 30 = 4 := by
  rw [show 8 = 2 * 4 by rfl, divisionPolynomial'_even, show 1 + 5 = 2 * 3 by rfl,
    divisionPolynomial'_even, show 0 + 5 = 2 * 2 + 1 by rfl, divisionPolynomial'_odd,
    divisionPolynomial2Sq]
  simp [-coeff_sub]
  compute_degree!

section Inductive

variable {W} (m : ℕ) (ih : ∀ k < 2 * m + 2,
  ((W.divisionPolynomial' <| 2 * k).natDegree ≤ 2 * k ^ 2 - 2 ∧
    (W.divisionPolynomial' <| 2 * k).coeff (2 * k ^ 2 - 2) = k) ∧
  ((W.divisionPolynomial' <| 2 * k + 1).natDegree ≤ 2 * k ^ 2 + 2 * k ∧
    (W.divisionPolynomial' <| 2 * k + 1).coeff (2 * k ^ 2 + 2 * k) = (2 * k + 1 : ℕ)))

private lemma natDegree_divisionPolynomial'_add_one :
    (W.divisionPolynomial' <| 2 * m + 1).natDegree ≤ 2 * m * (m + 1) := by
  convert (ih m <| by linarith only).right.left using 1
  ring1

private lemma coeff_divisionPolynomial'_add_one :
    (W.divisionPolynomial' <| 2 * m + 1).coeff (2 * m * (m + 1)) = (2 * m + 1 : ℕ) := by
  convert (ih m <| by linarith only).right.right using 2
  ring1

private lemma natDegree_divisionPolynomial'_add_two :
    (W.divisionPolynomial' <| 2 * m + 2).natDegree ≤ 2 * m * (m + 2) := by
  convert (ih (m + 1) <| by linarith only).left.left using 1
  rw [show 2 * (m + 1) ^ 2 = 2 * m * (m + 2) + 2 by ring1, Nat.add_sub_cancel]

private lemma coeff_divisionPolynomial'_add_two :
    (W.divisionPolynomial' <| 2 * m + 2).coeff (2 * m * (m + 2)) = (m + 1 : ℕ) := by
  convert (ih (m + 1) <| by linarith only).left.right using 2
  rw [show 2 * (m + 1) ^ 2 = 2 * m * (m + 2) + 2 by ring1, Nat.add_sub_cancel]

private lemma natDegree_divisionPolynomial'_add_three :
    (W.divisionPolynomial' <| 2 * m + 3).natDegree ≤ 2 * (m + 1) * (m + 2) := by
  convert (ih (m + 1) <| by linarith only).right.left using 1
  ring1

private lemma coeff_divisionPolynomial'_add_three :
    (W.divisionPolynomial' <| 2 * m + 3).coeff (2 * (m + 1) * (m + 2)) = (2 * m + 3 : ℕ) := by
  convert (ih (m + 1) <| by linarith only).right.right using 2
  ring1

private lemma natDegree_divisionPolynomial'_add_four :
    (W.divisionPolynomial' <| 2 * m + 4).natDegree ≤ 2 * (m + 1) * (m + 3) := by
  rcases m with _ | m
  · exact W.natDegree_divisionPolynomial'_four
  · convert (ih (m + 3) <| by linarith only).left.left using 1
    rw [show 2 * (m + 3) ^ 2 = 2 * (m + 2) * (m + 4) + 2 by ring1, Nat.add_sub_cancel]

private lemma coeff_divisionPolynomial'_add_four :
    (W.divisionPolynomial' <| 2 * m + 4).coeff (2 * (m + 1) * (m + 3)) = (m + 2 : ℕ) := by
  rcases m with _ | m
  · exact W.coeff_divisionPolynomial'_four
  · convert (ih (m + 3) <| by linarith only).left.right using 2
    rw [show 2 * (m + 3) ^ 2 = 2 * (m + 2) * (m + 4) + 2 by ring1, Nat.add_sub_cancel]

private lemma natDegree_divisionPolynomial'_add_five :
    (W.divisionPolynomial' <| 2 * m + 5).natDegree ≤ 2 * (m + 2) * (m + 3) := by
  rcases m with _ | m
  · exact W.natDegree_divisionPolynomial'_five
  · convert (ih (m + 3) <| by linarith only).right.left using 1
    rw [← Nat.add_one]
    ring1

private lemma coeff_divisionPolynomial'_add_five :
    (W.divisionPolynomial' <| 2 * m + 5).coeff (2 * (m + 2) * (m + 3)) = (2 * m + 5 : ℕ) := by
  rcases m with _ | m
  · exact W.coeff_divisionPolynomial'_five
  · convert (ih (m + 3) <| by linarith only).right.right using 2
    rw [← Nat.add_one]
    ring1

private lemma natDegree_divisionPolynomial'_add_six :
    (W.divisionPolynomial' <| 2 * m + 6).natDegree ≤ 2 * (m + 2) * (m + 4) := by
  rcases m with _ | _ | m
  · exact W.natDegree_divisionPolynomial'_six
  · exact W.natDegree_divisionPolynomial'_eight
  · convert (ih (m + 5) <| by linarith only).left.left using 1
    rw [show 2 * (m + 5) ^ 2 = 2 * (m + 4) * (m + 6) + 2 by ring1, Nat.add_sub_cancel]

private lemma coeff_divisionPolynomial'_add_six :
    (W.divisionPolynomial' <| 2 * m + 6).coeff (2 * (m + 2) * (m + 4)) = (m + 3 : ℕ) := by
  rcases m with _ | _ | m
  · exact W.coeff_divisionPolynomial'_six
  · exact W.coeff_divisionPolynomial'_eight
  · convert (ih (m + 5) <| by linarith only).left.right using 2
    rw [show 2 * (m + 5) ^ 2 = 2 * (m + 4) * (m + 6) + 2 by ring1, Nat.add_sub_cancel]

private lemma natDegree_odd {a b c d e f : R[X]} {da db dc dd de df n : ℕ}
    (ha : a.natDegree ≤ da) (hb : b.natDegree ≤ db) (hc : c.natDegree ≤ dc)
    (hd : d.natDegree ≤ dd) (he : e.natDegree ≤ de) (hf : f.natDegree ≤ df)
    (habc : n = da + 3 * db + 2 * dc) (hdef : n = dd + 3 * de + 2 * df) :
    (a * b ^ 3 * c ^ 2 - d * e ^ 3 * f ^ 2).natDegree ≤ n := by
  nth_rw 1 [← max_self n, habc, hdef]
  convert natDegree_sub_le_of_le .. using 1
  · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le ha <| natDegree_pow_le_of_le 3 hb) <|
      natDegree_pow_le_of_le 2 hc
  · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le hd <| natDegree_pow_le_of_le 3 he) <|
      natDegree_pow_le_of_le 2 hf

private lemma natDegree_odd_divisionPolynomial'_even :
    (W.divisionPolynomial' <| 2 * (2 * m + 2) + 1).natDegree ≤ 2 * (2 * m + 2) * (2 * m + 3) := by
  rw [divisionPolynomial'_odd, if_pos <| even_two_mul m, if_pos <| even_two_mul m,
    ← @one_pow R[X] _ 2]
  exact natDegree_odd (natDegree_divisionPolynomial'_add_four m ih)
    (natDegree_divisionPolynomial'_add_two m ih) W.natDegree_divisionPolynomial2Sq
    (natDegree_divisionPolynomial'_add_one m ih) (natDegree_divisionPolynomial'_add_three m ih)
    natDegree_one.le (by ring1) (by ring1)

private lemma natDegree_odd_divisionPolynomial'_odd :
    (W.divisionPolynomial' <| 2 * (2 * m + 3) + 1).natDegree ≤ 2 * (2 * m + 3) * (2 * m + 4) := by
  rw [divisionPolynomial'_odd, if_neg m.not_even_two_mul_add_one, ← @one_pow R[X] _ 2,
    if_neg m.not_even_two_mul_add_one]
  exact natDegree_odd (natDegree_divisionPolynomial'_add_five m ih)
    (natDegree_divisionPolynomial'_add_three m ih) natDegree_one.le
    (natDegree_divisionPolynomial'_add_two m ih) (natDegree_divisionPolynomial'_add_four m ih)
    W.natDegree_divisionPolynomial2Sq (by ring1) (by ring1)

private lemma coeff_odd {a b c d e f : R[X]} {da db dc dd de df n : ℕ}
    (ha : a.natDegree ≤ da) (hb : b.natDegree ≤ db) (hc : c.natDegree ≤ dc)
    (hd : d.natDegree ≤ dd) (he : e.natDegree ≤ de) (hf : f.natDegree ≤ df)
    (habc : n = da + 3 * db + 2 * dc) (hdef : n = dd + 3 * de + 2 * df) :
    (a * b ^ 3 * c ^ 2 - d * e ^ 3 * f ^ 2).coeff n = a.coeff da * b.coeff db ^ 3 * c.coeff dc ^ 2 -
      d.coeff dd * e.coeff de ^ 3 * f.coeff df ^ 2 := by
  rw [coeff_sub, habc, coeff_mul_of_natDegree_le
      (natDegree_mul_le_of_le ha <| natDegree_pow_le_of_le 3 hb) <| natDegree_pow_le_of_le 2 hc,
    coeff_pow_of_natDegree_le hc, coeff_mul_of_natDegree_le ha <| natDegree_pow_le_of_le 3 hb,
    coeff_pow_of_natDegree_le hb, ← habc, hdef, coeff_mul_of_natDegree_le
      (natDegree_mul_le_of_le hd <| natDegree_pow_le_of_le 3 he) <| natDegree_pow_le_of_le 2 hf,
    coeff_mul_of_natDegree_le hd <| natDegree_pow_le_of_le 3 he, coeff_pow_of_natDegree_le he,
    coeff_pow_of_natDegree_le hf]

private lemma coeff_odd_divisionPolynomial'_even :
    (W.divisionPolynomial' <| 2 * (2 * m + 2) + 1).coeff (2 * (2 * m + 2) * (2 * m + 3)) =
      (2 * (2 * m + 2) + 1 : ℕ) := by
  rw [divisionPolynomial'_odd, if_pos <| even_two_mul m, if_pos <| even_two_mul m,
    ← @one_pow R[X] _ 2, coeff_odd (natDegree_divisionPolynomial'_add_four m ih)
      (natDegree_divisionPolynomial'_add_two m ih) W.natDegree_divisionPolynomial2Sq
      (natDegree_divisionPolynomial'_add_one m ih) (natDegree_divisionPolynomial'_add_three m ih)
      natDegree_one.le (by ring1) (by ring1), coeff_divisionPolynomial'_add_four m ih,
    coeff_divisionPolynomial'_add_two m ih, coeff_divisionPolynomial2Sq,
    coeff_divisionPolynomial'_add_one m ih, coeff_divisionPolynomial'_add_three m ih,
    coeff_one_zero]
  push_cast
  ring1

private lemma coeff_odd_divisionPolynomial'_odd :
    (W.divisionPolynomial' <| 2 * (2 * m + 3) + 1).coeff (2 * (2 * m + 3) * (2 * m + 4)) =
      (2 * (2 * m + 3) + 1 : ℕ) := by
  rw [divisionPolynomial'_odd, if_neg m.not_even_two_mul_add_one, ← @one_pow R[X] _ 2,
    if_neg m.not_even_two_mul_add_one, coeff_odd (natDegree_divisionPolynomial'_add_five m ih)
      (natDegree_divisionPolynomial'_add_three m ih) natDegree_one.le
      (natDegree_divisionPolynomial'_add_two m ih) (natDegree_divisionPolynomial'_add_four m ih)
      W.natDegree_divisionPolynomial2Sq (by ring1) (by ring1),
    coeff_divisionPolynomial'_add_five m ih, coeff_divisionPolynomial'_add_three m ih,
    coeff_one_zero, coeff_divisionPolynomial'_add_two m ih, coeff_divisionPolynomial'_add_four m ih,
    coeff_divisionPolynomial2Sq]
  push_cast
  ring1

private lemma natDegree_even {a b c d e f : R[X]} {da db dc dd de df n : ℕ}
    (ha : a.natDegree ≤ da) (hb : b.natDegree ≤ db) (hc : c.natDegree ≤ dc)
    (hd : d.natDegree ≤ dd) (he : e.natDegree ≤ de) (hf : f.natDegree ≤ df)
    (habc : n = 2 * da + db + dc) (hdef : n = dd + de + 2 * df) :
    (a ^ 2 * b * c - d * e * f ^ 2).natDegree ≤ n := by
  nth_rw 1 [← max_self n, habc, hdef]
  convert natDegree_sub_le_of_le .. using 1
  · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 ha) hb) hc
  · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le hd he) <| natDegree_pow_le_of_le 2 hf

private lemma natDegree_even_divisionPolynomial'_even :
    (W.divisionPolynomial' <| 2 * (2 * m + 3)).natDegree ≤ 2 * (2 * m + 2) * (2 * m + 4) := by
  rw [divisionPolynomial'_even]
  exact natDegree_even (natDegree_divisionPolynomial'_add_two m ih)
    (natDegree_divisionPolynomial'_add_three m ih) (natDegree_divisionPolynomial'_add_five m ih)
    (natDegree_divisionPolynomial'_add_one m ih) (natDegree_divisionPolynomial'_add_three m ih)
    (natDegree_divisionPolynomial'_add_four m ih) (by ring1) (by ring1)

private lemma natDegree_even_divisionPolynomial'_odd :
    (W.divisionPolynomial' <| 2 * (2 * m + 4)).natDegree ≤ 2 * (2 * m + 3) * (2 * m + 5) := by
  rw [divisionPolynomial'_even]
  exact natDegree_even (natDegree_divisionPolynomial'_add_three m ih)
    (natDegree_divisionPolynomial'_add_four m ih) (natDegree_divisionPolynomial'_add_six m ih)
    (natDegree_divisionPolynomial'_add_two m ih) (natDegree_divisionPolynomial'_add_four m ih)
    (natDegree_divisionPolynomial'_add_five m ih) (by ring1) (by ring1)

private lemma coeff_even {a b c d e f : R[X]} {da db dc dd de df n : ℕ}
    (ha : a.natDegree ≤ da) (hb : b.natDegree ≤ db) (hc : c.natDegree ≤ dc)
    (hd : d.natDegree ≤ dd) (he : e.natDegree ≤ de) (hf : f.natDegree ≤ df)
    (habc : n = 2 * da + db + dc) (hdef : n = dd + de + 2 * df) :
    (a ^ 2 * b * c - d * e * f ^ 2).coeff n =
      a.coeff da ^ 2 * b.coeff db * c.coeff dc - d.coeff dd * e.coeff de * f.coeff df ^ 2 := by
  rw [coeff_sub, habc, coeff_mul_of_natDegree_le
      (natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 ha) hb) hc,
    coeff_mul_of_natDegree_le (natDegree_pow_le_of_le 2 ha) hb, coeff_pow_of_natDegree_le ha,
    ← habc, hdef, coeff_mul_of_natDegree_le (natDegree_mul_le_of_le hd he) <|
      natDegree_pow_le_of_le 2 hf, coeff_mul_of_natDegree_le hd he, coeff_pow_of_natDegree_le hf]

private lemma coeff_even_divisionPolynomial'_even :
    (W.divisionPolynomial' <| 2 * (2 * m + 3)).coeff (2 * (2 * m + 2) * (2 * m + 4)) =
      (2 * m + 3 : ℕ) := by
  rw [divisionPolynomial'_even, coeff_even (natDegree_divisionPolynomial'_add_two m ih)
      (natDegree_divisionPolynomial'_add_three m ih) (natDegree_divisionPolynomial'_add_five m ih)
      (natDegree_divisionPolynomial'_add_one m ih) (natDegree_divisionPolynomial'_add_three m ih)
      (natDegree_divisionPolynomial'_add_four m ih) (by ring1) (by ring1),
    coeff_divisionPolynomial'_add_two m ih, coeff_divisionPolynomial'_add_three m ih,
    coeff_divisionPolynomial'_add_five m ih, coeff_divisionPolynomial'_add_one m ih,
    coeff_divisionPolynomial'_add_four m ih]
  push_cast
  ring1

private lemma coeff_even_divisionPolynomial'_odd :
    (W.divisionPolynomial' <| 2 * (2 * m + 4)).coeff (2 * (2 * m + 3) * (2 * m + 5)) =
      (2 * m + 4 : ℕ) := by
  rw [divisionPolynomial'_even, coeff_even (natDegree_divisionPolynomial'_add_three m ih)
      (natDegree_divisionPolynomial'_add_four m ih) (natDegree_divisionPolynomial'_add_six m ih)
      (natDegree_divisionPolynomial'_add_two m ih) (natDegree_divisionPolynomial'_add_four m ih)
      (natDegree_divisionPolynomial'_add_five m ih) (by ring1) (by ring1),
    coeff_divisionPolynomial'_add_three m ih, coeff_divisionPolynomial'_add_four m ih,
    coeff_divisionPolynomial'_add_six m ih, coeff_divisionPolynomial'_add_two m ih,
    coeff_divisionPolynomial'_add_five m ih]
  push_cast
  ring1

end Inductive

private lemma natDegree_coeff_divisionPolynomial' (n : ℕ) :
    if Even n then (W.divisionPolynomial' n).natDegree ≤ (n ^ 2 - 4) / 2 ∧
      (W.divisionPolynomial' n).coeff ((n ^ 2 - 4) / 2) = (n / 2 : ℕ)
    else (W.divisionPolynomial' n).natDegree ≤ (n ^ 2 - 1) / 2 ∧
      (W.divisionPolynomial' n).coeff ((n ^ 2 - 1) / 2) = n := by
  induction n using normEDSRec' with
  | base0 => exact ⟨W.natDegree_divisionPolynomial'_zero.le,
    by erw [coeff_divisionPolynomial'_zero, Nat.cast_zero]⟩
  | base1 => exact ⟨W.natDegree_divisionPolynomial'_one.le,
    by erw [coeff_divisionPolynomial'_one, Nat.cast_one]⟩
  | base2 => exact ⟨W.natDegree_divisionPolynomial'_two.le,
    by erw [coeff_divisionPolynomial'_two, Nat.cast_one]⟩
  | base3 => exact ⟨W.natDegree_divisionPolynomial'_three, W.coeff_divisionPolynomial'_three⟩
  | base4 => exact ⟨W.natDegree_divisionPolynomial'_four, W.coeff_divisionPolynomial'_four⟩
  | _ m ih =>
    replace ih (k : ℕ) (hk : k < m + 2) :
        ((W.divisionPolynomial' <| 2 * k).natDegree ≤ 2 * k ^ 2 - 2 ∧
          (W.divisionPolynomial' <| 2 * k).coeff (2 * k ^ 2 - 2) = k) ∧
        ((W.divisionPolynomial' <| 2 * k + 1).natDegree ≤ 2 * k ^ 2 + 2 * k ∧
          (W.divisionPolynomial' <| 2 * k + 1).coeff (2 * k ^ 2 + 2 * k) = (2 * k + 1 : ℕ)) := by
      rw [← show ((2 * k) ^ 2 - 4) / 2 = 2 * k ^ 2 - 2 by
          exact Nat.div_eq_of_eq_mul_right two_pos <| by rw [Nat.mul_sub_left_distrib]; ring_nf,
        ← show ((2 * k + 1) ^ 2 - 1) / 2 = 2 * k ^ 2 + 2 * k by
          exact Nat.div_eq_of_eq_mul_right two_pos <| by erw [add_sq, Nat.add_sub_cancel]; ring1]
      nth_rw 5 [← k.mul_div_cancel_left two_pos]
      exact ⟨imp_of_if_pos (ih (2 * k) <| by linarith only [hk]) <| even_two_mul k,
        imp_of_if_neg (ih (2 * k + 1) <| by linarith only [hk]) k.not_even_two_mul_add_one⟩
    simp only [if_pos <| even_two_mul _, if_neg (m + 2).not_even_two_mul_add_one,
      show (2 * (m + 3)) ^ 2 = 2 * (2 * (m + 2) * (m + 4)) + 4 by ring1,
      show (2 * (m + 2) + 1) ^ 2 = 2 * (2 * (m + 2) * (m + 3)) + 1 by ring1, Nat.add_sub_cancel,
      Nat.mul_div_cancel_left _ two_pos]
    by_cases hm : Even m
    · rcases (even_iff_exists_two_mul m).mp hm with ⟨m, rfl⟩
      simp only [natDegree_odd_divisionPolynomial'_even m ih,
        coeff_odd_divisionPolynomial'_even m ih, natDegree_even_divisionPolynomial'_even m ih,
        coeff_even_divisionPolynomial'_even m ih, and_self]
    · replace ih (k : ℕ) (hk : k < m + 1) := ih k <| Nat.lt.step hk
      rcases Nat.odd_iff_not_even.mpr hm with ⟨m, rfl⟩
      simp only [natDegree_odd_divisionPolynomial'_odd m ih, coeff_odd_divisionPolynomial'_odd m ih,
        natDegree_even_divisionPolynomial'_odd m ih, coeff_even_divisionPolynomial'_odd m ih,
        and_self]

lemma natDegree_divisionPolynomial' (n : ℕ) : (W.divisionPolynomial' n).natDegree ≤
    if Even n then (n ^ 2 - 4) / 2 else (n ^ 2 - 1) / 2 := by
  by_cases hn : Even n
  · simpa only [if_pos hn] using (imp_of_if_pos (W.natDegree_coeff_divisionPolynomial' n) hn).left
  · simpa only [if_neg hn] using (imp_of_if_neg (W.natDegree_coeff_divisionPolynomial' n) hn).left

lemma coeff_divisionPolynomial' (n : ℕ) :
    if Even n then (W.divisionPolynomial' n).coeff ((n ^ 2 - 4) / 2) = (n / 2 : ℕ)
    else (W.divisionPolynomial' n).coeff ((n ^ 2 - 1) / 2) = n := by
  by_cases hn : Even n
  · rw [if_pos hn, (imp_of_if_pos (W.natDegree_coeff_divisionPolynomial' n) hn).right]
  · rw [if_neg hn, (imp_of_if_neg (W.natDegree_coeff_divisionPolynomial' n) hn).right]

/-! ### The univariate polynomials congruent to $\tilde{\psi}_n$ for $n \in \mathbb{Z}$ -/

/-- The univariate polynomials congruent under $R[W]$ to the bivariate auxiliary polynomials
$\tilde{\psi}_n$ associated to the $n$-division polynomials $\psi_n$ for $n \in \mathbb{Z}$. -/
@[pp_dot]
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

private lemma natDegree_coeff_divisionPolynomial (n : ℤ) :
    if Even n then (W.divisionPolynomial n).natDegree ≤ (n.natAbs ^ 2 - 4) / 2 ∧
      (W.divisionPolynomial n).coeff ((n.natAbs ^ 2 - 4) / 2) = (n / 2 : ℤ)
    else (W.divisionPolynomial n).natDegree ≤ (n.natAbs ^ 2 - 1) / 2 ∧
      (W.divisionPolynomial n).coeff ((n.natAbs ^ 2 - 1) / 2) = n := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · norm_cast
    exact W.divisionPolynomial_ofNat n ▸ W.natDegree_coeff_divisionPolynomial' n
  · simp only [even_neg, Int.even_coe_nat, divisionPolynomial_neg, natDegree_neg,
      divisionPolynomial_ofNat, Int.natAbs_neg, Int.natAbs_cast, coeff_neg, neg_eq_iff_eq_neg,
      Int.cast_neg, Int.cast_ofNat, neg_neg]
    convert W.natDegree_coeff_divisionPolynomial' n using 3 with hn
    rcases (even_iff_exists_two_mul _).mp hn with ⟨_, rfl⟩
    rw [Nat.cast_mul, neg_mul_eq_mul_neg, Nat.cast_ofNat, Int.mul_ediv_cancel_left _ two_ne_zero,
      Int.cast_neg, neg_neg, Int.cast_ofNat, Nat.mul_div_cancel_left _ two_pos]

lemma natDegree_divisionPolynomial (n : ℤ) : (W.divisionPolynomial n).natDegree ≤
    if Even n then (n.natAbs ^ 2 - 4) / 2 else (n.natAbs ^ 2 - 1) / 2 := by
  by_cases hn : Even n
  · simpa only [if_pos hn] using (imp_of_if_pos (W.natDegree_coeff_divisionPolynomial n) hn).left
  · simpa only [if_neg hn] using (imp_of_if_neg (W.natDegree_coeff_divisionPolynomial n) hn).left

lemma coeff_divisionPolynomial (n : ℤ) :
    if Even n then (W.divisionPolynomial n).coeff ((n.natAbs ^ 2 - 4) / 2) = (n / 2 : ℤ)
    else (W.divisionPolynomial n).coeff ((n.natAbs ^ 2 - 1) / 2) = n := by
  by_cases hn : Even n
  · rw [if_pos hn, (imp_of_if_pos (W.natDegree_coeff_divisionPolynomial n) hn).right]
  · rw [if_neg hn, (imp_of_if_neg (W.natDegree_coeff_divisionPolynomial n) hn).right]

/-! ### The univariate polynomials congruent to $\psi_n^2$ for $n \in \mathbb{Z}$ -/

/-- The univariate polynomials congruent under $R[W]$ to the bivariate squares $\psi_n^2$ of the
$n$-division polynomials $\psi_n$ for $n \in \mathbb{Z}$. -/
@[pp_dot]
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

private lemma natDegree_coeff_divisionPolynomialZSq_ofNat (n : ℕ) :
    (W.divisionPolynomialZSq n).natDegree ≤ n ^ 2 - 1 ∧
    (W.divisionPolynomialZSq n).coeff (n ^ 2 - 1) = (n ^ 2 : ℕ) := by
  rcases n with _ | n
  · erw [divisionPolynomialZSq_zero]
    exact ⟨natDegree_zero.le, Nat.cast_zero.symm⟩
  · have h := W.natDegree_coeff_divisionPolynomial' <| n + 1
    simp only [divisionPolynomialZSq, divisionPolynomial_ofNat, Int.natAbs_even, Int.even_coe_nat,
      Nat.even_add_one, ite_not] at h ⊢
    by_cases hn : Even n
    · rcases (even_iff_exists_two_mul n).mp hn with ⟨m, rfl⟩
      rw [if_pos hn, show (2 * m + 1) ^ 2 = 2 * (2 * m * (m + 1)) + 1 by ring1, Nat.add_sub_cancel,
        Nat.mul_div_cancel_left _ two_pos] at h
      rw [if_pos hn, mul_one, show (2 * m + 1) ^ 2 = 2 * (2 * m * (m + 1)) + 1 by ring1,
        Nat.add_sub_cancel]
      constructor
      · exact natDegree_pow_le_of_le 2 h.left
      · rw [coeff_pow_of_natDegree_le h.left, h.right]
        push_cast
        ring1
    · rcases Nat.odd_iff_not_even.mpr hn with ⟨m, rfl⟩
      rw [if_neg hn, show (2 * m + 2) ^ 2 = 2 * (2 * m * (m + 2)) + 4 by ring1, Nat.add_sub_cancel,
        Nat.mul_div_cancel_left _ two_pos, show (2 * m + 2) / 2 = 2 * (m + 1) / 2 by rfl,
        Nat.mul_div_cancel_left _ two_pos] at h
      rw [if_neg hn, show (2 * m + 2) ^ 2 = 2 * (2 * m * (m + 2)) + 4 by ring1, Nat.succ_sub_one]
      constructor
      · exact natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 h.left)
          W.natDegree_divisionPolynomial2Sq
      · rw [coeff_mul_of_natDegree_le (natDegree_pow_le_of_le 2 h.left)
            W.natDegree_divisionPolynomial2Sq, coeff_pow_of_natDegree_le h.left, h.right,
          coeff_divisionPolynomial2Sq]
        push_cast
        ring1

private lemma natDegree_coeff_divisionPolynomialZSq (n : ℤ) :
    (W.divisionPolynomialZSq n).natDegree ≤ n.natAbs ^ 2 - 1 ∧
    (W.divisionPolynomialZSq n).coeff (n.natAbs ^ 2 - 1) = (n.natAbs ^ 2 : ℕ) := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · exact W.natDegree_coeff_divisionPolynomialZSq_ofNat n
  · simp only [divisionPolynomialZSq_neg, Int.natAbs_neg]
    exact W.natDegree_coeff_divisionPolynomialZSq_ofNat n

lemma natDegree_divisionPolynomialZSq (n : ℤ) :
    (W.divisionPolynomialZSq n).natDegree ≤ n.natAbs ^ 2 - 1 :=
  (W.natDegree_coeff_divisionPolynomialZSq n).left

lemma coeff_divisionPolynomialZSq (n : ℤ) :
    (W.divisionPolynomialZSq n).coeff (n.natAbs ^ 2 - 1) = (n.natAbs ^ 2 : ℕ) :=
  (W.natDegree_coeff_divisionPolynomialZSq n).right

/-! ### The univariate polynomials congruent to $\phi_n$ for $n \in \mathbb{Z}$ -/

/-- The univariate polynomials congruent under $R[W]$ to the bivariate polynomials $\phi_n$ defined
in terms of the $n$-division polynomials $\psi_n$ for $n \in \mathbb{Z}$. -/
@[pp_dot]
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
    add_sub_cancel, divisionPolynomial_ofNat, Int.natAbs_cast]
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

private lemma natDegree_coeff_divisionPolynomialX_ofNat (n : ℕ) :
    (W.divisionPolynomialX n).natDegree ≤ n ^ 2 ∧ (W.divisionPolynomialX n).coeff (n ^ 2) = 1 := by
  rcases n with _ | _ | n
  · erw [divisionPolynomialX_zero]
    exact ⟨natDegree_one.le, coeff_one_zero⟩
  · erw [divisionPolynomialX_one]
    exact ⟨natDegree_X_le, coeff_X⟩
  · have h1 := W.natDegree_coeff_divisionPolynomial' <| n + 1
    have h2 := W.natDegree_coeff_divisionPolynomialZSq (n + 2 : ℕ)
    have h3 := W.natDegree_coeff_divisionPolynomial' <| n + 3
    simp only [divisionPolynomialX, Int.natAbs_cast, Nat.even_add_one, ite_not] at h1 h3 ⊢
    erw [← Nat.cast_add, divisionPolynomial_ofNat, ← Nat.cast_sub <| by linarith only,
      divisionPolynomial_ofNat, ← Nat.add_one, Nat.add_sub_cancel]
    by_cases hn : Even n
    · rcases (even_iff_exists_two_mul n).mp hn with ⟨m, rfl⟩
      rw [if_pos hn, show (2 * m + 1) ^ 2 = 2 * (2 * m * (m + 1)) + 1 by ring1, Nat.add_sub_cancel,
        Nat.mul_div_cancel_left _ two_pos] at h1
      rw [Int.natAbs_cast, show (2 * m + 2) ^ 2 = 4 * m * (m + 2) + 4 by ring1, Nat.succ_sub_one]
        at h2
      rw [if_pos hn, show (2 * m + 3) ^ 2 = 2 * (2 * (m + 1) * (m + 2)) + 1 by ring1,
        Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos] at h3
      rw [if_pos hn, mul_one]
      constructor
      · convert natDegree_sub_le_of_le (natDegree_mul_le_of_le natDegree_X_le h2.left) <|
          natDegree_mul_le_of_le h3.left h1.left using 1
        convert (max_self _).symm using 2 <;> ring1
      · rw [coeff_sub, show (2 * m + 2) ^ 2 = 4 * m * (m + 2) + 4 by ring1, coeff_X_mul, h2.right,
          show _ + _ = (2 * (m + 1) * (m + 2)) + (2 * m * (m + 1)) by ring1,
          coeff_mul_of_natDegree_le h3.left h1.left, h3.right, h1.right]
        push_cast
        ring1
    · rcases Nat.odd_iff_not_even.mpr hn with ⟨m, rfl⟩
      rw [if_neg hn, show (2 * m + 2) ^ 2 = 2 * (2 * m * (m + 2)) + 4 by ring1, Nat.add_sub_cancel,
        Nat.mul_div_cancel_left _ two_pos, show (2 * m + 2) / 2 = 2 * (m + 1) / 2 by rfl,
        Nat.mul_div_cancel_left _ two_pos] at h1
      rw [Int.natAbs_cast, show (2 * m + 3) ^ 2 = 4 * (m + 1) * (m + 2) + 1 by ring1,
        Nat.add_sub_cancel] at h2
      rw [if_neg hn, show (2 * m + 4) ^ 2 = 2 * (2 * (m + 1) * (m + 3)) + 4 by ring1,
        Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos,
        show (2 * m + 4) / 2 = 2 * (m + 2) / 2 by rfl, Nat.mul_div_cancel_left _ two_pos] at h3
      rw [if_neg hn]
      constructor
      · convert natDegree_sub_le_of_le (natDegree_mul_le_of_le natDegree_X_le h2.left) <|
          natDegree_mul_le_of_le (natDegree_mul_le_of_le h3.left h1.left)
            W.natDegree_divisionPolynomial2Sq using 1
        convert (max_self _).symm using 2 <;> ring1
      · rw [coeff_sub, show (2 * m + 3) ^ 2 = 4 * (m + 1) * (m + 2) + 1 by ring1, coeff_X_mul,
          h2.right, show _ + _ = (2 * (m + 1) * (m + 3)) + (2 * m * (m + 2)) + 3 by ring1,
          coeff_mul_of_natDegree_le (natDegree_mul_le_of_le h3.left h1.left)
            W.natDegree_divisionPolynomial2Sq, coeff_mul_of_natDegree_le h3.left h1.left, h3.right,
          h1.right, coeff_divisionPolynomial2Sq]
        push_cast
        ring1

private lemma natDegree_coeff_divisionPolynomialX (n : ℤ) :
    (W.divisionPolynomialX n).natDegree ≤ n.natAbs ^ 2 ∧
    (W.divisionPolynomialX n).coeff (n.natAbs ^ 2) = 1 := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · exact W.natDegree_coeff_divisionPolynomialX_ofNat n
  · rw [divisionPolynomialX_neg, Int.natAbs_neg]
    exact W.natDegree_coeff_divisionPolynomialX_ofNat n

lemma natDegree_divisionPolynomialX (n : ℤ) : (W.divisionPolynomialX n).natDegree ≤ n.natAbs ^ 2 :=
  (W.natDegree_coeff_divisionPolynomialX n).left

lemma coeff_divisionPolynomialX (n : ℤ) : (W.divisionPolynomialX n).coeff (n.natAbs ^ 2) = 1 :=
  (W.natDegree_coeff_divisionPolynomialX n).right

/-! ### The bivariate $n$-division polynomials $\psi_n$ for $n \in \mathbb{Z}$ -/

/-- The bivariate $n$-division polynomials $\psi_n$ for $n \in \mathbb{Z}$. -/
@[pp_dot]
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
