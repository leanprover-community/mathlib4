/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic.ComputeDegree

/-!
# Division polynomials of Weierstrass curves

This file defines certain polynomials associated to division polynomials of Weierstrass curves and
computes their leading terms. These are defined in terms of the auxiliary sequences of normalised
elliptic divisibility sequences defined in `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

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
$\mathcal{R}[X, Y] := \mathbb{Z}[a_i][X, Y] / \langle W(a_i, X, Y)\rangle$ associated to $W$, where
$W(a_i, X, Y)$ is the associated Weierstrass equation. Then $\omega_n$ can be equivalently defined
as its image under the associated universal morphism $\mathcal{R}[X, Y] \to R[X, Y]$.

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
$\Psi_2^{[2]} \in R[X]$ and $\tilde{\Psi}_n \in R[X]$. By induction, their leading terms are
 * $\tilde{\Psi}_n = nX^{\tfrac{n^2 - 4}{2}} + \dots$ if $n$ is even,
 * $\tilde{\Psi}_n = nX^{\tfrac{n^2 - 1}{2}} + \dots$ if $n$ is odd,
 * $\Psi_n^{[2]} = n^2X^{n^2 - 1} + \dots$, and
 * $\Phi_n = X^{n^2} + \dots$.

## Main definitions

 * `WeierstrassCurve.Ψ₂Sq`: the univariate polynomial $\Psi_2^{[2]}$.
 * `WeierstrassCurve.preΨ`: the univariate polynomials $\tilde{\Psi}_n$.
 * `WeierstrassCurve.ΨSq`: the univariate polynomials $\Psi_n^{[2]}$.
 * `WeierstrassCurve.Ψ`: the bivariate polynomials $\Psi_n$.
 * `WeierstrassCurve.Φ`: the univariate polynomials $\Phi_n$.
 * `WeierstrassCurve.ψ`: the bivariate $n$-division polynomials $\psi_n$.
 * `WeierstrassCurve.φ`: the bivariate polynomials $\phi_n$.
 * TODO: the bivariate polynomials $\omega_n$.

## Main statements
 * `WeierstrassCurve.natDegree_Ψ₂Sq`: the degree of $\Psi_2^{[2]}$.
 * `WeierstrassCurve.coeff_Ψ₂Sq`: the leading coefficient of $\Psi_2^{[2]}$..
 * `WeierstrassCurve.natDegree_Ψ'`: the degree of $\tilde{\Psi}_n$.
 * `WeierstrassCurve.coeff_Ψ'`: the leading coefficient of $\tilde{\Psi}_n$.
 * `WeierstrassCurve.natDegree_ΨSq`: the degree of $\Psi_n^{[2]}$.
 * `WeierstrassCurve.coeff_ΨSq`: the leading coefficient of $\Psi_n^{[2]}$.
 * `WeierstrassCurve.natDegree_Φ`: the degree of $\Phi_n$.
 * `WeierstrassCurve.coeff_Φ`: the leading coefficient of $\Phi_n$.

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

universe u v

namespace WeierstrassCurve

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)

/-! ### The univariate polynomial $\Psi_2^{[2]}$ -/

/-- The $2$-division polynomial $\psi_2 = \Psi_2$. -/
protected noncomputable def ψ₂ : R[X][Y] :=
  W.toAffine.polynomialY

/-- The univariate polynomial $\Psi_2^{[2]}$ congruent to $\psi_2^2$. -/
protected noncomputable def Ψ₂Sq : R[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

lemma C_Ψ₂Sq_eq : C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial := by
  rw [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.ψ₂, b₂, b₄, b₆, Affine.polynomialY, Affine.polynomial]
  C_simp
  ring1

-- TODO: remove `twoTorsionPolynomial` in favour of `Ψ₂Sq`
lemma Ψ₂Sq_eq : W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly :=
  rfl

lemma natDegree_Ψ₂Sq : W.Ψ₂Sq.natDegree ≤ 3 := by
  rw [WeierstrassCurve.Ψ₂Sq]
  compute_degree

@[simp]
lemma coeff_Ψ₂Sq : W.Ψ₂Sq.coeff 3 = 4 := by
  rw [WeierstrassCurve.Ψ₂Sq]
  compute_degree!

/-! ### The univariate polynomials $\tilde{\Psi}_n$ for $n \in \mathbb{N}$ -/

/-- The $3$-division polynomial $\psi_3 = \Psi_3$. -/
protected noncomputable def Ψ₃ : R[X] :=
  3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈

lemma natDegree_Ψ₃ : W.Ψ₃.natDegree ≤ 4 := by
  rw [WeierstrassCurve.Ψ₃]
  compute_degree

@[simp]
lemma coeff_Ψ₃ : W.Ψ₃.coeff 4 = 3 := by
  rw [WeierstrassCurve.Ψ₃]
  compute_degree!

/-- The univariate polynomial $\tilde{\Psi}_4$, which is auxiliary to the $4$-division polynomial
$\psi_4 = \Psi_4 = \tilde{\Psi}_4\psi_2$. -/
protected noncomputable def Ψ₄' : R[X] :=
  2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)

lemma natDegree_Ψ₄' : W.Ψ₄'.natDegree ≤ 6 := by
  rw [WeierstrassCurve.Ψ₄']
  compute_degree

@[simp]
lemma coeff_Ψ₄' : W.Ψ₄'.coeff 6 = 2 := by
  rw [WeierstrassCurve.Ψ₄']
  compute_degree!

/-- The univariate polynomials $\tilde{\Psi}_n$ for $n \in \mathbb{N}$, which are auxiliary to the
bivariate polynomials $\Psi_n$ congruent to the bivariate $n$-division polynomials $\psi_n$. -/
protected noncomputable def preΨ' (n : ℕ) : R[X] :=
  preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.Ψ₄' n

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
lemma preΨ'_four : W.preΨ' 4 = W.Ψ₄' :=
  preNormEDS'_four ..

lemma preΨ'_odd (m : ℕ) : W.preΨ' (2 * (m + 2) + 1) =
    W.preΨ' (m + 4) * W.preΨ' (m + 2) ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=
  preNormEDS'_odd ..

lemma preΨ'_even (m : ℕ) : W.preΨ' (2 * (m + 3)) =
    W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 3) * W.preΨ' (m + 5) -
      W.preΨ' (m + 1) * W.preΨ' (m + 3) * W.preΨ' (m + 4) ^ 2 :=
  preNormEDS'_even ..

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

private lemma natDegree_even {a b c d e f : R[X]} {da db dc dd de df n : ℕ}
    (ha : a.natDegree ≤ da) (hb : b.natDegree ≤ db) (hc : c.natDegree ≤ dc)
    (hd : d.natDegree ≤ dd) (he : e.natDegree ≤ de) (hf : f.natDegree ≤ df)
    (habc : n = 2 * da + db + dc) (hdef : n = dd + de + 2 * df) :
    (a ^ 2 * b * c - d * e * f ^ 2).natDegree ≤ n := by
  nth_rw 1 [← max_self n, habc, hdef]
  convert natDegree_sub_le_of_le .. using 1
  · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 ha) hb) hc
  · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le hd he) <| natDegree_pow_le_of_le 2 hf

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

private lemma natDegree_Ψ''_zero : (W.Ψ'' 0).natDegree = 0 := by
  rw [Ψ''_zero, natDegree_zero]

private lemma coeff_Ψ''_zero : (W.Ψ'' 0).coeff 0 = 0 := by
  rw [Ψ''_zero, coeff_zero]

private lemma natDegree_Ψ''_one : (W.Ψ'' 1).natDegree = 0 := by
  rw [Ψ''_one, natDegree_one]

private lemma coeff_Ψ''_one : (W.Ψ'' 1).coeff 0 = 1 := by
  rw [Ψ''_one, coeff_one_zero]

private lemma natDegree_Ψ''_two : (W.Ψ'' 2).natDegree = 0 := by
  rw [Ψ''_two, natDegree_one]

private lemma coeff_Ψ''_two : (W.Ψ'' 2).coeff 0 = 1 := by
  rw [Ψ''_two, coeff_one_zero]

private lemma natDegree_Ψ''_three : (W.Ψ'' 3).natDegree ≤ 4 := by
  simp only [Ψ''_three, natDegree_Ψ₃]

private lemma coeff_Ψ''_three : (W.Ψ'' 3).coeff 4 = 3 := by
  rw [Ψ''_three, coeff_Ψ₃]

private lemma natDegree_Ψ''_four : (W.Ψ'' 4).natDegree ≤ 6 := by
  simp only [Ψ''_four, natDegree_Ψ₄']

private lemma coeff_Ψ''_four : (W.Ψ'' 4).coeff 6 = 2 := by
  rw [Ψ''_four, coeff_Ψ₄']

private lemma natDegree_Ψ''_five : (W.Ψ'' 5).natDegree ≤ 12 := by
  rw [show 5 = 2 * 2 + 1 by rfl, Ψ''_odd, if_pos even_zero, if_pos even_zero, ← @one_pow R[X]]
  exact natDegree_odd W.natDegree_Ψ''_four W.natDegree_Ψ''_two.le W.natDegree_Ψ₂Sq
    W.natDegree_Ψ''_one.le W.natDegree_Ψ''_three natDegree_one.le rfl rfl

private lemma coeff_Ψ''_five : (W.Ψ'' 5).coeff 12 = 5 := by
  rw [show 5 = 2 * 2 + 1 by rfl, Ψ''_odd, if_pos even_zero, if_pos even_zero, ← @one_pow R[X],
    coeff_odd W.natDegree_Ψ''_four W.natDegree_Ψ''_two.le W.natDegree_Ψ₂Sq W.natDegree_Ψ''_one.le
      W.natDegree_Ψ''_three natDegree_one.le rfl rfl, coeff_Ψ''_four, coeff_Ψ''_two, coeff_Ψ₂Sq,
    coeff_Ψ''_one, coeff_Ψ''_three, coeff_one_zero]
  norm_num1

private lemma natDegree_Ψ''_six : (W.Ψ'' 6).natDegree ≤ 16 := by
  rw [show 6 = 2 * 3 by rfl, Ψ''_even]
  exact natDegree_even W.natDegree_Ψ''_two.le W.natDegree_Ψ''_three W.natDegree_Ψ''_five
    W.natDegree_Ψ''_one.le W.natDegree_Ψ''_three W.natDegree_Ψ''_four rfl rfl

private lemma coeff_Ψ''_six : (W.Ψ'' 6).coeff 16 = 3 := by
  rw [show 6 = 2 * 3 by rfl, Ψ''_even, coeff_even W.natDegree_Ψ''_two.le W.natDegree_Ψ''_three
      W.natDegree_Ψ''_five W.natDegree_Ψ''_one.le W.natDegree_Ψ''_three W.natDegree_Ψ''_four rfl
    rfl, coeff_Ψ''_two, coeff_Ψ''_three, coeff_Ψ''_five, coeff_Ψ''_one, coeff_Ψ''_four]
  norm_num1

private lemma natDegree_Ψ''_eight : (W.Ψ'' 8).natDegree ≤ 30 := by
  rw [show 8 = 2 * 4 by rfl, Ψ''_even]
  exact natDegree_even W.natDegree_Ψ''_three W.natDegree_Ψ''_four W.natDegree_Ψ''_six
    W.natDegree_Ψ''_two.le W.natDegree_Ψ''_four W.natDegree_Ψ''_five rfl rfl

private lemma coeff_Ψ''_eight : (W.Ψ'' 8).coeff 30 = 4 := by
  rw [show 8 = 2 * 4 by rfl, Ψ''_even, coeff_even W.natDegree_Ψ''_three W.natDegree_Ψ''_four
      W.natDegree_Ψ''_six W.natDegree_Ψ''_two.le W.natDegree_Ψ''_four W.natDegree_Ψ''_five rfl rfl,
    coeff_Ψ''_three, coeff_Ψ''_four, coeff_Ψ''_six, coeff_Ψ''_two, coeff_Ψ''_five]
  norm_num1

section Inductive

variable {W} (m : ℕ) (ih : ∀ k < 2 * m + 2,
  ((W.Ψ'' <| 2 * k).natDegree ≤ 2 * k ^ 2 - 2 ∧ (W.Ψ'' <| 2 * k).coeff (2 * k ^ 2 - 2) = k) ∧
  ((W.Ψ'' <| 2 * k + 1).natDegree ≤ 2 * k ^ 2 + 2 * k ∧
    (W.Ψ'' <| 2 * k + 1).coeff (2 * k ^ 2 + 2 * k) = (2 * k + 1 : ℕ)))

private lemma natDegree_Ψ''_add_one : (W.Ψ'' <| 2 * m + 1).natDegree ≤ 2 * m * (m + 1) := by
  convert (ih m <| by linarith only).right.left using 1
  ring1

private lemma coeff_Ψ''_add_one :
    (W.Ψ'' <| 2 * m + 1).coeff (2 * m * (m + 1)) = (2 * m + 1 : ℕ) := by
  convert (ih m <| by linarith only).right.right using 2
  ring1

private lemma natDegree_Ψ''_add_two : (W.Ψ'' <| 2 * m + 2).natDegree ≤ 2 * m * (m + 2) := by
  convert (ih (m + 1) <| by linarith only).left.left using 1
  rw [show 2 * (m + 1) ^ 2 = 2 * m * (m + 2) + 2 by ring1, Nat.add_sub_cancel]

private lemma coeff_Ψ''_add_two : (W.Ψ'' <| 2 * m + 2).coeff (2 * m * (m + 2)) = (m + 1 : ℕ) := by
  convert (ih (m + 1) <| by linarith only).left.right using 2
  rw [show 2 * (m + 1) ^ 2 = 2 * m * (m + 2) + 2 by ring1, Nat.add_sub_cancel]

private lemma natDegree_Ψ''_add_three : (W.Ψ'' <| 2 * m + 3).natDegree ≤ 2 * (m + 1) * (m + 2) := by
  convert (ih (m + 1) <| by linarith only).right.left using 1
  ring1

private lemma coeff_Ψ''_add_three :
    (W.Ψ'' <| 2 * m + 3).coeff (2 * (m + 1) * (m + 2)) = (2 * m + 3 : ℕ) := by
  convert (ih (m + 1) <| by linarith only).right.right using 2
  ring1

private lemma natDegree_Ψ''_add_four : (W.Ψ'' <| 2 * m + 4).natDegree ≤ 2 * (m + 1) * (m + 3) := by
  rcases m with _ | m
  · exact W.natDegree_Ψ''_four
  · convert (ih (m + 3) <| by linarith only).left.left using 1
    rw [show 2 * (m + 3) ^ 2 = 2 * (m + 2) * (m + 4) + 2 by ring1, Nat.add_sub_cancel]

private lemma coeff_Ψ''_add_four :
    (W.Ψ'' <| 2 * m + 4).coeff (2 * (m + 1) * (m + 3)) = (m + 2 : ℕ) := by
  rcases m with _ | m
  · exact W.coeff_Ψ''_four
  · convert (ih (m + 3) <| by linarith only).left.right using 2
    rw [show 2 * (m + 3) ^ 2 = 2 * (m + 2) * (m + 4) + 2 by ring1, Nat.add_sub_cancel]

private lemma natDegree_Ψ''_add_five : (W.Ψ'' <| 2 * m + 5).natDegree ≤ 2 * (m + 2) * (m + 3) := by
  rcases m with _ | m
  · exact W.natDegree_Ψ''_five
  · convert (ih (m + 3) <| by linarith only).right.left using 1
    ring1

private lemma coeff_Ψ''_add_five :
    (W.Ψ'' <| 2 * m + 5).coeff (2 * (m + 2) * (m + 3)) = (2 * m + 5 : ℕ) := by
  rcases m with _ | m
  · exact W.coeff_Ψ''_five
  · convert (ih (m + 3) <| by linarith only).right.right using 2
    ring1

private lemma natDegree_Ψ''_add_six : (W.Ψ'' <| 2 * m + 6).natDegree ≤ 2 * (m + 2) * (m + 4) := by
  rcases m with _ | _ | m
  · exact W.natDegree_Ψ''_six
  · exact W.natDegree_Ψ''_eight
  · convert (ih (m + 5) <| by linarith only).left.left using 1
    rw [show 2 * (m + 5) ^ 2 = 2 * (m + 4) * (m + 6) + 2 by ring1, Nat.add_sub_cancel]

private lemma coeff_Ψ''_add_six :
    (W.Ψ'' <| 2 * m + 6).coeff (2 * (m + 2) * (m + 4)) = (m + 3 : ℕ) := by
  rcases m with _ | _ | m
  · exact W.coeff_Ψ''_six
  · exact W.coeff_Ψ''_eight
  · convert (ih (m + 5) <| by linarith only).left.right using 2
    rw [show 2 * (m + 5) ^ 2 = 2 * (m + 4) * (m + 6) + 2 by ring1, Nat.add_sub_cancel]

private lemma natDegree_odd_Ψ''_even :
    (W.Ψ'' <| 2 * (2 * m + 2) + 1).natDegree ≤ 2 * (2 * m + 2) * (2 * m + 3) := by
  rw [Ψ''_odd, if_pos <| even_two_mul m, if_pos <| even_two_mul m, ← @one_pow R[X]]
  exact natDegree_odd (natDegree_Ψ''_add_four m ih) (natDegree_Ψ''_add_two m ih) W.natDegree_Ψ₂Sq
    (natDegree_Ψ''_add_one m ih) (natDegree_Ψ''_add_three m ih) natDegree_one.le (by ring1)
    (by ring1)

private lemma coeff_odd_Ψ''_even :
    (W.Ψ'' <| 2 * (2 * m + 2) + 1).coeff (2 * (2 * m + 2) * (2 * m + 3)) =
      (2 * (2 * m + 2) + 1 : ℕ) := by
  rw [Ψ''_odd, if_pos <| even_two_mul m, if_pos <| even_two_mul m, ← @one_pow R[X],
    coeff_odd (natDegree_Ψ''_add_four m ih) (natDegree_Ψ''_add_two m ih) W.natDegree_Ψ₂Sq
      (natDegree_Ψ''_add_one m ih) (natDegree_Ψ''_add_three m ih) natDegree_one.le (by ring1)
      (by ring1), coeff_Ψ''_add_four m ih, coeff_Ψ''_add_two m ih, coeff_Ψ₂Sq,
    coeff_Ψ''_add_one m ih, coeff_Ψ''_add_three m ih, coeff_one_zero]
  push_cast
  ring1

private lemma natDegree_odd_Ψ''_odd :
    (W.Ψ'' <| 2 * (2 * m + 3) + 1).natDegree ≤ 2 * (2 * m + 3) * (2 * m + 4) := by
  rw [Ψ''_odd, if_neg m.not_even_two_mul_add_one, ← @one_pow R[X],
    if_neg m.not_even_two_mul_add_one]
  exact natDegree_odd (natDegree_Ψ''_add_five m ih) (natDegree_Ψ''_add_three m ih) natDegree_one.le
    (natDegree_Ψ''_add_two m ih) (natDegree_Ψ''_add_four m ih) W.natDegree_Ψ₂Sq (by ring1)
    (by ring1)

private lemma coeff_odd_Ψ''_odd :
    (W.Ψ'' <| 2 * (2 * m + 3) + 1).coeff (2 * (2 * m + 3) * (2 * m + 4)) =
      (2 * (2 * m + 3) + 1 : ℕ) := by
  rw [Ψ''_odd, if_neg m.not_even_two_mul_add_one, ← @one_pow R[X],
    if_neg m.not_even_two_mul_add_one, coeff_odd (natDegree_Ψ''_add_five m ih)
      (natDegree_Ψ''_add_three m ih) natDegree_one.le (natDegree_Ψ''_add_two m ih)
      (natDegree_Ψ''_add_four m ih) W.natDegree_Ψ₂Sq (by ring1) (by ring1), coeff_Ψ''_add_five m ih,
    coeff_Ψ''_add_three m ih, coeff_one_zero, coeff_Ψ''_add_two m ih, coeff_Ψ''_add_four m ih,
    coeff_Ψ₂Sq]
  push_cast
  ring1

private lemma natDegree_even_Ψ''_even :
    (W.Ψ'' <| 2 * (2 * m + 3)).natDegree ≤ 2 * (2 * m + 2) * (2 * m + 4) := by
  rw [Ψ''_even]
  exact natDegree_even (natDegree_Ψ''_add_two m ih) (natDegree_Ψ''_add_three m ih)
    (natDegree_Ψ''_add_five m ih) (natDegree_Ψ''_add_one m ih) (natDegree_Ψ''_add_three m ih)
    (natDegree_Ψ''_add_four m ih) (by ring1) (by ring1)

private lemma coeff_even_Ψ''_even :
    (W.Ψ'' <| 2 * (2 * m + 3)).coeff (2 * (2 * m + 2) * (2 * m + 4)) = (2 * m + 3 : ℕ) := by
  rw [Ψ''_even, coeff_even (natDegree_Ψ''_add_two m ih) (natDegree_Ψ''_add_three m ih)
      (natDegree_Ψ''_add_five m ih) (natDegree_Ψ''_add_one m ih) (natDegree_Ψ''_add_three m ih)
      (natDegree_Ψ''_add_four m ih) (by ring1) (by ring1), coeff_Ψ''_add_two m ih,
    coeff_Ψ''_add_three m ih, coeff_Ψ''_add_five m ih, coeff_Ψ''_add_one m ih,
    coeff_Ψ''_add_four m ih]
  push_cast
  ring1

private lemma natDegree_even_Ψ''_odd :
    (W.Ψ'' <| 2 * (2 * m + 4)).natDegree ≤ 2 * (2 * m + 3) * (2 * m + 5) := by
  rw [Ψ''_even]
  exact natDegree_even (natDegree_Ψ''_add_three m ih) (natDegree_Ψ''_add_four m ih)
    (natDegree_Ψ''_add_six m ih) (natDegree_Ψ''_add_two m ih) (natDegree_Ψ''_add_four m ih)
    (natDegree_Ψ''_add_five m ih) (by ring1) (by ring1)

private lemma coeff_even_Ψ''_odd :
    (W.Ψ'' <| 2 * (2 * m + 4)).coeff (2 * (2 * m + 3) * (2 * m + 5)) = (2 * m + 4 : ℕ) := by
  rw [Ψ''_even, coeff_even (natDegree_Ψ''_add_three m ih) (natDegree_Ψ''_add_four m ih)
      (natDegree_Ψ''_add_six m ih) (natDegree_Ψ''_add_two m ih) (natDegree_Ψ''_add_four m ih)
      (natDegree_Ψ''_add_five m ih) (by ring1) (by ring1), coeff_Ψ''_add_three m ih,
    coeff_Ψ''_add_four m ih, coeff_Ψ''_add_six m ih, coeff_Ψ''_add_two m ih,
    coeff_Ψ''_add_five m ih]
  push_cast
  ring1

end Inductive

private lemma natDegree_coeff_Ψ'' (n : ℕ) :
    if Even n then (W.Ψ'' n).natDegree ≤ (n ^ 2 - 4) / 2 ∧
        (W.Ψ'' n).coeff ((n ^ 2 - 4) / 2) = (n / 2 : ℕ)
      else (W.Ψ'' n).natDegree ≤ (n ^ 2 - 1) / 2 ∧ (W.Ψ'' n).coeff ((n ^ 2 - 1) / 2) = n := by
  induction n using normEDSRec' with
  | zero => exact ⟨W.natDegree_Ψ''_zero.le, by erw [coeff_Ψ''_zero, Nat.cast_zero]⟩
  | one => exact ⟨W.natDegree_Ψ''_one.le, by erw [coeff_Ψ''_one, Nat.cast_one]⟩
  | two => exact ⟨W.natDegree_Ψ''_two.le, by erw [coeff_Ψ''_two, Nat.cast_one]⟩
  | three => exact ⟨W.natDegree_Ψ''_three, W.coeff_Ψ''_three⟩
  | four => exact ⟨W.natDegree_Ψ''_four, W.coeff_Ψ''_four⟩
  | _ m ih =>
    replace ih (k : ℕ) (hk : k < m + 2) :
        ((W.Ψ'' <| 2 * k).natDegree ≤ 2 * k ^ 2 - 2 ∧
          (W.Ψ'' <| 2 * k).coeff (2 * k ^ 2 - 2) = k) ∧
        ((W.Ψ'' <| 2 * k + 1).natDegree ≤ 2 * k ^ 2 + 2 * k ∧
          (W.Ψ'' <| 2 * k + 1).coeff (2 * k ^ 2 + 2 * k) = (2 * k + 1 : ℕ)) := by
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
    · rcases even_iff_exists_two_mul.mp hm with ⟨m, rfl⟩
      simp only [natDegree_odd_Ψ''_even m ih, coeff_odd_Ψ''_even m ih, natDegree_even_Ψ''_even m ih,
        coeff_even_Ψ''_even m ih, and_self]
    · replace ih (k : ℕ) (hk : k < m + 1) := ih k <| Nat.lt.step hk
      rcases Nat.odd_iff_not_even.mpr hm with ⟨m, rfl⟩
      simp only [natDegree_odd_Ψ''_odd m ih, coeff_odd_Ψ''_odd m ih, natDegree_even_Ψ''_odd m ih,
        coeff_even_Ψ''_odd m ih, and_self]

lemma natDegree_Ψ'' (n : ℕ) :
    (W.Ψ'' n).natDegree ≤ if Even n then (n ^ 2 - 4) / 2 else (n ^ 2 - 1) / 2 := by
  by_cases hn : Even n
  · simpa only [if_pos hn] using (imp_of_if_pos (W.natDegree_coeff_Ψ'' n) hn).left
  · simpa only [if_neg hn] using (imp_of_if_neg (W.natDegree_coeff_Ψ'' n) hn).left

lemma coeff_Ψ'' (n : ℕ) :
    if Even n then (W.Ψ'' n).coeff ((n ^ 2 - 4) / 2) = (n / 2 : ℕ)
      else (W.Ψ'' n).coeff ((n ^ 2 - 1) / 2) = n := by
  by_cases hn : Even n
  · rw [if_pos hn, (imp_of_if_pos (W.natDegree_coeff_Ψ'' n) hn).right]
  · rw [if_neg hn, (imp_of_if_neg (W.natDegree_coeff_Ψ'' n) hn).right]

/-! ### The univariate polynomials $\tilde{\Psi}_n$ for $n \in \mathbb{Z}$ -/

/-- The univariate polynomials $\tilde{\Psi}_n$ for $n \in \mathbb{Z}$, which are auxiliary to the
bivariate polynomials $\Psi_n$ congruent to the bivariate $n$-division polynomials $\psi_n$. -/
protected noncomputable def preΨ (n : ℤ) : R[X] :=
  preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.Ψ₄' n

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
lemma preΨ_four : W.preΨ 4 = W.Ψ₄' :=
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

private lemma natDegree_coeff_Ψ' (n : ℤ) :
    if Even n then (W.Ψ' n).natDegree ≤ (n.natAbs ^ 2 - 4) / 2 ∧
        (W.Ψ' n).coeff ((n.natAbs ^ 2 - 4) / 2) = (n / 2 : ℤ)
      else (W.Ψ' n).natDegree ≤ (n.natAbs ^ 2 - 1) / 2 ∧
          (W.Ψ' n).coeff ((n.natAbs ^ 2 - 1) / 2) = n := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · norm_cast
    exact W.Ψ'_ofNat n ▸ W.natDegree_coeff_Ψ'' n
  · simp only [even_neg, Int.even_coe_nat, Ψ'_neg, natDegree_neg, Ψ'_ofNat, Int.natAbs_neg,
      Int.natAbs_cast, coeff_neg, neg_eq_iff_eq_neg, Int.cast_neg, Int.cast_natCast, neg_neg]
    convert W.natDegree_coeff_Ψ'' n using 3 with hn
    rcases even_iff_exists_two_mul.mp hn with ⟨_, rfl⟩
    rw [Nat.cast_mul, neg_mul_eq_mul_neg, Nat.cast_ofNat, Int.mul_ediv_cancel_left _ two_ne_zero,
      Int.cast_neg, neg_neg, Int.cast_natCast, Nat.mul_div_cancel_left _ two_pos]

lemma natDegree_Ψ' (n : ℤ) :
    (W.Ψ' n).natDegree ≤ if Even n then (n.natAbs ^ 2 - 4) / 2 else (n.natAbs ^ 2 - 1) / 2 := by
  by_cases hn : Even n
  · simpa only [if_pos hn] using (imp_of_if_pos (W.natDegree_coeff_Ψ' n) hn).left
  · simpa only [if_neg hn] using (imp_of_if_neg (W.natDegree_coeff_Ψ' n) hn).left

lemma coeff_Ψ' (n : ℤ) :
    if Even n then (W.Ψ' n).coeff ((n.natAbs ^ 2 - 4) / 2) = (n / 2 : ℤ)
      else (W.Ψ' n).coeff ((n.natAbs ^ 2 - 1) / 2) = n := by
  by_cases hn : Even n
  · rw [if_pos hn, (imp_of_if_pos (W.natDegree_coeff_Ψ' n) hn).right]
  · rw [if_neg hn, (imp_of_if_neg (W.natDegree_coeff_Ψ' n) hn).right]

/-! ### The univariate polynomials $\Psi_n^{[2]}$ -/

/-- The univariate polynomials $\Psi_n^{[2]}$ congruent to $\psi_n^2$. -/
protected noncomputable def ΨSq (n : ℤ) : R[X] :=
  W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1

@[simp]
lemma ΨSq_ofNat (n : ℕ) : W.ΨSq n = W.preΨ' n ^ 2 * if Even n then W.Ψ₂Sq else 1 := by
  simp only [WeierstrassCurve.ΨSq, preΨ_ofNat, Int.even_coe_nat]

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
lemma ΨSq_four : W.ΨSq 4 = W.Ψ₄' ^ 2 * W.Ψ₂Sq := by
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
  simp only [WeierstrassCurve.ΨSq, preΨ_neg, neg_sq, even_neg]

private lemma natDegree_coeff_ΨSq_ofNat (n : ℕ) :
    (W.ΨSq n).natDegree ≤ n ^ 2 - 1 ∧ (W.ΨSq n).coeff (n ^ 2 - 1) = (n ^ 2 : ℕ) := by
  rcases n with _ | n
  · erw [ΨSq_zero]
    exact ⟨natDegree_zero.le, Nat.cast_zero.symm⟩
  · have h := W.natDegree_coeff_Ψ'' <| n + 1
    simp only [WeierstrassCurve.ΨSq, Ψ'_ofNat, Int.natAbs_even, Int.even_coe_nat, Nat.even_add_one,
      ite_not] at h ⊢
    by_cases hn : Even n
    · rcases even_iff_exists_two_mul.mp hn with ⟨m, rfl⟩
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
      · exact natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 h.left) W.natDegree_Ψ₂Sq
      · rw [coeff_mul_of_natDegree_le (natDegree_pow_le_of_le 2 h.left) W.natDegree_Ψ₂Sq,
          coeff_pow_of_natDegree_le h.left, h.right, coeff_Ψ₂Sq]
        push_cast
        ring1

private lemma natDegree_coeff_ΨSq (n : ℤ) :
    (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 ∧
      (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = (n.natAbs ^ 2 : ℕ) := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · exact W.natDegree_coeff_ΨSq_ofNat n
  · simpa only [ΨSq_neg, Int.natAbs_neg] using W.natDegree_coeff_ΨSq_ofNat n

lemma natDegree_ΨSq (n : ℤ) :
    (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 :=
  (W.natDegree_coeff_ΨSq n).left

lemma coeff_ΨSq (n : ℤ) :
    (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = (n.natAbs ^ 2 : ℕ) :=
  (W.natDegree_coeff_ΨSq n).right

/-! ### The bivariate polynomials $\Psi_n$ -/

/-- The bivariate polynomials $\Psi_n$ congruent to the $n$-division polynomials $\psi_n$. -/
protected noncomputable def Ψ (n : ℤ) : R[X][Y] :=
  C (W.preΨ n) * if Even n then W.ψ₂ else 1

@[simp]
lemma Ψ_ofNat (n : ℕ) : W.Ψ n = C (W.preΨ' n) * if Even n then W.ψ₂ else 1 := by
  simp only [WeierstrassCurve.Ψ, preΨ_ofNat, Int.even_coe_nat]

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
lemma Ψ_four : W.Ψ 4 = C W.Ψ₄' * W.ψ₂ := by
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
  simp only [WeierstrassCurve.Ψ, preΨ_neg, C_neg, neg_mul (α := R[X][Y]), even_neg]

/-! ### The univariate polynomials $\Phi_n$ -/

/-- The univariate polynomials $\Phi_n$ congruent to $\phi_n$. -/
protected noncomputable def Φ (n : ℤ) : R[X] :=
  X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq

@[simp]
lemma Φ_ofNat (n : ℕ) : W.Φ (n + 1) =
    X * W.preΨ' (n + 1) ^ 2 * (if Even n then 1 else W.Ψ₂Sq) -
      W.preΨ' (n + 2) * W.preΨ' n * (if Even n then W.Ψ₂Sq else 1) := by
  erw [WeierstrassCurve.Φ, ΨSq_ofNat, ← mul_assoc, preΨ_ofNat, add_sub_cancel_right, preΨ_ofNat]
  simp only [Nat.even_add_one, Int.even_add_one, Int.even_coe_nat, ite_not]

@[simp]
lemma Φ_zero : W.Φ 0 = 1 := by
  rw [WeierstrassCurve.Φ, ΨSq_zero, mul_zero, zero_sub, zero_add, preΨ_one, one_mul, zero_sub,
    preΨ_neg, preΨ_one, neg_one_mul, neg_neg, if_pos even_zero]

@[simp]
lemma Φ_one : W.Φ 1 = X := by
  erw [Φ_ofNat, preΨ'_one, one_pow, mul_one, mul_one, preΨ'_zero, mul_zero, zero_mul, sub_zero]

@[simp]
lemma Φ_two : W.Φ 2 = X ^ 4 - C W.b₄ * X ^ 2 - C (2 * W.b₆) * X - C W.b₈ := by
  erw [Φ_ofNat, preΨ'_two, if_neg Nat.not_even_one, WeierstrassCurve.Ψ₂Sq, preΨ'_three, preΨ'_one,
    mul_one, WeierstrassCurve.Ψ₃]
  C_simp
  ring1

@[simp]
lemma Φ_three : W.Φ 3 = X * W.Ψ₃ ^ 2 - W.Ψ₄' * W.Ψ₂Sq := by
  erw [Φ_ofNat, preΨ'_three, mul_one, preΨ'_four, preΨ'_two, mul_one, if_pos even_two]

@[simp]
lemma Φ_four : W.Φ 4 = X * W.Ψ₄' ^ 2 * W.Ψ₂Sq - W.Ψ₃ * (W.Ψ₄' * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) := by
  erw [Φ_ofNat, preΨ'_four, if_neg <| by decide, show 3 + 2 = 2 * 2 + 1 by rfl, preΨ'_odd,
    preΨ'_four, preΨ'_two, if_pos even_zero, preΨ'_one, preΨ'_three, if_pos even_zero]
  ring1

@[simp]
lemma Φ_neg (n : ℤ) : W.Φ (-n) = W.Φ n := by
  simp only [WeierstrassCurve.Φ, ΨSq_neg, neg_add_eq_sub, ← neg_sub n, preΨ_neg, ← neg_add',
    preΨ_neg, neg_mul_neg, mul_comm <| W.preΨ <| n - 1, even_neg]

private lemma natDegree_coeff_Φ_ofNat (n : ℕ) :
    (W.Φ n).natDegree ≤ n ^ 2 ∧ (W.Φ n).coeff (n ^ 2) = 1 := by
  rcases n with _ | _ | n
  · erw [Φ_zero]
    exact ⟨natDegree_one.le, coeff_one_zero⟩
  · erw [Φ_one]
    exact ⟨natDegree_X_le, coeff_X⟩
  · have h1 := W.natDegree_coeff_Ψ'' <| n + 1
    have h2 := W.natDegree_coeff_ΨSq (n + 2 : ℕ)
    have h3 := W.natDegree_coeff_Ψ'' <| n + 3
    simp only [WeierstrassCurve.Φ, Int.natAbs_cast, Nat.even_add_one, ite_not] at h1 h3 ⊢
    erw [Ψ'_ofNat, ← Nat.cast_sub <| by linarith only, Ψ'_ofNat, Nat.add_sub_cancel]
    by_cases hn : Even n
    · rcases even_iff_exists_two_mul.mp hn with ⟨m, rfl⟩
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
          natDegree_mul_le_of_le (natDegree_mul_le_of_le h3.left h1.left) W.natDegree_Ψ₂Sq using 1
        convert (max_self _).symm using 2 <;> ring1
      · rw [coeff_sub, show (2 * m + 3) ^ 2 = 4 * (m + 1) * (m + 2) + 1 by ring1, coeff_X_mul,
          h2.right, show _ + _ = (2 * (m + 1) * (m + 3)) + (2 * m * (m + 2)) + 3 by ring1,
          coeff_mul_of_natDegree_le (natDegree_mul_le_of_le h3.left h1.left) W.natDegree_Ψ₂Sq,
          coeff_mul_of_natDegree_le h3.left h1.left, h3.right, h1.right, coeff_Ψ₂Sq]
        push_cast
        ring1

private lemma natDegree_coeff_Φ (n : ℤ) :
    (W.Φ n).natDegree ≤ n.natAbs ^ 2 ∧ (W.Φ n).coeff (n.natAbs ^ 2) = 1 := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · exact W.natDegree_coeff_Φ_ofNat n
  · simpa only [Φ_neg, Int.natAbs_neg] using W.natDegree_coeff_Φ_ofNat n

lemma natDegree_Φ (n : ℤ) : (W.Φ n).natDegree ≤ n.natAbs ^ 2 :=
  (W.natDegree_coeff_Φ n).left

lemma coeff_Φ (n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) = 1 :=
  (W.natDegree_coeff_Φ n).right

/-! ### The bivariate polynomials $\psi_n$ -/

/-- The bivariate $n$-division polynomials $\psi_n$. -/
protected noncomputable def ψ (n : ℤ) : R[X][Y] :=
  normEDS W.ψ₂ (C W.Ψ₃) (C W.Ψ₄') n

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
lemma ψ_four : W.ψ 4 = C W.Ψ₄' * W.ψ₂ :=
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

/-! ### The bivariate polynomials $\phi_n$ -/

/-- The bivariate polynomials $\phi_n$. -/
protected noncomputable def φ (n : ℤ) : R[X][Y] :=
  C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)

@[simp]
lemma φ_zero : W.φ 0 = 1 := by
  erw [WeierstrassCurve.φ, ψ_zero, zero_pow two_ne_zero, mul_zero, zero_sub, ψ_one, one_mul,
    zero_sub, ψ_neg, neg_neg, ψ_one]

@[simp]
lemma φ_one : W.φ 1 = C X := by
  erw [WeierstrassCurve.φ, ψ_one, one_pow, mul_one, ψ_zero, mul_zero, sub_zero]

@[simp]
lemma φ_two : W.φ 2 = C X * W.ψ₂ ^ 2 - C W.Ψ₃ := by
  erw [WeierstrassCurve.φ, ψ_two, ψ_three, ψ_one, mul_one]

@[simp]
lemma φ_three : W.φ 3 = C X * C W.Ψ₃ ^ 2 - C W.Ψ₄' * W.ψ₂ ^ 2 := by
  erw [WeierstrassCurve.φ, ψ_three, ψ_four, mul_assoc, ψ_two, ← sq]

@[simp]
lemma φ_four : W.φ 4 = C X * C W.Ψ₄' ^ 2 * W.ψ₂ ^ 2 - C W.Ψ₄' * W.ψ₂ ^ 4 * C W.Ψ₃ + C W.Ψ₃ ^ 4 := by
  erw [WeierstrassCurve.φ, ψ_four, show (4 + 1 : ℤ) = 2 * 2 + 1 by rfl, ψ_odd, ψ_four, ψ_two, ψ_one,
    ψ_three]
  ring1

@[simp]
lemma φ_neg (n : ℤ) : W.φ (-n) = W.φ n := by
  rw [WeierstrassCurve.φ, ψ_neg, neg_sq (R := R[X][Y]), neg_add_eq_sub, ← neg_sub n, ψ_neg,
    ← neg_add', ψ_neg, neg_mul_neg (α := R[X][Y]), mul_comm <| W.ψ _, WeierstrassCurve.φ]

end WeierstrassCurve
