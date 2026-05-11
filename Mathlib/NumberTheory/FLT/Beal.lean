/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.FLT.Polynomial
public import Mathlib.Tactic.LinearCombination

/-!
# Statement of Beal's Conjecture and its polynomial corollary

This file states Beal's conjecture as `Prop` predicates, analogous to
`FermatLastTheoremFor` and friends in `Mathlib.NumberTheory.FLT.Basic`, and
derives the polynomial version (coprime case) as a corollary of
`Polynomial.flt_catalan`.

## Main definitions

* `BealConjectureWith R p q r` : The statement that the only solutions to
  `a ^ p + b ^ q = c ^ r` in the semiring `R` have `a = 0`, `b = 0` or `c = 0`.
  Note that this can be false for specific choices of `R, p, q, r` (for example
  `BealConjectureWith ℕ 0 3 2` is false as `1^0 + 2^3 = 3^2`).
* `BealConjectureFor p q r` : The same statement over `ℕ`.
* `BealConjecture` : The full Beal conjecture proper: for all `p, q, r ≥ 3` and
  coprime positive naturals `a, b, c`, `a^p + b^q ≠ c^r`.

## Main results

* `bealConjectureWith_eq_fermat`, `bealConjectureFor_eq_fermat` : at equal
  exponents `p = q = r = n`, Beal coincides with `FermatLastTheoremWith` /
  `FermatLastTheoremFor`.
* `beal_hyperbolicity` : `q*r + r*p + p*q ≤ p*q*r` whenever `p, q, r ≥ 3`
  (equivalent to `1/p + 1/q + 1/r ≤ 1`). Required as input to
  `Polynomial.flt_catalan`.
* `bealConjecture_polynomial_coprime` : Beal for polynomials over a field, in
  the coprime case, with characteristic coprime to `p*q*r` and exponents `≥ 3`.
  Direct specialisation of `Polynomial.flt_catalan` with coefficients `(1, 1, -1)`.

## History

Beal's conjecture was formulated in 1993 by D. Andrew Beal as a generalisation
of Fermat's Last Theorem. A US$1 000 000 prize, administered by the American
Mathematical Society, is offered for a proof or counterexample
(see [A. Mauldin, *A Generalization of Fermat's Last Theorem: The Beal
Conjecture and Prize Problem*, Notices AMS 44 (1997), 1436-1437]).

Computational verification by Peter Norvig (2000, updated 2015) excludes
primitive counterexamples with `A, B, C ≤ 250 000` for exponents `≤ 7`, and
with `A, B, C ≤ 10 000` for exponents `≤ 100`. Many specific exponent
signatures `(p, q, r)` have been settled by Frey-Hellegouarch curve + modularity
techniques (Bennett-Chen-Dahmen-Yazdani 2015, Dahmen-Siksek 2014,
Grechuk-Ratcliffe 2024 catalog over 100 solved signatures).

The non-coprime case of polynomial Beal does not follow trivially from the
coprime case here, unlike for polynomial Fermat: factoring `gcd(a, b)` out of
`a^p + b^q = c^r` does not yield a clean equation when the exponents `p, q, r`
differ. We leave that extension as future work.
-/

public section

open Polynomial

/-- Statement of Beal's conjecture over a given semiring with specific exponents.
For nonzero `a b c : R`, the equation `a ^ p + b ^ q = c ^ r` has no solutions.

Note that this statement can be false for certain choices of `R, p, q, r`.
For example `BealConjectureWith ℕ 0 3 2` is false, as `1^0 + 2^3 = 3^2`. -/
def BealConjectureWith (R : Type*) [Semiring R] (p q r : ℕ) : Prop :=
  ∀ a b c : R, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ p + b ^ q ≠ c ^ r

/-- Statement of Beal's conjecture over the naturals for fixed exponents. -/
def BealConjectureFor (p q r : ℕ) : Prop := BealConjectureWith ℕ p q r

/-- Statement of Beal's conjecture: for all `p, q, r ≥ 3` and coprime positive
naturals `a, b, c`, the equation `a ^ p + b ^ q = c ^ r` has no solutions.

Encodes primitivity via `Nat.gcd (Nat.gcd a b) c = 1`, equivalent (contrapositive)
to the original "any solution shares a common prime factor" formulation. -/
def BealConjecture : Prop :=
  ∀ p q r : ℕ, 3 ≤ p → 3 ≤ q → 3 ≤ r →
    ∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd (Nat.gcd a b) c = 1 → a ^ p + b ^ q ≠ c ^ r

/-- Beal at `p = q = r = n` is exactly Fermat's Last Theorem with exponent `n`. -/
lemma bealConjectureWith_eq_fermat (R : Type*) [Semiring R] (n : ℕ) :
    BealConjectureWith R n n n ↔ FermatLastTheoremWith R n := by
  rfl

/-- Same equivalence over `ℕ`. -/
lemma bealConjectureFor_eq_fermat (n : ℕ) :
    BealConjectureFor n n n ↔ FermatLastTheoremFor n := by
  rfl

/-- `BealConjectureFor 0 3 2` is false: `1^0 + 2^3 = 1 + 8 = 9 = 3^2`. This is
the simplest witness that dropping the `≥ 3` exponent hypothesis breaks Beal. -/
lemma not_bealConjectureFor_zero_three_two : ¬ BealConjectureFor 0 3 2 := by
  intro h
  exact h 1 2 3 (by decide) (by decide) (by decide) (by decide)

/-- The hyperbolicity inequality `q*r + r*p + p*q ≤ p*q*r` holds whenever
`p, q, r ≥ 3`. Equivalent to `1/p + 1/q + 1/r ≤ 1` (the Darmon-Granville
hyperbolic case). Required as a hypothesis of `Polynomial.flt_catalan`. -/
lemma beal_hyperbolicity {p q r : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 3 ≤ r) :
    q * r + r * p + p * q ≤ p * q * r := by
  zify
  nlinarith [hp, hq, hr,
    mul_nonneg (by linarith : (0:ℤ) ≤ (q:ℤ)) (by linarith : (0:ℤ) ≤ (r:ℤ)),
    mul_nonneg (by linarith : (0:ℤ) ≤ (p:ℤ)) (by linarith : (0:ℤ) ≤ (r:ℤ)),
    mul_nonneg (by linarith : (0:ℤ) ≤ (p:ℤ)) (by linarith : (0:ℤ) ≤ (q:ℤ))]

variable {k : Type*} [Field k]

/-- **Polynomial Beal (coprime case).** For polynomials `a, b, c` over a field
`k`, with `p, q, r ≥ 3` coprime to `char k`, `a, b, c` pairwise nonzero, and
`a, b` coprime: if `a^p + b^q = c^r`, then all three polynomials are constants
(i.e. `natDegree = 0`).

This is the polynomial version of Beal's conjecture, derived directly from
`Polynomial.flt_catalan` (specialisation to coefficients `u = 1, v = 1, w = -1`).
-/
theorem bealConjecture_polynomial_coprime
    {p q r : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 3 ≤ r)
    (chp : (p : k) ≠ 0) (chq : (q : k) ≠ 0) (chr : (r : k) ≠ 0)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (heq : a ^ p + b ^ q = c ^ r) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  have hp' : p ≠ 0 := by omega
  have hq' : q ≠ 0 := by omega
  have hr' : r ≠ 0 := by omega
  have hineq : q * r + r * p + p * q ≤ p * q * r := beal_hyperbolicity hp hq hr
  -- Restate `a^p + b^q = c^r` as `1·a^p + 1·b^q + (-1)·c^r = 0`
  -- to match the `flt_catalan` signature.
  have heq' : C (1 : k) * a ^ p + C (1 : k) * b ^ q + C (-1 : k) * c ^ r = 0 := by
    simp only [map_one, one_mul, map_neg, neg_mul]
    linear_combination heq
  exact Polynomial.flt_catalan hp' hq' hr' hineq chp chq chr ha hb hc hab
    one_ne_zero one_ne_zero (neg_ne_zero.mpr one_ne_zero) heq'
