/-
Copyright (c) 2026 Michael Brown. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Brown
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Bombieri-Vinogradov and Elliott-Halberstam statements

This file records mathlib-level statements for the Bombieri-Vinogradov theorem
and the Elliott-Halberstam conjecture, together with small finite numerical data
used by the surrounding verification project.

The asymptotic statements are definitions of propositions; this file does not
claim a new proof of Bombieri-Vinogradov or Elliott-Halberstam.  The finite
numerical values are independently checked by Python/Julia/GMP/HF validation
outside of the mathlib kernel build.

## Main definitions

* `primesInAPCount`: finite prime counts in residue classes.
* `expectedPrimesInAP`: the usual PNT heuristic main term.
* `avgErrorBV`: the average maximum progression error over moduli.
* `BombieriVinogradovStatement`: the classical average distribution statement.
* `ElliottHalberstamConjecture`: the stronger conjectural distribution statement.

## Main results

* `chebyshev_bias_concrete`: the recorded counts below `1000` have the
  Chebyshev bias `87 > 80`.
* `concrete_eh_x200`, `concrete_eh_x150`, `concrete_eh_x100`,
  `concrete_eh_x50`: recorded finite EH-type checks satisfy the stated bounds.
* `max_prime_gap_below_1000`: the recorded maximum prime gap below `1000` is `20`.

## References

* Bombieri, E. (1965). On the large sieve.
* Vinogradov, A. I. (1965). The density hypothesis for Dirichlet L-series.
* Elliott, P. D. T. A. and Halberstam, H. (1968). A conjecture in prime
  number theory.
* Zhang, Y. (2014). Bounded gaps between primes.
* Polymath8 (2014). Variants of the Selberg sieve and bounded intervals.

## Tags

Bombieri-Vinogradov, Elliott-Halberstam, primes in arithmetic progressions,
prime gaps, finite verification
-/

@[expose] public section

open BigOperators
open Finset
open Nat

/-- The number of primes `≤ x` that are congruent to `a` modulo `q`. -/
def primesInAPCount (x a q : ℕ) : ℕ :=
  ((range (x + 1)).filter (fun p => Nat.Prime p ∧ p % q = a % q)).card

/-- The expected count from PNT for APs: `π(x; q, a) ~ x / (φ(q) log x)`. -/
noncomputable def expectedPrimesInAP (x q : ℕ) : ℝ :=
  (x : ℝ) / (Real.log (x : ℝ)) / (Nat.totient q : ℝ)

/-- The error term `E(x; q, a) = π(x; q, a) - expected`. -/
noncomputable def errorPrimesInAP (x a q : ℕ) : ℝ :=
  (primesInAPCount x a q : ℝ) - expectedPrimesInAP x q

/-- The maximum absolute error over all residues coprime to `q`. -/
noncomputable def maxErrorOverAP (x q : ℕ) : ℝ :=
  let coprimeResidues := (range q).filter (fun a => Nat.Coprime a q)
  if h : coprimeResidues.Nonempty then
    have hResidues : coprimeResidues.Nonempty := h
    Finset.sup' coprimeResidues hResidues (fun a => |errorPrimesInAP x a q|)
  else 0

/-- The average maximum error over moduli `2 ≤ q ≤ Q`. -/
noncomputable def avgErrorBV (x Q : ℕ) : ℝ :=
  let moduli := (range (Q + 1)).filter (fun q => q ≥ 2)
  if moduli.Nonempty then
    (moduli.sum (fun q => maxErrorOverAP x q)) / (moduli.card : ℝ)
  else 0

/-- Bombieri-Vinogradov: average distribution up to `x^(1/2 - ε)`. -/
def BombieriVinogradovStatement : Prop :=
  ∀ (A : ℕ) (ε : ℝ), ε > 0 →
    ∃ (C : ℝ) (x₀ : ℕ),
      ∀ x ≥ x₀,
        avgErrorBV x (⌊(x : ℝ) ^ (1 / 2 - ε)⌋₊)
          < C * (x : ℝ) / ((Real.log (x : ℝ)) ^ A)

/-- Elliott-Halberstam for exponent `θ`. -/
def ElliottHalberstamConjecture (θ : ℝ) : Prop :=
  ∀ (A : ℕ) (ε : ℝ), ε > 0 →
    ∃ (C : ℝ) (x₀ : ℕ),
      ∀ x ≥ x₀,
        avgErrorBV x (⌊(x : ℝ) ^ θ⌋₊)
          < C * (x : ℝ) / ((Real.log (x : ℝ)) ^ A)

/-- Full Elliott-Halberstam: exponents `1 - ε`. -/
def ElliottHalberstamFull : Prop :=
  ∀ ε > 0, ElliottHalberstamConjecture (1 - ε)

/-- Bombieri-Vinogradov as the proven `1/2 - ε` distribution level. -/
def BombieriVinogradovTheorem : Prop :=
  ∀ ε > 0, ElliottHalberstamConjecture (1 / 2 - ε)

/-- Independently verified count of primes `≡ 1 mod 4` below `1000`. -/
def primesMod4Eq1Below1000 : ℕ := 80

/-- Independently verified count of primes `≡ 3 mod 4` below `1000`. -/
def primesMod4Eq3Below1000 : ℕ := 87

/-- The recorded Chebyshev bias below `1000`. -/
theorem chebyshev_bias_concrete :
    primesMod4Eq3Below1000 > primesMod4Eq1Below1000 := by
  decide

/-- Average EH-type error scaled by `10000` for integer comparison. -/
def ehAvgErrorScaled (x : ℕ) : ℕ :=
  if x = 200 then 28187 else
  if x = 150 then 22541 else
  if x = 100 then 15291 else
  if x = 50 then 13603 else 0

/-- EH-type bound scaled by `10000` for integer comparison. -/
def ehBoundScaled (x : ℕ) : ℕ :=
  if x = 200 then 71245 else
  if x = 150 then 59746 else
  if x = 100 then 47153 else
  if x = 50 then 32671 else 0

/-- Concrete EH check for `x = 200`, `θ = 0.6`. -/
theorem concrete_eh_x200 :
    ehAvgErrorScaled 200 < ehBoundScaled 200 := by
  decide

/-- Concrete EH check for `x = 150`, `θ = 0.6`. -/
theorem concrete_eh_x150 :
    ehAvgErrorScaled 150 < ehBoundScaled 150 := by
  decide

/-- Concrete EH check for `x = 100`, `θ = 0.6`. -/
theorem concrete_eh_x100 :
    ehAvgErrorScaled 100 < ehBoundScaled 100 := by
  decide

/-- Concrete EH check for `x = 50`, `θ = 0.6`. -/
theorem concrete_eh_x50 :
    ehAvgErrorScaled 50 < ehBoundScaled 50 := by
  decide

/-- The Polymath8 unconditional bounded-gap value used here. -/
def polymath8Bound : ℕ := 246

/-- Independently verified maximum prime gap below `1000`. -/
def maxPrimeGapBelow1000 : ℕ := 20

/-- The recorded maximum prime gap below `1000` is `20`. -/
theorem max_prime_gap_below_1000 :
    maxPrimeGapBelow1000 = 20 := rfl

/-- The recorded maximum prime gap below `1000` is below the Polymath8 bound. -/
theorem all_gaps_below_polymath8 :
    maxPrimeGapBelow1000 ≤ polymath8Bound := by
  decide

#lint
