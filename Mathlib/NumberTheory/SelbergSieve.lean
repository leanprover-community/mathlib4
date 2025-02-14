/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.NumberTheory.ArithmeticFunction

/-!
# The Selberg Sieve

We set up the working assumptions of the Selberg sieve and define the notion of an upper bound sieve
and show that every upper bound sieve yields an upper bound on the size of the sifted set. We also
define the Λ² sieve and prove that Λ² sieves are upper bound sieves. We then diagonalise the main
term of the Λ² sieve.

We mostly follow the treatment outlined by Heath-Brown in the notes to an old graduate course. One
minor notational difference is that we write $\nu(n)$ in place of $\frac{\omega(n)}{n}$.

## Results
 * `siftedSum_le_mainSum_errSum_of_UpperBoundSieve` - Every upper bound sieve gives an upper bound
 on the size of the sifted set in terms of `mainSum` and `errSum`
 * `upperMoebius_of_lambda_sq` - Lambda squared weights produce upper bound sieves

## Notation
The `SelbergSieve.Notation` namespace includes common shorthand for the variables included in the
`SelbergSieve` structure.
 * `A` for `support`
 * `𝒜 d` for `multSum d`
 * `P` for `prodPrimes`
 * `a` for `weights`
 * `X` for `totalMass`
 * `ν` for `nu`
 * `y` for `level`
 * `R d` for `rem d`
 * `g d` for `selbergTerms d`

## References

 * [Heath-Brown, *Lectures on sieves*][heathbrown2002lecturessieves]
 * [Koukoulopoulos, *The Distribution of Prime Numbers*][MR3971232]

-/

noncomputable section

open scoped BigOperators ArithmeticFunction

open Finset Real Nat

/--
We set up the Selberg sieve as follows. Take a finite set of natural numbers `A`, whose elements
are weighted by a sequence `a n`. Also take a finite set of primes `P`, represented as a squarefree
natural number. These are the primes that we will sift from our set `A`. Suppose we can approximate
`∑ n ∈ {k ∈ A | d ∣ k}, a n = ν d * X + R d`, where `X` is an approximation to the total size of `A`
and `ν` is a multiplicative arithmetic function such that `0 < ν p < 1` for all primes `p ∣ P`.

Then the fundamental theorem of the Selberg sieve will give us an upper bound on the size of the
sifted sum `∑ n ∈ {k ∈ support | k.Coprime P}, a n`, obtained by removing any elements of `A` that
are a multiple of a prime in `P`.
-/
class SelbergSieve where
  support : Finset ℕ
  prodPrimes : ℕ
  prodPrimes_squarefree : Squarefree prodPrimes
  weights : ℕ → ℝ
  weights_nonneg : ∀ n : ℕ, 0 ≤ weights n
  totalMass : ℝ
  nu : ArithmeticFunction ℝ
  nu_mult : nu.IsMultiplicative
  nu_pos_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → 0 < nu p
  nu_lt_one_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → nu p < 1
  level : ℝ
  one_le_level : 1 ≤ level

attribute [arith_mult] SelbergSieve.nu_mult

namespace SelbergSieve

namespace Notation

scoped notation3 "ν" => nu
scoped notation3 "P" => prodPrimes
scoped notation3 "a" => weights
scoped notation3 "X" => totalMass
scoped notation3 "A" => support
scoped notation3 "y" => level
scoped notation3 "hy" => one_le_level

end Notation

open Notation

variable [s : SelbergSieve]

/-! Lemmas aboud $P$. -/

theorem prodPrimes_ne_zero : P ≠ 0 :=
  Squarefree.ne_zero prodPrimes_squarefree

theorem squarefree_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd prodPrimes_squarefree

theorem squarefree_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : Squarefree d := by
  simp only [Nat.mem_divisors] at hd
  exact Squarefree.squarefree_of_dvd hd.left prodPrimes_squarefree

/-! Lemmas about $\nu$. -/

theorem prod_primeFactors_nu {d : ℕ} (hd : d ∣ P) : ∏ p ∈ d.primeFactors, ν p = ν d := by
  rw [← nu_mult.map_prod_of_subset_primeFactors _ _ subset_rfl,
    Nat.prod_primeFactors_of_squarefree <| Squarefree.squarefree_of_dvd hd prodPrimes_squarefree]

theorem nu_pos_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : 0 < ν d := by
  calc
    0 < ∏ p ∈ d.primeFactors, ν p := by
      apply prod_pos
      intro p hpd
      have hp_prime : p.Prime := prime_of_mem_primeFactors hpd
      have hp_dvd : p ∣ P := (dvd_of_mem_primeFactors hpd).trans hd
      exact nu_pos_of_prime p hp_prime hp_dvd
    _ = ν d := prod_primeFactors_nu hd

theorem nu_ne_zero {d : ℕ} (hd : d ∣ P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  exact nu_pos_of_dvd_prodPrimes hd

theorem nu_ne_zero_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  rw [mem_divisors] at hd
  apply nu_pos_of_dvd_prodPrimes hd.left

theorem nu_lt_self_of_dvd_prodPrimes (d : ℕ) (hdP : d ∣ P) (hd_ne_one : d ≠ 1) : ν d < 1 := by
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP prodPrimes_squarefree
  have := hd_sq.ne_zero
  calc
    ν d = ∏ p ∈ d.primeFactors, ν p := (prod_primeFactors_nu hdP).symm
    _ < ∏ p ∈ d.primeFactors, 1 := by
      apply prod_lt_prod_of_nonempty
      · intro p hp
        simp only [mem_primeFactors] at hp
        apply nu_pos_of_prime p hp.1 (hp.2.1.trans hdP)
      · intro p hpd; rw [mem_primeFactors_of_ne_zero hd_sq.ne_zero] at hpd
        apply nu_lt_one_of_prime p hpd.left (hpd.2.trans hdP)
      · simp only [nonempty_primeFactors, show 1 < d by omega]
    _ = 1 := by
      simp

@[simp]
def multSum (d : ℕ) : ℝ :=
  ∑ n ∈ A, if d ∣ n then a n else 0

scoped [SelbergSieve.Notation] notation3 "𝒜" => multSum

-- A_d = ν (d)/d X + R_d
@[simp]
def rem (d : ℕ) : ℝ :=
  𝒜 d - ν d * X

scoped [SelbergSieve.Notation] notation3 "R" => rem

def siftedSum : ℝ :=
  ∑ d ∈ A, if Coprime P d then a d else 0

/-! We will write the sifted -/
def mainSum (muPlus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ divisors P, muPlus d * ν d

def errSum (muPlus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ divisors P, |muPlus d| * |R d|

theorem multSum_eq_main_err (d : ℕ) : multSum d = ν d * X + R d := by
  dsimp [rem]
  ring

theorem siftedSum_as_delta : siftedSum = ∑ d ∈ support, a d * if Nat.gcd P d = 1 then 1 else 0 :=
  by
  dsimp only [siftedSum]
  simp_rw [mul_ite, mul_one, mul_zero]

omit s in
/-! A sequence of coefficients $\mu^{+}$ is upper Moebius if $\mu * \zeta ≤ \mu^{+} * \zeta$. These
  coefficients then yield an upper bound on the sifted sum.-/
def UpperMoebius (muPlus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (if n=1 then 1 else 0) ≤ ∑ d ∈ n.divisors, muPlus d

theorem upper_bound_of_UpperMoebius (muPlus : ℕ → ℝ) (h : UpperMoebius muPlus) :
    siftedSum ≤ ∑ d ∈ divisors P, muPlus d * multSum d := by
  have hμ : ∀ n, (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, muPlus d := h
  calc siftedSum ≤
    ∑ n ∈ support, a n * ∑ d ∈ (Nat.gcd P n).divisors, muPlus d := ?caseA
    _ = ∑ n ∈ support, ∑ d ∈ divisors P, if d ∣ n then a n * muPlus d else 0 := ?caseB
    _ = ∑ d ∈ divisors P, muPlus d * multSum d := ?caseC
  case caseA =>
    rw [siftedSum_as_delta]
    apply Finset.sum_le_sum; intro n _
    exact mul_le_mul_of_nonneg_left (hμ (Nat.gcd P n)) (weights_nonneg n)
  case caseB =>
    simp_rw [mul_sum, ← sum_filter]
    congr with n
    congr
    · rw [← divisors_filter_dvd_of_dvd prodPrimes_ne_zero (Nat.gcd_dvd_left _ _)]
      ext x; simp +contextual [dvd_gcd_iff]
  case caseC =>
    rw [sum_comm]
    simp_rw [multSum, ← sum_filter, mul_sum, mul_comm]

theorem siftedSum_le_mainSum_errSum_of_UpperMoebius (muPlus : ℕ → ℝ)
    (h : UpperMoebius muPlus) :
    siftedSum ≤ X * mainSum muPlus + errSum muPlus := by
  calc siftedSum ≤ ∑ d ∈ divisors P, muPlus d * multSum d := upper_bound_of_UpperMoebius _ h
   _ ≤ X * ∑ d ∈ divisors P, muPlus d * ν d + ∑ d ∈ divisors P, muPlus d * R d := ?caseA
   _ ≤ _ := ?caseB
  case caseA =>
    apply le_of_eq
    rw [mul_sum, ←sum_add_distrib]
    congr with d
    dsimp only [rem]; ring
  case caseB =>
    apply _root_.add_le_add (le_rfl)
    apply sum_le_sum; intro d _
    rw [←abs_mul]
    exact le_abs_self (muPlus d * R d)

end SelbergSieve
