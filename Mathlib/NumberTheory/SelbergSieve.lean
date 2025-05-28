/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.NumberTheory.ArithmeticFunction

/-!
# The Selberg Sieve

We set up the working assumptions of the Selberg sieve, define the notion of an upper bound sieve
and show that every upper bound sieve yields an upper bound on the size of the sifted set. We also
define the Λ² sieve and prove that Λ² sieves are upper bound sieves. We then diagonalise the main
term of the Λ² sieve.

We mostly follow the treatment outlined by Heath-Brown in the notes to an old graduate course. One
minor notational difference is that we write $\nu(n)$ in place of $\frac{\omega(n)}{n}$.

## Results
* `siftedSum_le_mainSum_errSum_of_UpperBoundSieve` - Every upper bound sieve gives an upper bound
  on the size of the sifted set in terms of `mainSum` and `errSum`

## Notation
The `SelbergSieve.Notation` namespace includes common shorthand for the variables included in the
`SelbergSieve` structure.
* `A` for `support`
* `𝒜 d` for `multSum d` - the combined weight of the elements of `A` that are divisible by `d`
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

/-- We set up a sieve problem as follows. Take a finite set of natural numbers `A`, whose elements
are weighted by a sequence `a n`. Also take a finite set of primes `P`, represented by a squarefree
natural number. These are the primes that we will sift from our set `A`. Suppose we can approximate
`∑ n ∈ {k ∈ A | d ∣ k}, a n = ν d * X + R d`, where `X` is an approximation to the total size of `A`
and `ν` is a multiplicative arithmetic function such that `0 < ν p < 1` for all primes `p ∣ P`.

Then a sieve-type theorem will give us an upper (or lower) bound on the size of the sifted sum
`∑ n ∈ {k ∈ support | k.Coprime P}, a n`, obtained by removing any elements of `A` that are a
multiple of a prime in `P`. -/
structure BoundingSieve where
  /-- The set of natural numbers that is to be sifted. The fundamental lemma yields an upper bound
    on the size of this set after the multiples of small primes have been removed. -/
  support : Finset ℕ
  /-- The finite set of prime numbers whose multiples are to be sifted from `support`. We work with
    their product because it lets us treat `nu` as a multiplicative arithmetic function. It also
    plays well with Moebius inversion. -/
  prodPrimes : ℕ
  prodPrimes_squarefree : Squarefree prodPrimes
  /-- A sequence representing how much each element of `support` should be weighted. -/
  weights : ℕ → ℝ
  weights_nonneg : ∀ n : ℕ, 0 ≤ weights n
  /-- An approximation to `∑ i in support, weights i`, i.e. the size of the unsifted set. A bad
    approximation will yield a weak statement in the final theorem. -/
  totalMass : ℝ
  /-- `nu d` is an approximation to the proportion of elements of `support` that are a multiple of
    `d` -/
  nu : ArithmeticFunction ℝ
  nu_mult : nu.IsMultiplicative
  nu_pos_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → 0 < nu p
  nu_lt_one_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → nu p < 1

/-- The Selberg upper bound sieve in particular introduces a parameter called the `level` which
  gives the user control over the size of the error term. -/
structure SelbergSieve extends BoundingSieve where
  /-- The `level` of the sieve controls how many terms we include in the inclusion-exclusion type
    sum. A higher level will yield a tighter bound for the main term, but will also increase the
    size of the error term. -/
  level : ℝ
  one_le_level : 1 ≤ level

attribute [arith_mult] BoundingSieve.nu_mult

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `BoundingSieve.weights`. -/
@[positivity BoundingSieve.weights _ _]
def evalBoundingSieveWeights : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@BoundingSieve.weights $s $n) =>
    assertInstancesCommute
    pure (.nonnegative q(BoundingSieve.weights_nonneg $s $n))
  | _, _, _ => throwError "not BoundingSieve.weights"

end Mathlib.Meta.Positivity

open BoundingSieve

variable {s : BoundingSieve}

-- private abbrev BoundingSieve.ν := BoundingSieve.nu

-- private abbrev BoundingSieve.P := BoundingSieve.prodPrimes

set_option quotPrecheck false
set_option hygiene false

@[inherit_doc nu]
local macro "ν" : term => `(s.nu)
@[inherit_doc prodPrimes]
local macro "P" : term => `(s.prodPrimes)
@[inherit_doc weights]
local macro "a" : term => `(s.weights)
@[inherit_doc totalMass]
local macro "X" : term => `(s.totalMass)
@[inherit_doc support]
local macro "A" : term => `(s.support)

@[inherit_doc SelbergSieve.level]
local macro "y" : term => `(s.level)

open Lean PrettyPrinter Delaborator SubExpr

@[local app_unexpander nu, inherit_doc nu]
def unexpanderNu : Unexpander
  | `($_nu $_s) => `(ν)
  | `($fn) => `($fn)

@[local app_unexpander prodPrimes, inherit_doc prodPrimes]
def unexpanderProdPrimes : Unexpander
  | `($_ $_s) => `(P)
  | `($fn) => `($fn)

@[local app_unexpander weights, inherit_doc weights]
def unexpanderWeights : Unexpander
  | `($_ $_s $n) => `(a $n)
  | `($_ $_s) => `(a)
  | `($fn) => `($fn)

@[local app_unexpander totalMass, inherit_doc totalMass]
def unexpanderTotalMass : Unexpander
  | `($_ $_s) => `(X)
  | `($fn) => `($fn)

@[local app_unexpander support, inherit_doc support]
def unexpanderSupport : Unexpander
  | `($_ $_s) => `(A)
  | `($fn) => `($fn)

@[local app_unexpander SelbergSieve.level, inherit_doc SelbergSieve.level]
def unexpanderLevel : Unexpander
  | `($_level $_s) => `(y)
  | `($level) => `($level)



theorem SelbergSieve.one_le_y {s : SelbergSieve} : 1 ≤ y := s.one_le_level


namespace BoundingSieve
/-! Lemmas about $P$. -/

theorem prodPrimes_ne_zero : P ≠ 0 := by
  apply Squarefree.ne_zero s.prodPrimes_squarefree

theorem squarefree_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree

theorem squarefree_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : Squarefree d := by
  simp only [Nat.mem_divisors] at hd
  exact Squarefree.squarefree_of_dvd hd.left s.prodPrimes_squarefree

/-! Lemmas about $\nu$. -/

theorem prod_primeFactors_nu {d : ℕ} (hd : d ∣ P) : ∏ p ∈ d.primeFactors, ν p = ν d := by
  rw [← s.nu_mult.map_prod_of_subset_primeFactors _ _ subset_rfl,
    Nat.prod_primeFactors_of_squarefree <| Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree]

theorem nu_pos_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : 0 < ν d := by
  calc
    0 < ∏ p ∈ d.primeFactors, ν p := by
      apply prod_pos
      intro p hpd
      have hp_prime : p.Prime := prime_of_mem_primeFactors hpd
      have hp_dvd : p ∣ P := (dvd_of_mem_primeFactors hpd).trans hd
      exact s.nu_pos_of_prime p hp_prime hp_dvd
    _ = ν d := prod_primeFactors_nu hd

theorem nu_ne_zero {d : ℕ} (hd : d ∣ P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  exact nu_pos_of_dvd_prodPrimes hd

theorem nu_lt_one_of_dvd_prodPrimes {d : ℕ} (hdP : d ∣ P) (hd_ne_one : d ≠ 1) : ν d < 1 := by
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
  have := hd_sq.ne_zero
  calc
    ν d = ∏ p ∈ d.primeFactors, ν p := (prod_primeFactors_nu hdP).symm
    _ < ∏ p ∈ d.primeFactors, 1 := by
      apply prod_lt_prod_of_nonempty
      · intro p hp
        simp only [mem_primeFactors] at hp
        apply s.nu_pos_of_prime p hp.1 (hp.2.1.trans hdP)
      · intro p hpd; rw [mem_primeFactors_of_ne_zero hd_sq.ne_zero] at hpd
        apply s.nu_lt_one_of_prime p hpd.left (hpd.2.trans hdP)
      · simp only [nonempty_primeFactors, show 1 < d by omega]
    _ = 1 := by
      simp

variable (s) in
/-- The weight of all the elements that are a multiple of `d`. -/
@[simp]
def multSum (d : ℕ) : ℝ := ∑ n ∈ A, if d ∣ n then a n else 0

@[inherit_doc multSum]
local macro "𝒜" : term => `(s.multSum)

@[local app_unexpander multSum, inherit_doc multSum]
def unexpanderMultSum : Unexpander
  | `($_ $_s $n) => `(𝒜 $n)
  | `($_ $_s) => `(𝒜)
  | `($fn) => `($fn)

variable (s) in
/-- The remainder term in the approximation A_d = ν (d) X + R_d. This is the degree to which `nu`
  fails to approximate the proportion of the weight that is a multiple of `d`. -/
@[simp]
def rem (d : ℕ) : ℝ := 𝒜 d - ν d * X

@[inherit_doc rem]
local macro "R" : term => `(s.rem)

@[local app_unexpander rem, inherit_doc rem]
def unexpanderRem : Unexpander
  | `($_ $_s $n) => `(R $n)
  | `($_ $_s) => `(R)
  | `($fn) => `($fn)

/-- The weight of all the elements that are not a multiple of any of our finite set of primes. -/
def siftedSum : ℝ := ∑ d ∈ A, if Coprime P d then a d else 0

/-- `X * mainSum μ⁺` is the main term in the upper bound on `sifted_sum`. -/
def mainSum (muPlus : ℕ → ℝ) : ℝ := ∑ d ∈ divisors P, muPlus d * ν d

/-- `errSum μ⁺` is the error term in the upper bound on `sifted_sum`. -/
def errSum (muPlus : ℕ → ℝ) : ℝ := ∑ d ∈ divisors P, |muPlus d| * |R d|

theorem multSum_eq_main_err (d : ℕ) : 𝒜 d = ν d * X + R d := by
  dsimp [rem]
  ring

theorem siftedsum_eq_sum_support_mul_ite :
    s.siftedSum = ∑ d ∈ A, a d * if Nat.gcd P d = 1 then 1 else 0 := by
  dsimp only [siftedSum]
  simp_rw [mul_ite, mul_one, mul_zero]

omit s in
/-- A sequence of coefficients $\mu^{+}$ is upper Moebius if $\mu * \zeta ≤ \mu^{+} * \zeta$. These
  coefficients then yield an upper bound on the sifted sum. -/
def IsUpperMoebius (muPlus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (if n=1 then 1 else 0) ≤ ∑ d ∈ n.divisors, muPlus d


theorem siftedSum_le_sum_of_upperMoebius (muPlus : ℕ → ℝ) (h : IsUpperMoebius muPlus) :
    s.siftedSum ≤ ∑ d ∈ divisors P, muPlus d * 𝒜 d := by
  have hμ : ∀ n, (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, muPlus d := h
  calc siftedSum ≤
    ∑ n ∈ A, a n * ∑ d ∈ (Nat.gcd P n).divisors, muPlus d := ?caseA
    _ = ∑ n ∈ A, ∑ d ∈ divisors P, if d ∣ n then a n * muPlus d else 0 := ?caseB
    _ = ∑ d ∈ divisors P, muPlus d * 𝒜 d := ?caseC
  case caseA =>
    rw [siftedsum_eq_sum_support_mul_ite]
    gcongr with n
    exact hμ (Nat.gcd P n)
  case caseB =>
    simp_rw [mul_sum, ← sum_filter]
    congr with n
    congr
    · rw [← divisors_filter_dvd_of_dvd prodPrimes_ne_zero (Nat.gcd_dvd_left _ _)]
      ext x; simp +contextual [dvd_gcd_iff]
  case caseC =>
    rw [sum_comm]
    simp_rw [multSum, ← sum_filter, mul_sum, mul_comm]

theorem siftedSum_le_mainSum_errSum_of_upperMoebius (muPlus : ℕ → ℝ) (h : IsUpperMoebius muPlus) :
    s.siftedSum ≤ X * s.mainSum muPlus + s.errSum muPlus := calc
  siftedSum ≤ ∑ d ∈ divisors P, muPlus d * 𝒜 d :=
    siftedSum_le_sum_of_upperMoebius _ h
  _ = X * mainSum muPlus + ∑ d ∈ divisors P, muPlus d * R d := by
    rw [mainSum, mul_sum, ←sum_add_distrib]
    congr with d
    dsimp only [rem]; ring
  _ ≤ X * mainSum muPlus + errSum muPlus := by
    rw [errSum]
    gcongr _ + ∑ d ∈ _, ?_ with d
    rw [←abs_mul]
    exact le_abs_self (muPlus d * R d)

end BoundingSieve
