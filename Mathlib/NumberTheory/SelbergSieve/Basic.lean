/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module sieve
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.SelbergSieve.Temp

/-!
# The Selberg Sieve

We set up the working assumptions of the Selberg sieve and define the notion of an upper bound sieve
and show that every upper bound sieve yields an upper bound on the size of the sifted set. We also
define the Λ² sieve and prove that Λ² sieves are upper bound sieves. We then diagonalise the main
term of the Λ² sieve.

We mostly follow the treatment outlined by Heath-Brown in the notes to an old graduate course. One
minor notational difference is that we write $\nu(n)$ in place of $\frac{\omega(n)}{n}$.

## Results


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

open Finset Real Nat Aux


/-!
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

section SelbergSieve

variable [s : SelbergSieve]

@[simp]
def multSum (d : ℕ) : ℝ :=
  ∑ n in A, if d ∣ n then a n else 0

scoped notation3 "𝒜" => multSum

-- A_d = ν (d)/d X + R_d
@[simp]
def rem (d : ℕ) : ℝ :=
  𝒜 d - ν d * X

scoped notation3 "R" => rem

def siftedSum : ℝ :=
  ∑ d in A, if Coprime P d then a d else 0

/-!
These are the terms that appear in the sum `S` in the main term of the fundamental theorem.

$S = ∑_{l|P, l≤\sqrt{y}} g(l)$
-/
def selbergTerms : ArithmeticFunction ℝ :=
  nu.pmul (.prodPrimeFactors fun p =>  1 / (1 - ν p))

scoped notation3 "g" => selbergTerms

theorem selbergTerms_apply (d : ℕ) :
    g d = ν d * ∏ p in d.primeFactors, 1 / (1 - ν p) := by
  unfold selbergTerms
  by_cases h : d=0
  · rw [h]; simp
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply h]

def mainSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d in divisors P, μPlus d * ν d

def errSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d in divisors P, |μPlus d| * |R d|

end SelbergSieve

section UpperBoundSieve

def UpperMoebius (μ_plus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (if n=1 then 1 else 0) ≤ ∑ d in n.divisors, μ_plus d

structure UpperBoundSieve where mk ::
  μPlus : ℕ → ℝ
  hμPlus : UpperMoebius μPlus

instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

end UpperBoundSieve

section SieveLemmas

variable [s : SelbergSieve]

theorem prodPrimes_ne_zero : P ≠ 0 :=
  Squarefree.ne_zero prodPrimes_squarefree

theorem squarefree_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd prodPrimes_squarefree

theorem squarefree_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : Squarefree d := by
  simp only [Nat.mem_divisors] at hd
  exact Squarefree.squarefree_of_dvd hd.left prodPrimes_squarefree

theorem nu_pos_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : 0 < ν d := by
  calc
    0 < ∏ p in d.primeFactors, ν p := by
      apply prod_pos
      intro p hpd
      have hp_prime : p.Prime := prime_of_mem_primeFactors hpd
      have hp_dvd : p ∣ P := (dvd_of_mem_primeFactors hpd).trans hd
      exact nu_pos_of_prime p hp_prime hp_dvd
    _ = ν d := nu_mult.prod_factors_of_mult ν
                (Squarefree.squarefree_of_dvd hd prodPrimes_squarefree)

theorem nu_ne_zero {d : ℕ} (hd : d ∣ P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  exact nu_pos_of_dvd_prodPrimes hd

theorem nu_ne_zero_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  rw [mem_divisors] at hd
  apply nu_pos_of_dvd_prodPrimes hd.left

theorem multSum_eq_main_err (d : ℕ) : multSum d = ν d * X + R d := by
  dsimp [rem]
  ring

theorem siftedSum_as_delta : siftedSum = ∑ d in support, a d * if Nat.gcd P d = 1 then 1 else 0 :=
  by
  dsimp only [siftedSum]
  simp_rw [mul_ite, mul_one, mul_zero]

theorem nu_lt_self_of_dvd_prodPrimes (d : ℕ) (hdP : d ∣ P) (hd_ne_one : d ≠ 1) : ν d < 1 := by
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP prodPrimes_squarefree
  calc
    ν d = ∏ p in d.primeFactors, ν p :=
      eq_comm.mp (nu_mult.prod_factors_of_mult ν hd_sq)
    _ < ∏ p in d.primeFactors, 1 := by
      apply prod_lt_prod_of_nonempty
      · intro p hp
        simp only [mem_primeFactors] at hp
        apply nu_pos_of_prime p (by aesop) (hp.2.1.trans hdP)
      · intro p hpd; rw [mem_primeFactors_of_ne_zero hd_sq.ne_zero] at hpd
        apply nu_lt_one_of_prime p hpd.left (hpd.2.trans hdP)
      · apply primeDivisors_nonempty _ <| (two_le_iff d).mpr ⟨hd_sq.ne_zero, hd_ne_one⟩
    _ = 1 := by
      simp

section SelbergTerms
/-!


-/

@[aesop safe]
theorem selbergTerms_pos (l : ℕ) (hl : l ∣ P) : 0 < g l := by
  rw [selbergTerms_apply]
  apply mul_pos <| nu_pos_of_dvd_prodPrimes hl
  apply prod_pos
  intro p hp
  rw [one_div_pos]
  have hp_prime : p.Prime := prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ P := (Nat.dvd_of_mem_primeFactors hp).trans hl
  linarith only [nu_lt_one_of_prime p hp_prime hp_dvd]

theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative g := by
  unfold selbergTerms
  arith_mult

theorem one_div_selbergTerms_eq_conv_moebius_nu (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : ν l ≠ 0) : 1 / g l = ∑ ⟨d, e⟩ ∈ l.divisorsAntidiagonal, (μ <| d) * (ν e)⁻¹ :=
  by
  simp only [selbergTerms_apply, one_div, mul_inv, inv_div, inv_inv, Finset.prod_congr,
    Finset.prod_inv_distrib, (nu_mult).prodPrimeFactors_one_sub_of_squarefree _ hl, mul_sum]
  apply symm
  rw [← Nat.sum_divisorsAntidiagonal fun i _ : ℕ => (ν l)⁻¹ * (↑(μ i) * ν i)]
  apply sum_congr rfl; intro ⟨d, e⟩ hd
  simp only [mem_divisorsAntidiagonal, ne_eq] at hd
  obtain ⟨rfl, _⟩ := hd
  have : ν e ≠ 0 := by
    revert hnu_nonzero; contrapose!
    exact multiplicative_zero_of_zero_dvd ν nu_mult hl (Nat.dvd_mul_left e d)
  simp only [squarefree_mul_iff] at hl ⊢
  field_simp
  rw [nu_mult.map_mul_of_coprime hl.1, mul_comm (ν d)]
  ring

theorem nu_eq_conv_one_div_selbergTerms (d : ℕ) (hdP : d ∣ P) :
    (ν d)⁻¹ = ∑ l in divisors P, if l ∣ d then 1 / g l else 0 := by
  apply symm
  rw [←sum_filter, Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).mpr
  intro l _ hlP
  apply symm
  exact one_div_selbergTerms_eq_conv_moebius_nu l
    (Squarefree.squarefree_of_dvd hlP prodPrimes_squarefree)
    (ne_of_gt <| nu_pos_of_dvd_prodPrimes hlP)

theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ P) :
    (∑ l in divisors P, if l ∣ d then g l else 0) = g d * (ν d)⁻¹ := by
  calc
    (∑ l in divisors P, if l ∣ d then g l else 0) =
        ∑ l in divisors P, if l ∣ d then g (d / l) else 0 := by
      rw [← sum_over_dvd_ite prodPrimes_ne_zero hd,
        ← Nat.sum_divisorsAntidiagonal fun x _ => g x, Nat.sum_divisorsAntidiagonal' fun x _ => g x,
        sum_over_dvd_ite prodPrimes_ne_zero hd]
    _ = g d * ∑ l in divisors P, if l ∣ d then 1 / g l else 0 := by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl); intro h
      rw [← div_mult_of_dvd_squarefree g selbergTerms_mult d l h
        (prodPrimes_squarefree.squarefree_of_dvd hd)]
      · ring
      · apply _root_.ne_of_gt; rw [mem_divisors] at hl ; apply selbergTerms_pos; exact hl.left
    _ = g d * (ν d)⁻¹ := by rw [← nu_eq_conv_one_div_selbergTerms d hd]

end SelbergTerms

theorem upper_bound_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum ≤ ∑ d in divisors P, μPlus d * multSum d := by
  have hμ : ∀ n, (if n = 1 then 1 else 0) ≤ ∑ d in n.divisors, μPlus d := μPlus.hμPlus
  calc siftedSum ≤
    ∑ n in support, a n * ∑ d in (Nat.gcd P n).divisors, μPlus d := ?caseA
    _ = ∑ n in support, ∑ d in divisors P, if d ∣ n then a n * μPlus d else 0 := ?caseB
    _ = ∑ d in divisors P, μPlus d * multSum d := ?caseC
  case caseA =>
    rw [siftedSum_as_delta]
    apply Finset.sum_le_sum; intro n _
    exact mul_le_mul_of_nonneg_left (hμ (Nat.gcd P n)) (weights_nonneg n)
  case caseB =>
    apply sum_congr rfl; intro n _;
    rw [mul_sum, sum_over_dvd_ite prodPrimes_ne_zero (Nat.gcd_dvd_left _ _), sum_congr rfl]
    intro d hd
    apply if_congr _ rfl rfl
    rw [Nat.dvd_gcd_iff, and_iff_right (dvd_of_mem_divisors hd)]
  case caseC =>
    rw [sum_comm, sum_congr rfl]; intro d _
    dsimp only [multSum]
    rw [mul_sum, sum_congr rfl]; intro n _
    rw [←ite_zero_mul, mul_comm]

theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum ≤ X * mainSum μPlus + errSum μPlus := by
  calc siftedSum ≤ ∑ d in divisors P, μPlus d * multSum d := by apply upper_bound_of_UpperBoundSieve
   _ ≤ X * ∑ d in divisors P, μPlus d * ν d + ∑ d in divisors P, μPlus d * R d := ?caseA
   _ ≤ _ := ?caseB
  case caseA =>
    apply le_of_eq
    rw [mul_sum, ←sum_add_distrib]
    apply sum_congr rfl; intro d _
    dsimp only [rem]; ring
  case caseB =>
    apply _root_.add_le_add (le_rfl)
    apply sum_le_sum; intro d _
    rw [←abs_mul]
    exact le_abs_self (UpperBoundSieve.μPlus μPlus d * R d)

end SieveLemmas

-- Results about Λ²-Sieves
section LambdaSquared

def lambdaSquared (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 in d.divisors, ∑ d2 in d.divisors, if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {height : ℝ}
  (hw : ∀ (d : ℕ), ¬d ^ 2 ≤ height → w d = 0) {d : ℕ} (hd : ¬↑d ≤ height) (d1 : ℕ) (d2 : ℕ)
  (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2]
  · ring
  by_contra hyp; apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr

theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (height : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ height → w d = 0) (d : ℕ) (hd : ¬d ≤ height) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hheight : 0 ≤ height
  swap
  · push_neg at hd hheight
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [ite_self, eq_self_iff_true, MulZeroClass.mul_zero]
  apply sum_eq_zero; intro d1 _; apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw[mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1 (Nat.lcm_comm d1 d2 ▸ h) hle

theorem upperMoebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    UpperMoebius <| lambdaSquared weights := by
  dsimp [UpperMoebius, lambdaSquared]
  intro n
  have h_sq :
    (∑ d in n.divisors, ∑ d1 in d.divisors, ∑ d2 in d.divisors,
      if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0) =
      (∑ d in n.divisors, weights d) ^ 2 := by
    rw [sq, mul_sum, conv_lambda_sq_larger_sum _ n, sum_comm]
    apply sum_congr rfl; intro d1 hd1
    rw [sum_mul, sum_comm]
    apply sum_congr rfl; intro d2 hd2
    rw [←Aux.sum_intro]
    ring
    rw [mem_divisors, Nat.lcm_dvd_iff]
    exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩
  rw [h_sq]
  split_ifs with hn
  · rw [hn]; simp [hw]
  · apply sq_nonneg

variable [s : SelbergSieve]

theorem lambdaSquared_mainSum_eq_quad_form (w : ℕ → ℝ) :
    mainSum (lambdaSquared w) =
      ∑ d1 in divisors P, ∑ d2 in divisors P,
        ν d1 * w d1 * ν d2 * w d2 * (ν (d1.gcd d2))⁻¹ := by
  calc mainSum (lambdaSquared w)
      = ∑ d ∈ divisors P, ∑ d1 ∈ divisors d, ∑ d2 ∈ divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0 := ?caseA
    _ = ∑ d ∈ divisors P, ∑ d1 in divisors P, ∑ d2 in divisors P,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0 := by apply conv_lambda_sq_larger_sum
    _ = ∑ d1 in divisors P, ∑ d2 in divisors P,
          ν d1 * w d1 * ν d2 * w d2 * (ν (d1.gcd d2))⁻¹ := ?caseB
  case caseA =>
    dsimp only [mainSum, lambdaSquared]
    rw [sum_congr rfl]; intro d _
    rw [sum_mul, sum_congr rfl]; intro d1 _
    rw [sum_mul, sum_congr rfl]; intro d2 _
    rw [ite_zero_mul]
  case caseB =>
    rw [sum_comm, sum_congr rfl]; intro d1 hd1
    rw [sum_comm, sum_congr rfl]; intro d2 hd2
    have h : d1.lcm d2 ∣ P := Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
    rw [←sum_intro (divisors P) (d1.lcm d2) (mem_divisors.mpr ⟨h, prodPrimes_ne_zero⟩ )]
    rw [nu_mult.mult_lcm_eq_of_ne_zero]
    · ring
    refine _root_.ne_of_gt (nu_pos_of_dvd_prodPrimes ?_)
    trans d1
    · exact Nat.gcd_dvd_left d1 d2
    · exact dvd_of_mem_divisors hd1

theorem lambdaSquared_mainSum_eq_diag_quad_form  (w : ℕ → ℝ) :
    mainSum (lambdaSquared w) =
      ∑ l in divisors P,
        1 / g l * (∑ d in divisors P, if l ∣ d then ν d * w d else 0) ^ 2 := by
  calc mainSum (lambdaSquared w) =
    ∑ d1 in divisors P, ∑ d2 in divisors P, (∑ l in divisors P,
          if l ∣ d1.gcd d2 then 1 / g l * (ν d1 * w d1) * (ν d2 * w d2) else 0) := ?caseA
    _ = ∑ l in divisors P, ∑ d1 in divisors P, ∑ d2 in divisors P,
        if l ∣ Nat.gcd d1 d2 then 1 / g l * (ν d1 * w d1) * (ν d2 * w d2) else 0 := ?caseB
    _ = ∑ l in divisors P,
        1 / g l * (∑ d in divisors P, if l ∣ d then ν d * w d else 0) ^ 2 := ?caseC
  case caseA =>
    rw [lambdaSquared_mainSum_eq_quad_form w]
    apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 _
    have hgcd_dvd: d1.gcd d2 ∣ P := (Nat.gcd_dvd_left d1 d2).trans (dvd_of_mem_divisors hd1)
    rw [nu_eq_conv_one_div_selbergTerms _ hgcd_dvd, mul_sum]
    apply sum_congr rfl; intro l _
    rw [mul_ite_zero]; apply if_congr Iff.rfl _ rfl
    ring
  case caseB =>
    apply symm; rw [sum_comm, sum_congr rfl]; intro d1 _; rw[sum_comm];
  case caseC =>
    apply sum_congr rfl; intro l _
    rw [sq, sum_mul, mul_sum, sum_congr rfl]; intro d1 _
    rw [mul_sum, mul_sum, sum_congr rfl]; intro d2 _
    rw [ite_zero_mul_ite_zero, mul_ite_zero]
    apply if_congr (Nat.dvd_gcd_iff) _ rfl;
    ring

end LambdaSquared

end SelbergSieve
