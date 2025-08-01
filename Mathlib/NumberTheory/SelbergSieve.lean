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
 * `upperMoebius_of_lambda_sq` - Lambda squared weights produce upper bound sieves
 * `lambdaSquared_mainSum_eq_diag_quad_form` - The main sum of a Λ² sieve has a nice diagonalisation

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

namespace BoundingSieve
open SelbergSieve

theorem one_le_y {s : SelbergSieve} : 1 ≤ s.level := s.one_le_level

variable {s : BoundingSieve}

/-! Lemmas about $P$. -/

theorem prodPrimes_ne_zero : s.prodPrimes ≠ 0 :=
  Squarefree.ne_zero s.prodPrimes_squarefree

theorem squarefree_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ s.prodPrimes) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree

theorem squarefree_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors s.prodPrimes) :
    Squarefree d := by
  simp only [Nat.mem_divisors] at hd
  exact Squarefree.squarefree_of_dvd hd.left s.prodPrimes_squarefree

/-! Lemmas about $\nu$. -/

theorem prod_primeFactors_nu {d : ℕ} (hd : d ∣ s.prodPrimes) :
    ∏ p ∈ d.primeFactors, s.nu p = s.nu d := by
  rw [← s.nu_mult.map_prod_of_subset_primeFactors _ _ subset_rfl,
    Nat.prod_primeFactors_of_squarefree <| Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree]

theorem nu_pos_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ s.prodPrimes) : 0 < s.nu d := by
  calc
    0 < ∏ p ∈ d.primeFactors, s.nu p := by
      apply prod_pos
      intro p hpd
      have hp_prime : p.Prime := prime_of_mem_primeFactors hpd
      have hp_dvd : p ∣ s.prodPrimes := (dvd_of_mem_primeFactors hpd).trans hd
      exact s.nu_pos_of_prime p hp_prime hp_dvd
    _ = s.nu d := prod_primeFactors_nu hd

theorem nu_ne_zero {d : ℕ} (hd : d ∣ s.prodPrimes) : s.nu d ≠ 0 := by
  apply _root_.ne_of_gt
  exact nu_pos_of_dvd_prodPrimes hd

theorem nu_lt_one_of_dvd_prodPrimes {d : ℕ} (hdP : d ∣ s.prodPrimes) (hd_ne_one : d ≠ 1) :
    s.nu d < 1 := by
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
  have := hd_sq.ne_zero
  calc
    s.nu d = ∏ p ∈ d.primeFactors, s.nu p := (prod_primeFactors_nu hdP).symm
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

/-- The weight of all the elements that are a multiple of `d`. -/
@[simp]
def multSum (d : ℕ) : ℝ := ∑ n ∈ s.support, if d ∣ n then s.weights n else 0


/-- The remainder term in the approximation A_d = ν (d) X + R_d. This is the degree to which `nu`
  fails to approximate the proportion of the weight that is a multiple of `d`. -/
@[simp]
def rem (d : ℕ) : ℝ := s.multSum d - s.nu d * s.totalMass

/-- The weight of all the elements that are not a multiple of any of our finite set of primes. -/
def siftedSum : ℝ := ∑ d ∈ s.support, if Coprime s.prodPrimes d then s.weights d else 0

/-- `X * mainSum μ⁺` is the main term in the upper bound on `sifted_sum`. -/
def mainSum (muPlus : ℕ → ℝ) : ℝ := ∑ d ∈ divisors s.prodPrimes, muPlus d * s.nu d

/-- `errSum μ⁺` is the error term in the upper bound on `sifted_sum`. -/
def errSum (muPlus : ℕ → ℝ) : ℝ := ∑ d ∈ divisors s.prodPrimes, |muPlus d| * |s.rem d|

theorem multSum_eq_main_err (d : ℕ) : s.multSum d = s.nu d * s.totalMass + s.rem d := by
  dsimp [rem]
  ring

theorem siftedSum_eq_sum_support_mul_ite :
    s.siftedSum = ∑ d ∈ s.support, s.weights d * if Nat.gcd s.prodPrimes d = 1 then 1 else 0 := by
  dsimp only [siftedSum]
  simp_rw [mul_ite, mul_one, mul_zero]

@[deprecated (since := "2025-07-27")]
alias siftedsum_eq_sum_support_mul_ite := siftedSum_eq_sum_support_mul_ite

omit s in
/-- A sequence of coefficients $\mu^{+}$ is upper Moebius if $\mu * \zeta ≤ \mu^{+} * \zeta$. These
  coefficients then yield an upper bound on the sifted sum. -/
def IsUpperMoebius (muPlus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, muPlus d

theorem siftedSum_le_sum_of_upperMoebius (muPlus : ℕ → ℝ) (h : IsUpperMoebius muPlus) :
    s.siftedSum ≤ ∑ d ∈ divisors s.prodPrimes, muPlus d * s.multSum d := by
  have hμ : ∀ n, (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, muPlus d := h
  calc siftedSum ≤
    ∑ n ∈ s.support, s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, muPlus d := ?caseA
    _ = ∑ n ∈ s.support, ∑ d ∈ divisors s.prodPrimes,
        if d ∣ n then s.weights n * muPlus d else 0 := ?caseB
    _ = ∑ d ∈ divisors s.prodPrimes, muPlus d * multSum d := ?caseC
  case caseA =>
    rw [siftedSum_eq_sum_support_mul_ite]
    gcongr with n
    exact hμ (Nat.gcd s.prodPrimes n)
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
    s.siftedSum ≤ s.totalMass * s.mainSum muPlus + s.errSum muPlus := calc
  s.siftedSum ≤ ∑ d ∈ divisors s.prodPrimes, muPlus d * multSum d :=
    siftedSum_le_sum_of_upperMoebius _ h
  _ = s.totalMass * mainSum muPlus + ∑ d ∈ divisors s.prodPrimes, muPlus d * s.rem d := by
    rw [mainSum, mul_sum, ← sum_add_distrib]
    congr with d
    dsimp only [rem]; ring
  _ ≤ s.totalMass * mainSum muPlus + errSum muPlus := by
    rw [errSum]
    gcongr _ + ∑ d ∈ _, ?_ with d
    rw [← abs_mul]
    exact le_abs_self (muPlus d * s.rem d)



section LambdaSquared
/-- We consider a special class of upper bound sieves called the Λ² sieve. This class is
  parameterised by a sequence of real numbers. We will later choose a set of weights that minimises
  the main term, under a constraint that lets us control the error term. -/
def lambdaSquared (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0

private theorem lambdaSquared_eq_zero_of_not_le_height_aux {w : ℕ → ℝ} {height : ℝ}
    (hw : ∀ (d : ℕ), ¬d ^ 2 ≤ height → w d = 0) {d : ℕ} (hd : ¬↑d ≤ height) (d1 : ℕ) (d2 : ℕ)
    (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  by_cases hd1 : d1 = 0
  · simp_all
  by_cases hd2 : d2 = 0
  · simp_all
  rw [hw d2]
  · ring
  by_contra hyp; apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ d1.lcm d2 := by rw [h]
      _ ≤ d1 * d2 := Nat.lcm_le_mul (by omega) (by omega)
      _ ≤ _       := ?_
  · rw [sq]; gcongr

theorem lambdaSquared_eq_zero_of_not_le_height (w : ℕ → ℝ) (height : ℝ)
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
    simp only [ite_self, MulZeroClass.mul_zero]
  apply sum_eq_zero; intro d1 _; apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_not_le_height_aux hw hd d1 d2 h hle
  · rw [mul_comm]
    apply lambdaSquared_eq_zero_of_not_le_height_aux hw hd d2 d1 (Nat.lcm_comm d1 d2 ▸ h) hle

private theorem conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors,
        ∑ d1 ∈ d.divisors,
          ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d ∈ n.divisors,
        ∑ d1 ∈ n.divisors,
          ∑ d2 ∈ n.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0 := by
  apply sum_congr rfl; intro d hd
  rw [mem_divisors] at hd
  simp_rw [←Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ite_sum_zero, ← ite_and]
  congr with d1
  congr with d2
  congr
  simp +contextual [← and_assoc, eq_iff_iff, and_iff_right_iff_imp,
    Nat.dvd_lcm_left, Nat.dvd_lcm_right]

theorem upperMoebius_lambdaSquared (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    IsUpperMoebius <| lambdaSquared weights := by
  dsimp [IsUpperMoebius, lambdaSquared]
  intro n
  have h_sq :
    (∑ d ∈ n.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0) =
      (∑ d ∈ n.divisors, weights d) ^ 2 := by
    rw [sq, mul_sum, conv_lambda_sq_larger_sum _ n, sum_comm]
    apply sum_congr rfl; intro d1 hd1
    rw [sum_mul, sum_comm]
    apply sum_congr rfl; intro d2 hd2
    rw [sum_ite_eq_of_mem']
    ring
    rw [mem_divisors, Nat.lcm_dvd_iff]
    exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩
  rw [h_sq]
  split_ifs with hn
  · rw [hn]; simp [hw]
  · apply sq_nonneg

end LambdaSquared

section SelbergTerms

variable {s : BoundingSieve}

/-- These are the terms that appear in the sum `S` in the main term of the fundamental theorem.

$S = ∑_{l|P, l≤\sqrt{y}} g(l)$ -/
def selbergTerms : ArithmeticFunction ℝ :=
  s.nu.pmul (.prodPrimeFactors fun p =>  1 / (1 - s.nu p))

theorem selbergTerms_apply (d : ℕ) :
    s.selbergTerms d = s.nu d * ∏ p ∈ d.primeFactors, 1 / (1 - s.nu p) := by
  unfold selbergTerms
  by_cases h : d=0
  · rw [h]; simp
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply h]

/-! Now follow some important identities involving `g` -/

theorem selbergTerms_pos (l : ℕ) (hl : l ∣ s.prodPrimes) : 0 < s.selbergTerms l := by
  rw [selbergTerms_apply]
  apply mul_pos <| nu_pos_of_dvd_prodPrimes hl
  apply prod_pos
  intro p hp
  rw [one_div_pos]
  have hp_prime : p.Prime := prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ s.prodPrimes := (Nat.dvd_of_mem_primeFactors hp).trans hl
  linarith only [s.nu_lt_one_of_prime p hp_prime hp_dvd]

theorem selbergTerms_isMultiplicative : ArithmeticFunction.IsMultiplicative s.selbergTerms := by
  unfold selbergTerms
  arith_mult

theorem one_div_selbergTerms_eq_conv_moebius_nu (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : s.nu l ≠ 0) :
    1 / s.selbergTerms l = ∑ ⟨d, e⟩ ∈ l.divisorsAntidiagonal, (μ d) * (s.nu e)⁻¹ :=
  by
  simp only [selbergTerms_apply, one_div, mul_inv, inv_inv,
    Finset.prod_inv_distrib, s.nu_mult.prodPrimeFactors_one_sub_of_squarefree _ hl, mul_sum]
  apply symm
  rw [← Nat.sum_divisorsAntidiagonal fun i _ : ℕ => (s.nu l)⁻¹ * (↑(μ i) * s.nu i)]
  apply sum_congr rfl; intro ⟨d, e⟩ hd
  simp only [mem_divisorsAntidiagonal, ne_eq] at hd
  obtain ⟨rfl, _⟩ := hd
  have : s.nu e ≠ 0 := by
    revert hnu_nonzero; contrapose!
    exact s.nu_mult.eq_zero_of_squarefree_of_dvd_eq_zero hl (Nat.dvd_mul_left e d)
  simp only [squarefree_mul_iff] at hl ⊢
  field_simp
  rw [s.nu_mult.map_mul_of_coprime hl.1, mul_comm (s.nu d)]
  ring

theorem nu_eq_conv_one_div_selbergTerms (d : ℕ) (hdP : d ∣ s.prodPrimes) :
    (s.nu d)⁻¹ = ∑ l ∈ divisors s.prodPrimes, if l ∣ d then 1 / s.selbergTerms l else 0 := by
  apply symm
  rw [←sum_filter, Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).mpr
  intro l _ hlP
  apply symm
  exact one_div_selbergTerms_eq_conv_moebius_nu l
    (Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree)
    (ne_of_gt <| nu_pos_of_dvd_prodPrimes hlP)

theorem conv_selbergTerms_eq_selbergTerms_mul_nu_inv {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (∑ l ∈ divisors s.prodPrimes, if l ∣ d then s.selbergTerms l else 0) =
      s.selbergTerms d * (s.nu d)⁻¹ := by
  calc
    (∑ l ∈ divisors s.prodPrimes, if l ∣ d then s.selbergTerms l else 0) =
        ∑ l ∈ divisors s.prodPrimes, if l ∣ d then s.selbergTerms (d / l) else 0 := by
      simp_rw [← sum_filter, Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hd,
        sum_div_divisors d s.selbergTerms]
    _ = s.selbergTerms d *
          ∑ l ∈ divisors s.prodPrimes, if l ∣ d then 1 / s.selbergTerms l else 0 := by
      simp_rw [← sum_filter, mul_sum]; apply sum_congr rfl; intro l hl
      simp only [mem_filter, mem_divisors, ne_eq] at hl
      rw [selbergTerms_isMultiplicative.map_div_of_coprime hl.2]
      · ring
      · apply coprime_of_squarefree_mul <|
          (Nat.div_mul_cancel hl.2).symm ▸ (squarefree_of_dvd_prodPrimes hd)
      · exact (selbergTerms_pos _ hl.1.1).ne.symm
    _ = s.selbergTerms d * (s.nu d)⁻¹ := by rw [← nu_eq_conv_one_div_selbergTerms d hd]

end SelbergTerms

section QuadForm

/-! The main sum we get from Λ² coefficients is a quadratic form. We will later choose weights that
  minimise this form. -/
theorem lambdaSquared_mainSum_eq_quad_form (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w) =
      ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes,
        s.nu d1 * w d1 * s.nu d2 * w d2 * (s.nu (d1.gcd d2))⁻¹ := by
  calc mainSum (lambdaSquared w)
      = ∑ d ∈ divisors s.prodPrimes, ∑ d1 ∈ divisors d, ∑ d2 ∈ divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * s.nu d else 0 := ?caseA
    _ = ∑ d ∈ divisors s.prodPrimes, ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes,
          if d = d1.lcm d2 then w d1 * w d2 * s.nu d else 0 := by apply conv_lambda_sq_larger_sum
    _ = ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes,
          s.nu d1 * w d1 * s.nu d2 * w d2 * (s.nu (d1.gcd d2))⁻¹ := ?caseB
  case caseA =>
    dsimp only [mainSum, lambdaSquared]
    rw [sum_congr rfl]; intro d _
    rw [sum_mul, sum_congr rfl]; intro d1 _
    rw [sum_mul, sum_congr rfl]; intro d2 _
    rw [ite_zero_mul]
  case caseB =>
    rw [sum_comm, sum_congr rfl]; intro d1 hd1
    rw [sum_comm, sum_congr rfl]; intro d2 hd2
    have h : d1.lcm d2 ∣ s.prodPrimes :=
      Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
    rw [sum_ite_eq_of_mem' (divisors s.prodPrimes) (d1.lcm d2) _
      (mem_divisors.mpr ⟨h, prodPrimes_ne_zero⟩), s.nu_mult.map_lcm]
    · ring
    refine _root_.ne_of_gt (nu_pos_of_dvd_prodPrimes ?_)
    trans d1
    · exact Nat.gcd_dvd_left d1 d2
    · exact dvd_of_mem_divisors hd1

/-! The previous quadratic form can be diagonalised with eigenvalues given by `1/g` -/
theorem lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w) =
      ∑ l ∈ divisors s.prodPrimes, 1 / s.selbergTerms l *
        (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * w d else 0) ^ 2 := by
  calc mainSum (lambdaSquared w) =
    ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes, (∑ l ∈ divisors s.prodPrimes,
      if l ∣ d1.gcd d2 then 1 / s.selbergTerms l * (s.nu d1 * w d1) * (s.nu d2 * w d2) else 0)
        := ?caseA
    _ = ∑ l ∈ divisors s.prodPrimes, ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes,
      if l ∣ Nat.gcd d1 d2 then 1 / s.selbergTerms l * (s.nu d1 * w d1) * (s.nu d2 * w d2) else 0
        := ?caseB
    _ = ∑ l ∈ divisors s.prodPrimes,
      1 / s.selbergTerms l * (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * w d else 0) ^ 2
        := ?caseC
  case caseA =>
    rw [lambdaSquared_mainSum_eq_quad_form w]
    apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 _
    have hgcd_dvd : d1.gcd d2 ∣ s.prodPrimes :=
      (Nat.gcd_dvd_left d1 d2).trans (dvd_of_mem_divisors hd1)
    simp_rw [nu_eq_conv_one_div_selbergTerms _ hgcd_dvd, ← sum_filter, mul_sum]
    congr with l
    ring
  case caseB =>
    apply symm; rw [sum_comm, sum_congr rfl]; intro d1 _; rw [sum_comm];
  case caseC =>
    congr with l
    simp_rw [← sum_filter, sq, sum_mul, mul_sum, sum_filter, ite_sum_zero, ← ite_and, dvd_gcd_iff]
    congr with d1
    congr with d2
    congr 1
    ring

end QuadForm

end BoundingSieve
