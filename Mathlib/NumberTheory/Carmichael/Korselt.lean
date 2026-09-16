/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
import Mathlib.NumberTheory.FermatPsp
import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factors
import Mathlib.GroupTheory.Exponent
import Mathlib.Tactic.NormNum.Prime

set_option exponentiation.threshold 1000

/-!
# Carmichael Numbers and Korselt's Criterion

This module formalizes Carmichael numbers (absolute Fermat pseudoprimes) and machine-checks
Korselt's Criterion (1899) in Lean 4 with Mathlib4.

A Carmichael number is a composite natural number `n > 1` that passes the Fermat primality test
for all bases `b` coprime to `n`, i.e., `ProbablePrime n b` holds for all `b` with `b.Coprime n`.

Korselt's Criterion (1899) characterizes Carmichael numbers as composite numbers `n > 1`
that are squarefree and satisfy `(p - 1) ∣ (n - 1)` for every prime divisor `p ∣ n`.

## Main Definitions and Theorems

- `Nat.Carmichael`: Definition of Carmichael numbers.
- `carmichael_561`: Proof that 561 is a Carmichael number.
- `not_carmichael_nine`: Proof that 9 is not a Carmichael number.
- `Nat.Korselt`: First-class predicate for Korselt's criterion.
- `Nat.carmichael_iff_carmichael_dvd`: Tripartite equivalence step 1.
- `Nat.carmichael_dvd_iff_korselt`: Tripartite equivalence step 2.
- `Nat.carmichael_iff_korselt`: Side-condition-free Korselt's criterion.
- `Nat.korseltDec`: Computable decider for Korselt's condition.

## References

* A. Korselt, *Problème chinois*, L'Intermédiaire des Mathématiciens 6 (1899), 142–143.

## Acknowledgments

Special thanks to Felix Pernegger for suggesting the characterization via the
Carmichael function (`ArithmeticFunction.carmichael`) and discussions on proof simplification.
-/

/-- Prime factorization of 561: 561 = 3 * 11 * 17. -/
lemma factor_561 : 561 = 3 * 11 * 17 := by rfl

/-- 561 is composite (not prime). -/
lemma not_prime_561 : ¬ (561 : ℕ).Prime := by norm_num

/-- Divisibility lemma for prime factor 3: for any base  coprime to 561, 3 ∣ b ^ 560 - 1. -/
lemma dvd_mod_three {b : ℕ} (h : b.Coprime 561) : 3 ∣ b ^ 560 - 1 := by
  have h_pow := (Nat.ModEq.pow_totient (h.coprime_dvd_right (by decide : 3 ∣ 561))).pow 280
  rw [← Nat.pow_mul, one_pow] at h_pow
  exact h_pow.symm.dvd'

/-- Divisibility lemma for prime factor 11: for any base  coprime to 561, 11 ∣ b ^ 560 - 1. -/
lemma dvd_mod_eleven {b : ℕ} (h : b.Coprime 561) : 11 ∣ b ^ 560 - 1 := by
  have h_pow := (Nat.ModEq.pow_totient (h.coprime_dvd_right (by decide : 11 ∣ 561))).pow 56
  rw [← Nat.pow_mul, one_pow] at h_pow
  exact h_pow.symm.dvd'

/-- Divisibility lemma for prime factor 17: for any base  coprime to 561, 17 ∣ b ^ 560 - 1. -/
lemma dvd_mod_seventeen {b : ℕ} (h : b.Coprime 561) : 17 ∣ b ^ 560 - 1 := by
  have h_pow := (Nat.ModEq.pow_totient (h.coprime_dvd_right (by decide : 17 ∣ 561))).pow 35
  rw [← Nat.pow_mul, one_pow] at h_pow
  exact h_pow.symm.dvd'

/-- Divisibility combination lemma: if 3, 11, and 17 each divide  ^ 560 - 1,
then their product 561 divides  ^ 560 - 1. -/
lemma dvd_561_of_prime_factors {b : ℕ}
    (h3 : 3 ∣ b ^ 560 - 1) (h11 : 11 ∣ b ^ 560 - 1) (h17 : 17 ∣ b ^ 560 - 1) :
    561 ∣ b ^ 560 - 1 :=
  (by decide : Nat.Coprime (3 * 11) 17).mul_dvd_of_dvd_of_dvd
    ((by decide : Nat.Coprime 3 11).mul_dvd_of_dvd_of_dvd h3 h11) h17

open ArithmeticFunction

namespace Nat

/-- A natural number 
 is a Carmichael number if it is composite, greater than 1,
and passes the Fermat primality test for all bases  coprime to 
. -/
def Carmichael (n : ℕ) : Prop :=
  ¬ n.Prime ∧ 1 < n ∧ ∀ b : ℕ, b.Coprime n → ProbablePrime n b

/-- A Carmichael number is composite (not prime). -/
lemma Carmichael.not_prime {n : ℕ} (h : Carmichael n) : ¬ n.Prime :=
  h.1

/-- A Carmichael number is strictly greater than 1. -/
lemma Carmichael.one_lt {n : ℕ} (h : Carmichael n) : 1 < n :=
  h.2.1

/-- A Carmichael number is a Fermat probable prime to any coprime base. -/
lemma Carmichael.probablePrime {n : ℕ} (h : Carmichael n) {b : ℕ} (hb : b.Coprime n) :
    ProbablePrime n b :=
  h.2.2 b hb

/-- Positive witness: 561 is a Carmichael number. -/
theorem carmichael_561 : Carmichael 561 :=
  ⟨not_prime_561, by decide, fun b h ↦
    dvd_561_of_prime_factors (dvd_mod_three h) (dvd_mod_eleven h) (dvd_mod_seventeen h)⟩

/-- Negative sanity check: 9 is not a Carmichael number because it fails the Fermat primality test
for base 2 (gcd(2, 9) = 1 but 9 ∤ 2^8 - 1). -/
theorem not_carmichael_nine : ¬ Carmichael 9 := fun h ↦
  (by decide : ¬ (9 ∣ 2 ^ (9 - 1) - 1)) (h.probablePrime (by decide : Nat.Coprime 2 9))

/-- **Korselt Condition (1899)**: A natural number 
 satisfies Korselt's condition if
it is square-free and p - 1 ∣ n - 1 for every prime divisor p ∣ n. -/
def Korselt (n : ℕ) : Prop :=
  Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)

/-- **Step 1**: A composite natural number 
 > 1 is a Carmichael number if and only if
the Carmichael function carmichael n divides 
 - 1. -/
theorem carmichael_iff_carmichael_dvd (n : ℕ) (hn : 1 < n) (hcomp : ¬ n.Prime) :
    Nat.Carmichael n ↔ ArithmeticFunction.carmichael n ∣ n - 1 := by
  have hn0 : n ≠ 0 := by lia
  have : NeZero n := ⟨hn0⟩
  have h_exp : ArithmeticFunction.carmichael n = Monoid.exponent (ZMod n)ˣ :=
    carmichael_eq_exponent hn0
  rw [h_exp, Monoid.exponent_dvd_iff_forall_pow_eq_one]
  constructor
  · intro hc g
    have hcop := ZMod.val_coe_unit_coprime g
    have hpp := hc.probablePrime hcop
    dsimp [ProbablePrime] at hpp
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    rw [← ZMod.natCast_zmod_val (g : ZMod n)]
    rw [← Nat.cast_pow]
    have hb_pos : 1 ≤ (g : ZMod n).val := by
      by_contra! h0
      have hz : (g : ZMod n).val = 0 := by lia
      rw [hz, Nat.Coprime, Nat.gcd_zero_left] at hcop
      subst hcop
      lia
    have hpow_ge : 1 ≤ (g : ZMod n).val ^ (n - 1) :=
      Nat.one_le_pow (n - 1) _ hb_pos
    have hmodeq : 1 ≡ (g : ZMod n).val ^ (n - 1) [MOD n] :=
      Nat.modEq_of_dvd' hpow_ge hpp
    rw [← Nat.cast_one (R := ZMod n)]
    exact ((ZMod.natCast_eq_natCast_iff 1 ((g : ZMod n).val ^ (n - 1)) n).mpr hmodeq).symm
  · intro hg
    refine ⟨hcomp, hn, fun b hb ↦ ?_⟩
    dsimp [ProbablePrime]
    let u : (ZMod n)ˣ := ZMod.unitOfCoprime b hb
    have hu := hg u
    have hu_val : ((u ^ (n - 1) : (ZMod n)ˣ) : ZMod n) = (1 : ZMod n) := by
      rw [hu, Units.val_one]
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime b hb, ← Nat.cast_pow,
      ← Nat.cast_one (R := ZMod n)] at hu_val
    have hmodeq : (b ^ (n - 1) : ℕ) ≡ 1 [MOD n] :=
      (ZMod.natCast_eq_natCast_iff (b ^ (n - 1)) 1 n).mp hu_val
    exact hmodeq.symm.dvd'

/-- The Carmichael function of a prime p is p - 1. -/
lemma carmichael_prime {p : ℕ} (hp : p.Prime) : ArithmeticFunction.carmichael p = p - 1 := by
  by_cases hp2 : p = 2
  · subst hp2
    have h2 : (2 : ℕ) = 2 ^ 1 := by rfl
    rw [h2, carmichael_two_pow_of_le_two (by decide)]
    rfl
  · have hp1 : (p : ℕ) = p ^ 1 := by rw [pow_one]
    rw [hp1, carmichael_pow_of_prime_ne_two 1 hp hp2, pow_one, Nat.totient_prime hp]

/-- For any prime p and power k ≥ 1, p - 1 divides carmichael (p ^ k). -/
lemma prime_sub_one_dvd_carmichael_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    p - 1 ∣ ArithmeticFunction.carmichael (p ^ k) := by
  by_cases hp2 : p = 2
  · subst hp2
    have : 2 - 1 = 1 := rfl
    rw [this]
    exact one_dvd _
  · rw [carmichael_pow_of_prime_ne_two k hp hp2, totient_prime_pow hp hk]
    exact ⟨p ^ (k - 1), mul_comm _ _⟩

/-- For any prime p and power k ≥ 2, p divides carmichael (p ^ k). -/
lemma prime_dvd_carmichael_pow_of_two_le {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 2 ≤ k) :
    p ∣ ArithmeticFunction.carmichael (p ^ k) := by
  by_cases hp2 : p = 2
  · subst hp2
    by_cases hk2 : k = 2
    · subst hk2
      rw [carmichael_two_pow_of_le_two (by decide)]
      exact dvd_rfl
    · rw [carmichael_two_pow_of_ne_two hk2]
      exact dvd_pow_self 2 (by lia)
  · rw [carmichael_pow_of_prime_ne_two k hp hp2, totient_prime_pow hp (by lia)]
    have hdvd : p ∣ p ^ (k - 1) := dvd_pow_self p (by lia)
    exact dvd_mul_of_dvd_left hdvd (p - 1)

/-- If p ∣ n and p ∣ n - 1 with 1 ≤ n, then p ∣ 1. -/
lemma dvd_one_of_dvd_and_dvd_sub_one {p n : ℕ} (hpn : p ∣ n) (hpn1 : p ∣ n - 1) (hn : 1 ≤ n) :
    p ∣ 1 := by
  have h_add : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  have hp_add : p ∣ (n - 1) + 1 := h_add.symm ▸ hpn
  exact (Nat.dvd_add_right hpn1).mp hp_add

/-- **Step 2**: The Carmichael function divides 
 - 1 if and only if 
 satisfies
Korselt's condition. -/
theorem carmichael_dvd_iff_korselt (n : ℕ) (hn : 1 < n) :
    ArithmeticFunction.carmichael n ∣ n - 1 ↔ Korselt n := by
  have hn0 : n ≠ 0 := by lia
  have : NeZero n := ⟨hn0⟩
  rw [carmichael_factorization n]
  dsimp [Korselt]
  constructor
  · intro h_div
    have h_korselt : ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1) := by
      intro p hp hpn
      have hp_mem : p ∈ n.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hp, hpn, hn0⟩
      have hdvd_lcm : carmichael (p ^ n.factorization p) ∣
          n.primeFactors.lcm fun q ↦ carmichael (q ^ n.factorization q) :=
        Finset.dvd_lcm hp_mem
      have hdvd_total : carmichael (p ^ n.factorization p) ∣ n - 1 :=
        hdvd_lcm.trans h_div
      have h1le : 1 ≤ n.factorization p :=
        (hp.dvd_iff_one_le_factorization hn0).mp hpn
      have hp_sub : p - 1 ∣ carmichael (p ^ n.factorization p) :=
        prime_sub_one_dvd_carmichael_pow hp h1le
      exact hp_sub.trans hdvd_total
    refine ⟨?_, h_korselt⟩
    rw [squarefree_iff_factorization_le_one hn0]
    intro p
    by_cases hp : p.Prime
    · by_contra! h2le
      have hpn : p ∣ n := by
        rw [hp.dvd_iff_one_le_factorization hn0]
        lia
      have hp_mem : p ∈ n.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hp, hpn, hn0⟩
      have hdvd_lcm : carmichael (p ^ n.factorization p) ∣
          n.primeFactors.lcm fun q ↦ carmichael (q ^ n.factorization q) :=
        Finset.dvd_lcm hp_mem
      have hdvd_total : carmichael (p ^ n.factorization p) ∣ n - 1 :=
        hdvd_lcm.trans h_div
      have hp_dvd : p ∣ carmichael (p ^ n.factorization p) :=
        prime_dvd_carmichael_pow_of_two_le hp h2le
      have hp_dvd_n1 : p ∣ n - 1 := hp_dvd.trans hdvd_total
      have hp_dvd_one : p ∣ 1 := dvd_one_of_dvd_and_dvd_sub_one hpn hp_dvd_n1 (by lia)
      exact hp.not_dvd_one hp_dvd_one
    · rw [factorization_eq_zero_of_not_prime _ hp]
      exact zero_le_one
  · rintro ⟨h_sq, h_korselt⟩
    rw [Finset.lcm_dvd_iff]
    intro p hp_mem
    rw [Nat.mem_primeFactors] at hp_mem
    rcases hp_mem with ⟨hp, hpn, -⟩
    have h_fac : n.factorization p = 1 :=
      factorization_eq_one_of_squarefree h_sq hp hpn
    rw [h_fac, pow_one, carmichael_prime hp]
    exact h_korselt p hp hpn

/-- **Korselt's Criterion (1899)**: A natural number 
 is a Carmichael number
if and only if 1 < n, 
 is composite, and 
 satisfies Korselt's condition. -/
theorem carmichael_iff_korselt (n : ℕ) :
    Nat.Carmichael n ↔ 1 < n ∧ ¬ n.Prime ∧ Korselt n := by
  constructor
  · intro hc
    have h1 := hc.one_lt
    have hp := hc.not_prime
    refine ⟨h1, hp, ?_⟩
    have hdvd := (carmichael_iff_carmichael_dvd n h1 hp).mp hc
    exact (carmichael_dvd_iff_korselt n h1).mp hdvd
  · rintro ⟨h1, hp, hk⟩
    have hdvd := (carmichael_dvd_iff_korselt n h1).mpr hk
    exact (carmichael_iff_carmichael_dvd n h1 hp).mpr hdvd

/-- Computable decider evaluating whether 
 satisfies Korselt's condition. -/
def korseltDec (n : ℕ) : Bool :=
  if n = 0 then false
  else
    let facs := n.primeFactorsList
    decide facs.Nodup && facs.all (fun p => decide ((p - 1) ∣ (n - 1)))

theorem korseltDec_iff (n : ℕ) : korseltDec n = true ↔ Korselt n := by
  unfold korseltDec
  split_ifs with hn0
  · subst hn0
    dsimp [Korselt]
    simp only [not_squarefree_zero, false_and]
  · simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true]
    dsimp [Korselt]
    rw [Nat.squarefree_iff_nodup_primeFactorsList hn0]
    constructor
    · rintro ⟨hnodup, hall⟩
      refine ⟨hnodup, fun p hp hpn => ?_⟩
      have hmem : p ∈ n.primeFactorsList := (Nat.mem_primeFactorsList hn0).mpr ⟨hp, hpn⟩
      exact hall p hmem
    · rintro ⟨hnodup, hk⟩
      refine ⟨hnodup, fun p hp_mem => ?_⟩
      rw [Nat.mem_primeFactorsList hn0] at hp_mem
      exact hk p hp_mem.1 hp_mem.2

instance (n : ℕ) : Decidable (Korselt n) :=
  decidable_of_iff (korseltDec n = true) (korseltDec_iff n)

end Nat

export Nat (Carmichael carmichael_561 not_carmichael_nine Korselt
  carmichael_iff_carmichael_dvd carmichael_dvd_iff_korselt carmichael_iff_korselt
  korseltDec korseltDec_iff)
