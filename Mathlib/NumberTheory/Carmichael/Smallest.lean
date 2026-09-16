/-
Copyright (c) 2026 Su MingKai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Su MingKai
-/
import Mathlib.NumberTheory.Carmichael.Korselt
import Mathlib.Tactic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factors

/-!
# 561 is the Smallest Carmichael Number

This module formally proves that 561 is the strictly smallest Carmichael number,
directly resolving the open TODO in Mathlib's Carmichael module:
Prove (in a computationally efficient manner) that there are no Carmichael numbers less than 561.

## Mathematical Strategy

Any Carmichael number `n` is odd (`IsCarmichael.odd`), squarefree, and has at least 3 distinct
prime factors. Using Korselt's criterion, every odd candidate `n < 561` is eliminated:
- `n ≤ 2` contradicts `2 < n`.
- Primes are eliminated because Carmichael numbers are composite.
- Numbers divisible by a square `p * p ∣ n` violate squarefreeness.
- Products of two distinct primes `p * q` cannot satisfy Korselt's condition.
- The remaining composite candidates with ≥ 3 prime factors fail Korselt's condition
  `p - 1 ∣ n - 1` for at least one prime factor `p ∣ n`.

## Main Theorems

- `Nat.not_isCarmichael_of_lt_561`: No natural number `n < 561` is a Carmichael number.
- `Nat.isCarmichael_min`: If `n` is a Carmichael number, then `561 ≤ n`.
- `Nat.not_carmichael_of_lt_561`: Corollary for `Nat.Carmichael`.
- `Nat.carmichael_min`: Corollary for `Nat.Carmichael`.
-/

namespace Nat

/-- A Carmichael number is a composite natural number `n > 2` that passes the Fermat primality test
for all bases `b` coprime to `n`. -/
def IsCarmichael (n : ℕ) : Prop :=
  2 < n ∧ ¬ n.Prime ∧ ∀ b : ℕ, b.Coprime n → ProbablePrime n b

/-- IsCarmichael n is equivalent to Nat.Carmichael n. -/
theorem isCarmichael_iff_carmichael {n : ℕ} : n.IsCarmichael ↔ Nat.Carmichael n := by
  constructor
  · rintro ⟨hn, hp, hpp⟩
    exact ⟨hp, by omega, hpp⟩
  · rintro ⟨hp, hn, hpp⟩
    refine ⟨?_, hp, hpp⟩
    by_contra! hle
    have : n = 2 := by omega
    subst this
    exact hp Nat.prime_two

/-- Korselt's criterion for IsCarmichael: `n` is Carmichael iff `2 < n`, composite,
and satisfies Korselt's condition. -/
theorem isCarmichael_iff_korselt (n : ℕ) :
    n.IsCarmichael ↔ 2 < n ∧ ¬ n.Prime ∧ Korselt n := by
  rw [isCarmichael_iff_carmichael, carmichael_iff_korselt]
  constructor
  · rintro ⟨h1, hp, hk⟩
    refine ⟨?_, hp, hk⟩
    by_contra! hle
    have : n = 2 := by omega
    subst this
    exact hp Nat.prime_two
  · rintro ⟨h2, hp, hk⟩
    exact ⟨by omega, hp, hk⟩

/-- Any Carmichael number is odd. -/
theorem IsCarmichael.odd {n : ℕ} (h : n.IsCarmichael) : Odd n := by
  have hk := (isCarmichael_iff_korselt n).mp h
  rcases hk with ⟨h2, hcomp, hsq, hkdiv⟩
  rw [Nat.odd_iff]
  by_contra! heven
  have h2dvd : 2 ∣ n := by omega
  rcases h2dvd with ⟨m, rfl⟩
  have hm1 : 1 < m := by omega
  have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
  have hpm : m.minFac ∣ m := Nat.minFac_dvd m
  have hpn : m.minFac ∣ 2 * m := dvd_mul_of_dvd_right hpm 2
  have hp2 : m.minFac ≠ 2 := by
    intro h_two
    rcases hpm with ⟨k, hk⟩
    have h4 : 2 * 2 ∣ 2 * m := by
      use k
      rw [hk, h_two]
      ring
    have hunit : IsUnit (2 : ℕ) := hsq 2 h4
    have : (2 : ℕ) = 1 := isUnit_iff_eq_one.mp hunit
    revert this
    decide
  have hmod1 : m.minFac % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have h2divp : 2 ∣ m.minFac - 1 := by omega
  have hdiv_n1 : m.minFac - 1 ∣ 2 * m - 1 := hkdiv m.minFac hp hpn
  have h2div_n1 : 2 ∣ 2 * m - 1 := h2divp.trans hdiv_n1
  have h2div1 : 2 ∣ 1 := by
    have h_add : (2 * m - 1) + 1 = 2 * m := by omega
    have h2_dvd_2m : 2 ∣ (2 * m - 1) + 1 := by
      rw [h_add]
      exact dvd_mul_right 2 m
    exact (Nat.dvd_add_right h2div_n1).mp h2_dvd_2m
  revert h2div1
  decide

/-- A product of two distinct primes cannot be a Carmichael number. -/
theorem not_isCarmichael_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ¬ (p * q).IsCarmichael := by
  intro h
  have hk := (isCarmichael_iff_korselt (p * q)).mp h
  have hq_dvd : q ∣ p * q := ⟨p, mul_comm p q⟩
  have hdiv : q - 1 ∣ p * q - 1 := hk.2.2.2 q hq hq_dvd
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hid : p * q - 1 = p * (q - 1) + (p - 1) := by
    have h1 : 1 ≤ p * q := by nlinarith
    have h2 : 1 ≤ q := by omega
    have h3 : 1 ≤ p := by omega
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
    push_cast
    ring
  have h_sum : q - 1 ∣ p * (q - 1) + (p - 1) := hid ▸ hdiv
  have h_left : q - 1 ∣ p * (q - 1) := dvd_mul_left (q - 1) p
  have hdiv_sub : q - 1 ∣ p - 1 := (Nat.dvd_add_right h_left).mp h_sum
  have hpos : 0 < p - 1 := by omega
  have hle : q - 1 ≤ p - 1 := Nat.le_of_dvd hpos hdiv_sub
  omega

/-- If `p * p ∣ n` with `p` non-unit, then `n` is not Carmichael (fails squarefreeness). -/
theorem not_isCarmichael_of_sq_dvd {n p : ℕ} (hpn : p * p ∣ n) (hp : ¬ IsUnit p) :
    ¬ n.IsCarmichael := by
  intro h
  have hk := (isCarmichael_iff_korselt n).mp h
  exact hp (hk.2.2.1 p hpn)

/-- If a prime factor `p ∣ n` does not satisfy `p - 1 ∣ n - 1`, then `n` is not Carmichael. -/
theorem not_isCarmichael_of_prime_factor_not_dvd {n p : ℕ}
    (hp : p.Prime) (hpn : p ∣ n) (hndiv : ¬ (p - 1 ∣ n - 1)) :
    ¬ n.IsCarmichael := by
  intro h
  have hk := (isCarmichael_iff_korselt n).mp h
  exact hndiv (hk.2.2.2 p hp hpn)

/-- Small prime divisors up to $\sqrt{561} < 24$. -/
def testPrimes : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

/-- Fast computable prime decider for natural numbers up to 561. -/
def isPrimeDec (n : ℕ) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else testPrimes.all (fun p => decide (p ≥ n) || decide (n % p ≠ 0))

/-- Auxiliary lemma: any prime between 3 and 23 is in `testPrimes`. -/
theorem prime_le_23_mem_testPrimes {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) (h23 : p ≤ 23) :
    p ∈ testPrimes := by
  interval_cases p <;> first | decide | (revert hp; decide)

/-- Correctness and soundness of `isPrimeDec`: for `n < 561`, evaluates to `true`
iff `n` is prime. -/
theorem isPrimeDec_prime {n : ℕ} (hn : n < 561) (h : isPrimeDec n = true) : Nat.Prime n := by
  unfold isPrimeDec at h
  split_ifs at h with hlt h2 heven
  · subst h2
    exact Nat.prime_two
  · by_contra hnp
    have h2le : 2 ≤ n := by omega
    have hp_prime : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hp_dvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
    have hp_ne2 : Nat.minFac n ≠ 2 := by
      intro hp2
      have : 2 ∣ n := hp2 ▸ hp_dvd
      have : n % 2 = 0 := Nat.mod_eq_zero_of_dvd this
      contradiction
    have hp_ge3 : 3 ≤ Nat.minFac n := by
      have := hp_prime.two_le
      omega
    have hp_lt : Nat.minFac n < n := (Nat.not_prime_iff_minFac_lt h2le).mp hnp
    have hdiv_ge2 : 2 ≤ n / Nat.minFac n := by
      have hmul : n = Nat.minFac n * (n / Nat.minFac n) := (Nat.mul_div_cancel' hp_dvd).symm
      by_contra! hlt
      interval_cases (n / Nat.minFac n)
      · omega
      · omega
    have hq : Nat.minFac n ≤ n / Nat.minFac n :=
      Nat.minFac_le_of_dvd hdiv_ge2 (Nat.div_dvd_of_dvd hp_dvd)
    have h_mul_div : Nat.minFac n * (n / Nat.minFac n) = n := Nat.mul_div_cancel' hp_dvd
    have h_sq : Nat.minFac n * Nat.minFac n ≤ n := by
      have h_le : Nat.minFac n * Nat.minFac n ≤ Nat.minFac n * (n / Nat.minFac n) :=
        Nat.mul_le_mul_left (Nat.minFac n) hq
      rwa [h_mul_div] at h_le
    have hp_le_23 : Nat.minFac n ≤ 23 := by
      by_contra! h24
      have h24_le : 24 ≤ Nat.minFac n := by omega
      have h576 : 24 * 24 ≤ Nat.minFac n * Nat.minFac n := Nat.mul_le_mul h24_le h24_le
      omega
    have hp_mem : Nat.minFac n ∈ testPrimes :=
      prime_le_23_mem_testPrimes hp_prime hp_ge3 hp_le_23
    rw [List.all_eq_true] at h
    have hspec := h (Nat.minFac n) hp_mem
    simp only [Bool.or_eq_true, decide_eq_true_iff] at hspec
    rcases hspec with hge | hne
    · omega
    · rw [Nat.dvd_iff_mod_eq_zero] at hp_dvd
      exact hne hp_dvd

/-- Full equivalence of `isPrimeDec` with `Nat.Prime` for `n < 561`. -/
theorem isPrimeDec_iff {n : ℕ} (hn : n < 561) : isPrimeDec n = true ↔ Nat.Prime n := by
  constructor
  · exact isPrimeDec_prime hn
  · intro hp
    unfold isPrimeDec
    split_ifs with hlt h2 heven
    · have := hp.two_le
      omega
    · rfl
    · have ho := hp.eq_two_or_odd
      rcases ho with rfl | ho
      · omega
      · omega
    · rw [List.all_eq_true]
      intro p hp_mem
      simp only [Bool.or_eq_true, decide_eq_true_iff]
      by_cases hle : p < n
      · right
        intro hmod
        have hdvd : p ∣ n := Nat.dvd_of_mod_eq_zero hmod
        have heq := (Nat.dvd_prime hp).mp hdvd
        rcases heq with rfl | rfl
        · revert hp_mem
          decide
        · omega
      · left
        omega

/-- Sieve of Eratosthenes up to `limit` as a boolean array using `isPrimeDec`. -/
def eratosthenesSieve (limit : ℕ) : Array Bool :=
  Array.ofFn (fun (i : Fin (limit + 1)) => isPrimeDec i.val)

/-- Correctness of `eratosthenesSieve`: index `n` is `true` if and only if `n` is prime. -/
theorem eratosthenesSieve_getElem {limit n : ℕ} (hlim : limit < 561) (hn : n ≤ limit) :
    (eratosthenesSieve limit)[n]'(by simp [eratosthenesSieve]; omega) = true ↔ Nat.Prime n := by
  simp only [eratosthenesSieve, Array.getElem_ofFn]
  exact isPrimeDec_iff (by omega)

/-- Certificate witnessing why a natural number `n` cannot be a Carmichael number. -/
inductive CarmichaelCert where
  | leTwo : CarmichaelCert
  | even : CarmichaelCert
  | prime : CarmichaelCert
  | sqDiv (p : ℕ) : CarmichaelCert
  | korseltFail (p : ℕ) : CarmichaelCert
  | fail : CarmichaelCert
  deriving Repr, DecidableEq

/-- Primes used to detect squared factors for odd numbers below 561. -/
def sqPrimes : List ℕ := testPrimes

/-- Primes used to detect Korselt criterion violations for odd composite numbers below 561. -/
def korseltPrimes : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
   83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
   173, 179, 181]

/-- Finds an odd prime `p` such that `p^2 ∣ n`. -/
def findSqDiv (n : ℕ) : Option ℕ :=
  sqPrimes.find? (fun p => n % (p * p) == 0)

/-- Finds an odd prime `p ∣ n` such that `p - 1 ∤ n - 1`. -/
def findKorseltFail (n : ℕ) : Option ℕ :=
  korseltPrimes.find? (fun p => p < n && (n % p == 0) && ((n - 1) % (p - 1) != 0))

/-- Generates a non-Carmichael certificate for `n`. -/
def certify (n : ℕ) : CarmichaelCert :=
  if n ≤ 2 then .leTwo
  else if n % 2 == 0 then .even
  else match findSqDiv n with
  | some p => .sqDiv p
  | none => match findKorseltFail n with
    | some p => .korseltFail p
    | none => if isPrimeDec n then .prime else .fail

/-- Verifies that a certificate `c` is valid for candidate `n`. -/
def verifyCert (n : ℕ) (c : CarmichaelCert) : Bool :=
  match c with
  | .leTwo => decide (n ≤ 2)
  | .even => decide (n % 2 = 0)
  | .prime => isPrimeDec n
  | .sqDiv p => decide (2 ≤ p) && decide (n % (p * p) = 0)
  | .korseltFail p =>
    decide (2 ≤ p) && isPrimeDec p && decide (n % p = 0) && decide ((n - 1) % (p - 1) ≠ 0)
  | .fail => false

/-- Soundness of certificate verification: any valid certificate implies `n` is not Carmichael. -/
theorem verifyCert_sound {n : ℕ} (hn : n < 561) {c : CarmichaelCert}
    (hc : verifyCert n c = true) : ¬ n.IsCarmichael := by
  intro h
  cases c with
  | leTwo =>
    simp only [verifyCert, decide_eq_true_iff] at hc
    have h2 := h.1
    omega
  | even =>
    simp only [verifyCert, decide_eq_true_iff] at hc
    have ho := h.odd
    rw [Nat.odd_iff] at ho
    omega
  | prime =>
    simp only [verifyCert] at hc
    have hp := (isPrimeDec_iff hn).mp hc
    exact h.2.1 hp
  | sqDiv p =>
    simp only [verifyCert, Bool.and_eq_true, decide_eq_true_iff] at hc
    rcases hc with ⟨hp2, hmod⟩
    have hpn : p * p ∣ n := Nat.dvd_of_mod_eq_zero hmod
    have hpunit : ¬ IsUnit p := by
      intro hu
      have : p = 1 := isUnit_iff_eq_one.mp hu
      omega
    exact not_isCarmichael_of_sq_dvd hpn hpunit h
  | korseltFail p =>
    simp only [verifyCert, Bool.and_eq_true, decide_eq_true_iff] at hc
    rcases hc with ⟨⟨⟨hp2, hp_dec⟩, hmod⟩, hmod_ne⟩
    have h2 := h.1
    have hpn : p ∣ n := Nat.dvd_of_mod_eq_zero hmod
    have hp_pos : 0 < p := by omega
    have hp_le : p ≤ n := Nat.le_of_dvd (by omega) hpn
    have hp_lt : p < 561 := by omega
    have hp_prime : p.Prime := (isPrimeDec_iff hp_lt).mp hp_dec
    have hndiv : ¬ (p - 1 ∣ n - 1) := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact hmod_ne
    exact not_isCarmichael_of_prime_factor_not_dvd hp_prime hpn hndiv h
  | fail =>
    simp only [verifyCert] at hc
    contradiction

/-- Decides whether candidate `n` is certified non-Carmichael. -/
def checkCandidate (n : ℕ) : Bool :=
  verifyCert n (certify n)

/-- Soundness of candidate checking: if `checkCandidate n = true`, then `n` is not Carmichael. -/
theorem not_isCarmichael_of_checkCandidate {n : ℕ} (hn : n < 561) (h : checkCandidate n = true) :
    ¬ n.IsCarmichael :=
  verifyCert_sound hn h

/-- Computational decision procedure verifying that no number strictly below `N` is Carmichael. -/
def checkCarmichaelBound (N : ℕ) : Bool :=
  if 561 < N then false
  else (List.range N).all checkCandidate

/-- Soundness theorem: if `checkCarmichaelBound N = true`, then no `n < N` is Carmichael. -/
theorem checkCarmichaelBound_sound {N : ℕ} (h : checkCarmichaelBound N = true) :
    ∀ n < N, ¬ n.IsCarmichael := by
  intro n hn
  unfold checkCarmichaelBound at h
  split_ifs at h with hgt
  rw [List.all_eq_true] at h
  have h_lt : n < 561 := by omega
  exact not_isCarmichael_of_checkCandidate h_lt (h n (List.mem_range.mpr hn))

set_option maxRecDepth 200000 in
/-- There are no Carmichael numbers strictly less than 561. -/
theorem not_isCarmichael_of_lt_561 {n : ℕ} (hn : n < 561) : ¬ n.IsCarmichael := by
  have h_dec : checkCarmichaelBound 561 = true := by decide
  exact checkCarmichaelBound_sound h_dec n hn

/-- 561 is the minimal Carmichael number. -/
theorem isCarmichael_min {n : ℕ} (hn : n.IsCarmichael) : 561 ≤ n := by
  by_contra! h
  exact not_isCarmichael_of_lt_561 h hn

/-- There are no Carmichael numbers strictly less than 561 (formulation for Nat.Carmichael). -/
theorem not_carmichael_of_lt_561 {n : ℕ} (h : n < 561) : ¬ Nat.Carmichael n := by
  intro hc
  exact not_isCarmichael_of_lt_561 h (isCarmichael_iff_carmichael.mpr hc)

/-- 561 is the minimal Carmichael number (formulation for Nat.Carmichael). -/
theorem carmichael_min {n : ℕ} (hn : Nat.Carmichael n) : 561 ≤ n :=
  isCarmichael_min (isCarmichael_iff_carmichael.mpr hn)

end Nat

export Nat (IsCarmichael isCarmichael_iff_carmichael isCarmichael_iff_korselt
  not_isCarmichael_mul_primes not_isCarmichael_of_sq_dvd
  not_isCarmichael_of_prime_factor_not_dvd not_isCarmichael_of_lt_561
  isCarmichael_min not_carmichael_of_lt_561 carmichael_min
  eratosthenesSieve checkCarmichaelBound checkCarmichaelBound_sound)

