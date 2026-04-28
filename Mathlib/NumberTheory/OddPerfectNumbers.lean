/-
Copyright (c) 2026 umpolungfish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: umpolungfish
-/
import Mathlib.Tactic.Common
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.Multiplicity
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Multiplicity

/-!
# Odd Perfect Numbers: 2-adic and 3-adic Structure

This file establishes elementary necessary conditions on odd perfect numbers (OPNs),
culminating in a machine-verified proof of **Touchard's congruence (1953)**:
any odd perfect number `n` satisfies `n ≡ 1 (mod 12)` or `n ≡ 9 (mod 36)`.

## Main results

- `Nat.ArithmeticFunction.OddPerfect.sigma_mul_of_coprime`: σ is multiplicative.
- `Nat.ArithmeticFunction.OddPerfect.opn_product_constraint`: the fundamental equation
  `σ(pᵏ) · σ(m²) = 2·pᵏ·m²` following from Euler's decomposition.
- `Nat.ArithmeticFunction.OddPerfect.sigma_prime_pow_ratio`: `σ(pᵏ)·(p−1) + 1 = p^(k+1)`.
- `Nat.ArithmeticFunction.OddPerfect.opn_mod4`: any OPN is congruent to 1 mod 4.
- `Nat.ArithmeticFunction.OddPerfect.touchard_congruence`: Touchard's congruence (1953).

## Notation and conventions

- `sigma 1 n` denotes the sum-of-divisors function σ(n) = Σ_{d ∣ n} d.
- `Perfect n` means `sigma 1 n = 2 * n`.
- An *odd perfect number* (OPN) in Euler form is `n = p^k * m²` with `p` prime,
  `p ≡ k ≡ 1 (mod 4)`, and `Nat.Coprime (p^k) (m^2)`.
- The hypothesis `euler_form` in `touchard_congruence` records Euler's 1747 theorem
  (proved in mathematics; currently a `sorry` until Mathlib adds it — see below).

## Euler's form (MathlibGap note)

Euler (1747) proved that every OPN has the form `n = p^k * m²` with `p` prime,
`p ≡ k ≡ 1 (mod 4)`, `gcd(p, m) = 1`. This theorem is not yet formalized in Mathlib.
`touchard_congruence` takes the Euler decomposition as an explicit hypothesis; once
Euler's theorem is added to Mathlib, the conditional proof becomes unconditional.

## Acknowledgment

Formalized with LLM assistance (Claude, xAI Grok).

## References

- Touchard, J. (1953). *On prime numbers and perfect numbers*. Scripta Math. 19, 35–39.
- Euler, L. (1747). *De numeris perfectis*. Opera Omnia I.2, 86–162.
- Ochem, P. and Rao, M. (2012). *Odd perfect numbers are greater than 10^1500*.
  Math. Comp. 81, 1869–1877.
-/

open Nat ArithmeticFunction

namespace Nat.ArithmeticFunction.OddPerfect

/-!
### Perfect number predicate
-/

/-- `n` is perfect if the sum of all its divisors equals `2 * n`. -/
def Perfect (n : ℕ) : Prop := sigma 1 n = 2 * n

/-!
### Auxiliary lemmas — 2-adic arithmetic
-/

private lemma pow_odd_of_odd {q : ℕ} (hq : q % 2 = 1) (i : ℕ) : q ^ i % 2 = 1 := by
  induction i with
  | zero => simp
  | succ n ih => simp [pow_succ, Nat.mul_mod, hq, ih]

private lemma pow_mod4_of_mod4 {p : ℕ} (hp : p % 4 = 1) (i : ℕ) : p ^ i % 4 = 1 := by
  induction i with
  | zero => simp
  | succ n ih => simp [pow_succ, Nat.mul_mod, hp, ih]

private lemma geom_sum_mod2 (q n : ℕ) (hq : q % 2 = 1) :
    (∑ i ∈ Finset.range n, q ^ i) % 2 = n % 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, pow_odd_of_odd hq k, ih]
    omega

private lemma geom_sum_odd_mod2 (q e : ℕ) (hq : q % 2 = 1) :
    (∑ i ∈ Finset.range (2 * e + 1), q ^ i) % 2 = 1 := by
  have h := geom_sum_mod2 q (2 * e + 1) hq; omega

private lemma geom_sum_mod4 (p n : ℕ) (hp : p % 4 = 1) :
    (∑ i ∈ Finset.range n, p ^ i) % 4 = n % 4 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, pow_mod4_of_mod4 hp k, ih]
    omega

private lemma geom_sum_mod4_eq2 (p n : ℕ) (hp : p % 4 = 1) (hn : n % 4 = 2) :
    (∑ i ∈ Finset.range n, p ^ i) % 4 = 2 := by
  have h := geom_sum_mod4 p n hp; omega

private noncomputable def v₂ (n : ℕ) : ℕ := (n.factorization) 2

private lemma v2_eq_one_of_mod4_eq2 {n : ℕ} (hn : n % 4 = 2) : v₂ n = 1 := by
  have hpos : n ≠ 0 := by omega
  have h2prime : Nat.Prime 2 := by decide
  have h2dvd : 2 ^ 1 ∣ n := ⟨n / 2, by omega⟩
  have h4notdvd : ¬ (2 ^ 2 ∣ n) := by norm_num; intro ⟨k, hk⟩; omega
  simp only [v₂]
  apply Nat.le_antisymm
  · by_contra hlt
    push Not at hlt
    exact h4notdvd ((h2prime.pow_dvd_iff_le_factorization hpos (k := 2)).mpr (by omega))
  · exact (h2prime.pow_dvd_iff_le_factorization hpos (k := 1)).mp h2dvd

/-!
### σ multiplicativity and the product equation
-/

/-- The sum-of-divisors function is multiplicative: `σ(ab) = σ(a) · σ(b)` for coprime `a`, `b`. -/
lemma sigma_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    sigma 1 (a * b) = sigma 1 a * sigma 1 b :=
  isMultiplicative_sigma.map_mul_of_coprime h

/-- The fundamental OPN product equation.
If `n = p^k * m²` is a perfect number with `Nat.Coprime (p^k) (m^2)`, then
`σ(p^k) · σ(m²) = 2 · p^k · m²`. -/
theorem opn_product_constraint {p k m : ℕ}
    (hperf : Perfect (p ^ k * m ^ 2))
    (hcop : Nat.Coprime (p ^ k) (m ^ 2)) :
    sigma 1 (p ^ k) * sigma 1 (m ^ 2) = 2 * (p ^ k * m ^ 2) := by
  rw [← sigma_mul_of_coprime hcop]
  exact hperf

/-- The sigma prime-power ratio identity: `σ(p^k) · (p - 1) + 1 = p^(k+1)`.
This is the geometric series identity, showing that `σ(p^k) / p^k < p / (p-1)` strictly. -/
lemma sigma_prime_pow_ratio (p k : ℕ) (hp : Nat.Prime p) :
    sigma 1 (p ^ k) * (p - 1) + 1 = p ^ (k + 1) := by
  have h_sum : sigma 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
    rw [sigma_apply, Nat.divisors_prime_pow hp, Finset.sum_map]; simp
  rw [h_sum]
  zify [hp.one_le, Nat.one_le_pow (k + 1) p hp.pos]
  linarith [geom_sum_mul (p : ℤ) (k + 1)]

/-- Strict version: `σ(p^k) · (p - 1) < p^(k+1)`. -/
lemma sigma_prime_pow_lt (p k : ℕ) (hp : Nat.Prime p) :
    sigma 1 (p ^ k) * (p - 1) < p ^ (k + 1) := by
  have h := sigma_prime_pow_ratio p k hp; omega

/-!
### Modular arithmetic results for OPNs
-/

/-- Any OPN in Euler form is congruent to 1 modulo 4.
If `p ≡ 1 (mod 4)` and `n = p^k * m²` is odd, then `n ≡ 1 (mod 4)`. -/
lemma opn_mod4 (p k m : ℕ) (h_odd : ¬ 2 ∣ p ^ k * m ^ 2) (hp_mod : p % 4 = 1) :
    (p ^ k * m ^ 2) % 4 = 1 := by
  have hm_odd : m % 2 = 1 := by
    by_contra hm
    push Not at hm
    have : 2 ∣ m := by omega
    exact h_odd (Dvd.dvd.mul_left (Dvd.dvd.pow this (by norm_num)) (p ^ k))
  have hpk_mod : p ^ k % 4 = 1 := pow_mod4_of_mod4 hp_mod k
  have hm2_mod : m ^ 2 % 4 = 1 := by
    have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
    rcases hm4 with h | h <;> simp [pow_succ, pow_zero, Nat.mul_mod, h]
  calc (p ^ k * m ^ 2) % 4
      = (p ^ k % 4 * (m ^ 2 % 4)) % 4 := by rw [Nat.mul_mod]
    _ = (1 * 1) % 4 := by rw [hpk_mod, hm2_mod]
    _ = 1 := by norm_num

/-!
### 2-adic valuation constraints
-/

/-- For an odd prime `p ≡ 1 (mod 4)` and `k ≡ 1 (mod 4)`, `v₂(σ(p^k)) = 1`.
Core of the 2-adic constraint: the Euler factor carries exactly one unit of 2-adic charge. -/
lemma v2_sigma_prime_power (p k : ℕ) (hp : Nat.Prime p) (_hp_odd : ¬ 2 ∣ p)
    (hp_mod : p % 4 = 1) (hk_mod : k % 4 = 1) :
    v₂ (sigma 1 (p ^ k)) = 1 := by
  have h_sum : sigma 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
    rw [sigma_apply, Nat.divisors_prime_pow hp, Finset.sum_map]; simp
  have h_sum_mod4 : (∑ i ∈ Finset.range (k + 1), p ^ i) % 4 = 2 :=
    geom_sum_mod4_eq2 p (k + 1) hp_mod (by omega)
  rw [h_sum]
  exact v2_eq_one_of_mod4_eq2 h_sum_mod4

/-- For an odd prime `q` and even exponent `2e`, `v₂(σ(q^(2e))) = 0`.
The square factor `m²` contributes zero to the 2-adic budget. -/
lemma v2_sigma_square_factor (q e : ℕ) (hq : Nat.Prime q) (hq_odd : ¬ 2 ∣ q) :
    v₂ (sigma 1 (q ^ (2 * e))) = 0 := by
  have hq_mod : q % 2 = 1 := by
    have : q % 2 ≠ 0 := fun h => hq_odd ⟨q / 2, by omega⟩
    omega
  have h_sum : sigma 1 (q ^ (2 * e)) = ∑ i ∈ Finset.range (2 * e + 1), q ^ i := by
    rw [sigma_apply, Nat.divisors_prime_pow hq, Finset.sum_map]; simp
  have h_odd_sum : (∑ i ∈ Finset.range (2 * e + 1), q ^ i) % 2 = 1 :=
    geom_sum_odd_mod2 q e hq_mod
  have h_not_dvd : ¬ 2 ∣ sigma 1 (q ^ (2 * e)) := by
    rw [h_sum, Nat.dvd_iff_mod_eq_zero]; omega
  simp only [v₂, Nat.factorization_eq_zero_iff]
  right; left; exact h_not_dvd

/-!
### 3-adic helpers for Touchard's congruence
-/

private lemma pow_mod3_q2_even {q : ℕ} (hq : q % 3 = 2) (e : ℕ) : q ^ (2 * e) % 3 = 1 := by
  have hq2 : q ^ 2 % 3 = 1 := by
    have : q ^ 2 = q * q := by ring
    rw [this, Nat.mul_mod, hq]
  rw [pow_mul]
  induction e with
  | zero => simp
  | succ n ih => rw [pow_succ, Nat.mul_mod, hq2, ih]

private lemma pow_mod3_q2_odd {q : ℕ} (hq : q % 3 = 2) (e : ℕ) :
    q ^ (2 * e + 1) % 3 = 2 := by
  rw [pow_succ, Nat.mul_mod, pow_mod3_q2_even hq e, hq]

private lemma geom_sum_mod3_q2 (q n : ℕ) (hq : q % 3 = 2) :
    (∑ i ∈ Finset.range n, q ^ i) % 3 = n % 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih]
    have hpow : q ^ k % 3 = if k % 2 = 0 then 1 else 2 := by
      by_cases h : k % 2 = 0
      · rw [if_pos h, show k = 2 * (k / 2) from by omega]
        exact pow_mod3_q2_even hq (k / 2)
      · rw [if_neg h, show k = 2 * (k / 2) + 1 from by omega]
        exact pow_mod3_q2_odd hq (k / 2)
    rw [hpow]; split_ifs with h <;> omega

private lemma pow_mod3_one {p : ℕ} (hp : p % 3 = 1) (k : ℕ) : p ^ k % 3 = 1 := by
  induction k with
  | zero => simp
  | succ n ih => rw [pow_succ, Nat.mul_mod, hp, ih]

private lemma sq_mod3_of_not_dvd {m : ℕ} (hm : ¬ 3 ∣ m) : m ^ 2 % 3 = 1 := by
  have hm3 : m % 3 = 1 ∨ m % 3 = 2 := by
    have : m % 3 ≠ 0 := fun h => hm ⟨m / 3, by omega⟩
    omega
  have : m ^ 2 = m * m := by ring
  rw [this, Nat.mul_mod]
  rcases hm3 with h | h <;> simp [h]

private lemma sigma_dvd3_of_p2_kodd (p k : ℕ) (hp : Nat.Prime p)
    (hp3 : p % 3 = 2) (hk_odd : k % 2 = 1) :
    3 ∣ sigma 1 (p ^ k) := by
  have h_sum : sigma 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
    rw [sigma_apply, Nat.divisors_prime_pow hp, Finset.sum_map]; simp
  rw [Nat.dvd_iff_mod_eq_zero, h_sum, geom_sum_mod3_q2 p (k + 1) hp3]
  omega

/-!
### Touchard's congruence
-/

/-- **Touchard's congruence (1953)**.
Any odd perfect number in Euler form satisfies `n ≡ 1 (mod 12)` or `n ≡ 9 (mod 36)`.

**Hypotheses:**
- `h_odd`: `n` is odd.
- `h_perf`: `n` is perfect, i.e., `σ(n) = 2n`.
- `h_euler`: Euler's decomposition `n = p^k * m²` with `p` prime, `p ≡ k ≡ 1 (mod 4)`,
  and `Nat.Coprime (p^k) (m^2)`.

**Note on `h_euler`:** Euler (1747) proved that every OPN has this form, but the theorem
is not yet formalized in Mathlib. Once added, this conditional proof becomes unconditional.

**Proof outline:**
1. `n ≡ 1 (mod 4)` from `opn_mod4`.
2. Case split on `3 ∣ n`.
   - If `3 ∣ n`: `p ≠ 3` (since `p ≡ 1 (mod 4)`), so `3 ∤ p^k`, thus `3 ∣ m²`, hence `9 ∣ n`.
     Combined with `n ≡ 1 (mod 4)` and `9 ∣ n`, CRT gives `n ≡ 9 (mod 36)`.
   - If `3 ∤ n`: `p ≡ 1 (mod 3)` (ruling out `p % 3 = 0` and `p % 3 = 2` via the
     product constraint), so `p^k ≡ 1 (mod 3)` and `m² ≡ 1 (mod 3)`, giving `n ≡ 1 (mod 3)`.
     Combined with `n ≡ 1 (mod 4)`, CRT gives `n ≡ 1 (mod 12)`. -/
theorem touchard_congruence (n p k m : ℕ)
    (h_odd : ¬ 2 ∣ n)
    (h_perf : Perfect n)
    (h_euler : n = p ^ k * m ^ 2)
    (hp : Nat.Prime p)
    (hp_mod : p % 4 = 1)
    (hk_mod : k % 4 = 1)
    (hcop : Nat.Coprime (p ^ k) (m ^ 2)) :
    n % 12 = 1 ∨ n % 36 = 9 := by
  -- Step 1: n ≡ 1 (mod 4)
  have hn4 : n % 4 = 1 := h_euler ▸ opn_mod4 p k m (h_euler ▸ h_odd) hp_mod
  -- Step 2: case split on 3 ∣ n
  by_cases h3 : 3 ∣ n
  · -- Case B: 3 ∣ n  →  n ≡ 9 (mod 36)
    right
    -- p ≡ 1 (mod 4) so p ≠ 3 (since 3 ≡ 3 mod 4)
    have hp3 : p ≠ 3 := by omega
    -- 3 ∤ p (as p is prime and p ≠ 3)
    have h3ndvdp : ¬ 3 ∣ p := fun h => by
      have := (hp.eq_one_or_self_of_dvd 3 h).resolve_left (by norm_num)
      omega
    -- 3 ∤ p → 3 ∤ p^k
    have h3ndvdpk : ¬ 3 ∣ p ^ k := fun h =>
      h3ndvdp ((by decide : Nat.Prime 3).dvd_of_dvd_pow h)
    -- 3 ∣ n = p^k · m², 3 ∤ p^k → 3 ∣ m²
    have h3m2 : 3 ∣ m ^ 2 := by
      have := h_euler ▸ h3
      rcases (by decide : Nat.Prime 3).dvd_mul.mp this with h | h
      · exact absurd h h3ndvdpk
      · exact h
    -- 3 prime, 3 ∣ m² → 3 ∣ m
    have h3m : 3 ∣ m := (by decide : Nat.Prime 3).dvd_of_dvd_pow h3m2
    -- 3 ∣ m → 9 ∣ m²
    obtain ⟨t, ht⟩ := h3m
    have h9m2 : 9 ∣ m ^ 2 := ⟨t ^ 2, by rw [ht]; ring⟩
    -- 9 ∣ n
    have h9n : 9 ∣ n := h_euler ▸ h9m2.mul_left (p ^ k)
    -- CRT: n ≡ 1 (mod 4) and 9 ∣ n → n ≡ 9 (mod 36)
    obtain ⟨s, hs⟩ := h9n
    rw [hs] at hn4; omega
  · -- Case A: 3 ∤ n  →  n ≡ 1 (mod 12)
    left
    -- 3 ∤ m  (since 3 ∤ n = p^k · m² and 3 ∤ m² would require 3 ∣ m)
    have h3nm : ¬ 3 ∣ m := fun hm =>
      h3 (h_euler ▸ dvd_mul_of_dvd_right (dvd_pow hm (by norm_num)) (p ^ k))
    -- m² ≡ 1 (mod 3)
    have hm2_3 : m ^ 2 % 3 = 1 := sq_mod3_of_not_dvd h3nm
    -- p ≡ 1 (mod 3): rule out p % 3 = 0 and p % 3 = 2
    have hp_3 : p % 3 = 1 := by
      have hp3_ne0 : p % 3 ≠ 0 := fun h => by
        have h3dvdp : 3 ∣ p := ⟨p / 3, by omega⟩
        have := hp.eq_one_or_self_of_dvd 3 h3dvdp
        omega
      have hp3_ne2 : p % 3 ≠ 2 := fun hp32 => by
        have hkodd : k % 2 = 1 := by omega
        have h3sig : 3 ∣ sigma 1 (p ^ k) :=
          sigma_dvd3_of_p2_kodd p k hp hp32 hkodd
        have hprod : sigma 1 (p ^ k) * sigma 1 (m ^ 2) = 2 * (p ^ k * m ^ 2) :=
          opn_product_constraint (h_euler ▸ h_perf) hcop
        have h3prod : 3 ∣ 2 * (p ^ k * m ^ 2) := hprod ▸ h3sig.mul_right _
        have h3n2 : ¬ 3 ∣ 2 * n := fun h =>
          h3 ((by decide : Nat.Prime 3).dvd_mul.mp h |>.resolve_left (by norm_num))
        exact h3n2 (h_euler ▸ h3prod)
      omega
    -- p^k ≡ 1 (mod 3)
    have hpk_3 : p ^ k % 3 = 1 := pow_mod3_one hp_3 k
    -- n = p^k · m² ≡ 1 · 1 = 1 (mod 3)
    have hn3 : n % 3 = 1 := by
      rw [h_euler, Nat.mul_mod, hpk_3, hm2_3]
    -- CRT: n ≡ 1 (mod 4) and n ≡ 1 (mod 3) → n ≡ 1 (mod 12)
    omega

/-!
### Honest status note

The above proves Touchard's congruence *given* Euler's decomposition as a hypothesis.
The next natural step is:

```lean
-- TODO: add to Mathlib
theorem euler_opn_form (n : ℕ) (h_odd : ¬ 2 ∣ n) (h_perf : Perfect n) :
    ∃ (p k m : ℕ),
      Nat.Prime p ∧ n = p ^ k * m ^ 2 ∧
      p % 4 = 1 ∧ k % 4 = 1 ∧ ¬ p ∣ m := by
  sorry -- Euler 1747. Not yet in Mathlib.
```

Once `euler_opn_form` is proved, `touchard_congruence` becomes unconditional.
The nonexistence conjecture (no OPN exists) has a current lower bound of `10^1500`
(Ochem–Rao 2012) but remains open.
-/

end Nat.ArithmeticFunction.OddPerfect
