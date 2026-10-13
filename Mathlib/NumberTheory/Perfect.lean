import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
# The Euclid–Euler theorem: Mersenne primes give perfect numbers

The **Euclid–Euler theorem** states that an even number is perfect if and only if it is of
the form `2^(p-1) * (2^p - 1)` with `2^p - 1` a (Mersenne) prime. This file proves the
**constructive half** (Euclid's part, c. 300 BC):

> If `2^p - 1` is prime, then `2^(p-1) * (2^p - 1)` is a perfect number.

## Main results
* `Nat.sigma` — the divisor function `σ(n) = ∑ d | n, d`.
* `Nat.sigma_mul` — multiplicativity of `σ` on coprime arguments.
* `Nat.sigma_two_pow`, `Nat.sigma_prime` — the values on prime powers and primes.
* `Nat.perfect_of_mersenne_prime` — Euclid's half of the Euclid–Euler theorem.

The converse (Euler's half: every even perfect number is of the Mersenne form) and
Sylvester's theorem on products of consecutive integers are planned as follow-ups.
-/

open BigOperators
open scoped BigOperators

namespace Nat

/-- The sum of the divisors of `n` (the divisor function `σ`). -/
noncomputable def sigma (n : ℕ) : ℕ := ∑ x ∈ n.divisors, x

/-- If `e ∣ b` and `a ⊥ b`, then `a ⊥ e`. -/
lemma coprime_of_dvd_right {a b e : ℕ} (hab : a.Coprime b) (he : e ∣ b) : a.Coprime e := by
  apply Nat.dvd_antisymm
  · have hg : a.gcd e ∣ a.gcd b :=
      Nat.dvd_gcd (Nat.gcd_dvd_left a e) (Nat.dvd_trans (Nat.gcd_dvd_right a e) he)
    rwa [show a.gcd b = 1 from hab] at hg
  · exact Nat.dvd_gcd (show 1 ∣ a from ⟨a, by omega⟩) (show 1 ∣ e from ⟨e, by omega⟩)

/-- `gcd (d*e) a = d` when `d ∣ a` and `a ⊥ e`. -/
lemma gcd_mul_left_of_coprime_dvd {a d e : ℕ} (hd : d ∣ a) (hae : a.Coprime e) :
    (d * e).gcd a = d := by
  apply Nat.dvd_antisymm
  · have hge : (d * e).gcd a ∣ d * e := Nat.gcd_dvd_left (d * e) a
    have hgcop : ((d * e).gcd a).Coprime e := Nat.Coprime.gcd_left (d * e) hae
    exact Nat.Coprime.dvd_of_dvd_mul_right hgcop hge
  · exact Nat.dvd_gcd (dvd_mul_right d e) hd

/-- `σ` is multiplicative on coprime arguments:
  `σ(a·b) = σ(a)·σ(b)` whenever `a ⊥ b`. -/
lemma sigma_mul {a b : ℕ} (hcop : a.Coprime b) : sigma (a * b) = sigma a * sigma b := by
  unfold sigma
  by_cases hab0 : a * b = 0
  · rcases (mul_eq_zero.mp hab0) with ha0 | hb0
    · rw [ha0]; simp [sigma]
    · rw [hb0]; simp [sigma]
  · have hne : a ≠ 0 ∧ b ≠ 0 := (mul_ne_zero_iff.mp hab0)
    calc
      (∑ x ∈ (a * b).divisors, x) = ∑ p ∈ a.divisors ×ˢ b.divisors, p.1 * p.2 := by
        refine Finset.sum_bij' (fun x hx => (x.gcd a, x.gcd b)) (fun p hp => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
        · intro x hx
          rw [Finset.mem_product]
          constructor
          · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right x a, hne.1⟩
          · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right x b, hne.2⟩
        · intro p hp
          rw [Finset.mem_product] at hp
          have hdm : p.1 ∣ a := (Nat.mem_divisors.mp hp.1).1
          have hem : p.2 ∣ b := (Nat.mem_divisors.mp hp.2).1
          exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul hdm hem, hab0⟩
        · intro x hx
          have hxdvd : x ∣ a * b := (Nat.mem_divisors.mp hx).1
          exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).2 hxdvd
        · intro p hp
          rw [Finset.mem_product] at hp
          have hdm : p.1 ∣ a := (Nat.mem_divisors.mp hp.1).1
          have hem : p.2 ∣ b := (Nat.mem_divisors.mp hp.2).1
          have hga : (p.1 * p.2).gcd a = p.1 :=
            gcd_mul_left_of_coprime_dvd hdm (coprime_of_dvd_right hcop hem)
          have hgb' : (p.2 * p.1).gcd b = p.2 :=
            gcd_mul_left_of_coprime_dvd hem (coprime_of_dvd_right (Nat.Coprime.symm hcop) hdm)
          have hgb : (p.1 * p.2).gcd b = p.2 := by simpa [mul_comm] using hgb'
          rw [hga, hgb]
        · intro x hx
          have hxdvd : x ∣ a * b := (Nat.mem_divisors.mp hx).1
          exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).2 hxdvd).symm
      _ = (∑ x ∈ a.divisors, x) * ∑ x ∈ b.divisors, x := by
        simp only [Finset.sum_product]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mul_sum]

/-- The geometric sum `∑_{i<k+1} 2^i = 2^(k+1) - 1`. -/
lemma sum_pow_two (k : ℕ) : (∑ i ∈ Finset.range (k + 1), 2 ^ i) = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    have ha : 1 ≤ 2 ^ (k + 1) := Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 2) (k + 1))
    have h2 : 2 ^ (k + 2) = 2 ^ (k + 1) * 2 := by ring
    rw [h2]
    rw [Nat.mul_comm]
    rw [Nat.two_mul]
    omega

/-- `σ(2^k) = 2^(k+1) - 1`. -/
lemma sigma_two_pow (k : ℕ) : sigma (2 ^ k) = 2 ^ (k + 1) - 1 := by
  unfold sigma
  rw [Nat.sum_divisors_prime_pow (by norm_num : Nat.Prime 2)]
  simpa using sum_pow_two k

/-- `σ(p) = p + 1` for a prime `p`. -/
lemma sigma_prime {p : ℕ} (hp : p.Prime) : sigma p = p + 1 := by
  unfold sigma
  have hpd : p.properDivisors = {1} := Nat.properDivisors_eq_singleton_one_iff_prime.mpr hp
  rw [sum_divisors_eq_sum_properDivisors_add_self]
  rw [hpd]
  simp
  omega

/-- **Euclid's half of the Euclid–Euler theorem:** if `2^p - 1` is a Mersenne prime,
  then `2^(p-1) * (2^p - 1)` is a perfect number. -/
theorem perfect_of_mersenne_prime {p : ℕ} (hp : (2 ^ p - 1).Prime) :
    Perfect (2 ^ (p - 1) * (2 ^ p - 1)) := by
  have hp_ge : 2 ≤ p := by
    by_contra hnot
    have hpl : p ≤ 1 := by omega
    interval_cases p <;> norm_num at hp
  have hodd : Odd (2 ^ p - 1) := hp.odd_of_ne_two (by
    intro h
    have hp1 : 1 ≤ 2 ^ p := Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 2) p)
    have : 2 ^ p = 3 := by omega
    have hpow : 4 ≤ 2 ^ p := by
      have h2 : 2 ^ 2 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hp_ge
      simpa using h2
    omega)
  have h2cop : (2 : ℕ).Coprime (2 ^ p - 1) := Nat.coprime_two_left.mpr hodd
  have hcop : (2 ^ (p - 1)).Coprime (2 ^ p - 1) := Nat.Coprime.pow_left (p - 1) h2cop
  have hnpos : 0 < 2 ^ (p - 1) * (2 ^ p - 1) :=
    Nat.mul_pos (pow_pos (by norm_num : 0 < 2) (p - 1))
      (Nat.sub_pos_of_lt (by
        have : 2 ^ 1 < 2 ^ p := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
        omega))
  rw [perfect_iff_sum_divisors_eq_two_mul hnpos]
  change sigma (2 ^ (p - 1) * (2 ^ p - 1)) = 2 * (2 ^ (p - 1) * (2 ^ p - 1))
  calc
    sigma (2 ^ (p - 1) * (2 ^ p - 1)) = sigma (2 ^ (p - 1)) * sigma (2 ^ p - 1) := sigma_mul hcop
    _ = (2 ^ p - 1) * 2 ^ p := by
      rw [sigma_two_pow (p - 1), sigma_prime hp]
      have hpp : (p - 1) + 1 = p := by omega
      rw [hpp]
      have h1 : 1 ≤ 2 ^ p := Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 2) p)
      rw [show (2 ^ p - 1) + 1 = 2 ^ p from (Nat.sub_add_cancel h1)]
    _ = 2 * (2 ^ (p - 1) * (2 ^ p - 1)) := by
      have hpp : (p - 1) + 1 = p := by omega
      have hpow : 2 ^ p = 2 ^ (p - 1) * 2 := by
        calc
          2 ^ p = 2 ^ ((p - 1) + 1) := by congr 1; omega
          _ = 2 ^ (p - 1) * 2 := by rw [pow_succ]
      rw [hpow]
      ring

end Nat
