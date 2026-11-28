import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
# The Euclid–Euler theorem: Mersenne primes give perfect numbers

The **Euclid–Euler theorem** states that an even number is perfect if and only if it is of
the form `2^(p-1) * (2^p - 1)` with `2^p - 1` a (Mersenne) prime. This file proves **both
directions**:

> * **Euclid's part:** if `2^p - 1` is prime, then `2^(p-1) * (2^p - 1)` is perfect.
> * **Euler's part:** every even perfect number has the Mersenne form.

## Main results
* `Nat.sigma` — the divisor function `σ(n) = ∑ d | n, d`.
* `Nat.sigma_mul` — multiplicativity of `σ` on coprime arguments.
* `Nat.sigma_two_pow`, `Nat.sigma_prime` — the values on prime powers and primes.
* `Nat.perfect_of_mersenne_prime` — Euclid's half.
* `Nat.even_perfect_of_mersenne` — Euler's half (via the 2-adic part `ordProj[2]`/`ordCompl[2]`).
* `Nat.euclid_euler` — the full theorem: an even number is perfect iff it has the Mersenne form.
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


/-- 2^k - 1 is odd for k ≥ 1. -/
lemma odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  have h1 : 1 ≤ 2 ^ (k - 1) := Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 2) (k - 1))
  have hkpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
    calc
      2 ^ k = 2 ^ ((k - 1) + 1) := by congr 1; omega
      _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
  have hmain : 2 * (2 ^ (k - 1) - 1) + 1 = 2 ^ k - 1 := by
    rw [hkpow]
    have : 2 ^ (k - 1) - 1 + 1 = 2 ^ (k - 1) := Nat.sub_add_cancel h1
    omega
  exact ⟨2 ^ (k - 1) - 1, hmain.symm⟩

/-- (2^(a+1)-1) ⊥ 2^(a+1). -/
lemma coprime_mersenne_pow_two (a : ℕ) : (2 ^ (a + 1) - 1).Coprime (2 ^ (a + 1)) := by
  have hodd : Odd (2 ^ (a + 1) - 1) := odd_two_pow_sub_one (by omega : 1 ≤ a + 1)
  have h2c : (2 ^ (a + 1) - 1).Coprime 2 := Nat.coprime_two_right.mpr hodd
  exact Nat.Coprime.pow_right (a + 1) h2c

/-- σ(m) ≥ m + 1 for m > 1. -/
lemma sigma_ge_add_one {m : ℕ} (hm1 : 1 < m) : m + 1 ≤ sigma m := by
  unfold sigma
  rw [sum_divisors_eq_sum_properDivisors_add_self]
  have h1 : 1 ∈ m.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd m, hm1⟩
  have hsub : ({1} : Finset ℕ) ⊆ m.properDivisors := by
    intro x hx
    simp at hx
    subst x
    exact h1
  have hge : 1 ≤ ∑ x ∈ m.properDivisors, x := by
    have hle : (∑ x ∈ ({1} : Finset ℕ), x : ℕ) ≤ ∑ x ∈ m.properDivisors, x :=
      Finset.sum_le_sum_of_subset hsub
    have hsum : (∑ x ∈ ({1} : Finset ℕ), x : ℕ) = 1 := by simp
    rwa [hsum] at hle
  omega

/-- If 1 and s are proper divisors of m (s ≠ 1), then σ(m) ≥ m + 1 + s. -/
lemma sigma_ge_add_one_add_s {m s : ℕ} (hm1 : 1 < m) (hs1 : 1 < s) (hsd : s ∣ m) (hsm : s < m) :
    m + 1 + s ≤ sigma m := by
  unfold sigma
  rw [sum_divisors_eq_sum_properDivisors_add_self]
  have h1 : 1 ∈ m.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd m, hm1⟩
  have hsmem : s ∈ m.properDivisors := Nat.mem_properDivisors.mpr ⟨hsd, hsm⟩
  have hsub : ({1, s} : Finset ℕ) ⊆ m.properDivisors := by
    intro x hx
    simp at hx
    rcases hx with hx1 | hxs
    · subst x; exact h1
    · subst x; exact hsmem
  have hge : 1 + s ≤ ∑ x ∈ m.properDivisors, x := by
    have hle : (∑ x ∈ ({1, s} : Finset ℕ), x : ℕ) ≤ ∑ x ∈ m.properDivisors, x :=
      Finset.sum_le_sum_of_subset hsub
    have hsum : (∑ x ∈ ({1, s} : Finset ℕ), x : ℕ) = 1 + s := by simp [ne_of_lt hs1]
    rwa [hsum] at hle
  omega

/-- 2^(a+1)-1 > 1 for a ≥ 1. -/
lemma mersenne_gt_one (a : ℕ) (ha : 1 ≤ a) : 1 < 2 ^ (a + 1) - 1 := by
  have h4 : 4 ≤ 2 ^ (a + 1) := by
    have h : 2 ^ 2 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 2 ≤ a + 1)
    simpa using h
  omega

/-- **Euler's half of the Euclid–Euler theorem:** every even perfect number has the
  Mersenne form `2^(p-1) * (2^p - 1)` with `2^p - 1` prime. -/
theorem even_perfect_of_mersenne {n : ℕ} (hnpos : 0 < n) (heven : Even n) (hnPerfect : Perfect n) :
    ∃ p : ℕ, (2 ^ p - 1).Prime ∧ n = 2 ^ (p - 1) * (2 ^ p - 1) := by
  let a := n.factorization 2
  let m := ordCompl[2] n
  have ha : 1 ≤ a := by
    have hdiv2 : 2 ∣ n := by
      rcases heven with ⟨k, rfl⟩
      exact (by simpa [two_mul] using (dvd_mul_right 2 k) : 2 ∣ k + k)
    exact (Nat.Prime.dvd_iff_one_le_factorization (by norm_num : (2 : ℕ).Prime) (ne_of_gt hnpos)).1 hdiv2
  have hn_eq : n = 2 ^ a * m := by
    simpa [a, m] using (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  have h2cop : (2 : ℕ).Coprime m := by
    simpa [m] using Nat.coprime_ordCompl (by norm_num : (2 : ℕ).Prime) (ne_of_gt hnpos)
  have hcop : (2 ^ a).Coprime m := Nat.Coprime.pow_left a h2cop
  have hperf : sigma n = 2 * n := (perfect_iff_sum_divisors_eq_two_mul hnpos).mp hnPerfect
  have hsig_mul : sigma n = sigma (2 ^ a) * sigma m := by
    rw [hn_eq]
    exact sigma_mul hcop
  have heq : (2 ^ (a + 1) - 1) * sigma m = 2 ^ (a + 1) * m := by
    calc
      (2 ^ (a + 1) - 1) * sigma m = sigma (2 ^ a) * sigma m := by rw [← sigma_two_pow a]
      _ = sigma n := hsig_mul.symm
      _ = 2 * n := hperf
      _ = 2 * (2 ^ a * m) := by rw [hn_eq]
      _ = 2 ^ (a + 1) * m := by
        have hpp : 2 ^ (a + 1) = 2 * 2 ^ a := by
          calc
            2 ^ (a + 1) = 2 ^ a * 2 := by rw [pow_succ]
            _ = 2 * 2 ^ a := by rw [mul_comm]
        rw [hpp]
        ring
  have hdiv : (2 ^ (a + 1) - 1) ∣ m := by
    have hdvd : (2 ^ (a + 1) - 1) ∣ m * 2 ^ (a + 1) :=
      ⟨sigma m, by simpa [mul_comm] using heq.symm⟩
    exact Nat.Coprime.dvd_of_dvd_mul_right (coprime_mersenne_pow_two a) hdvd
  rcases hdiv with ⟨s, hs⟩
  have hm_eq : m = (2 ^ (a + 1) - 1) * s := hs
  have hsig_s : sigma m = 2 ^ (a + 1) * s := by
    have h : (2 ^ (a + 1) - 1) * sigma m = (2 ^ (a + 1) - 1) * (2 ^ (a + 1) * s) := by
      calc
        (2 ^ (a + 1) - 1) * sigma m = 2 ^ (a + 1) * m := heq
        _ = 2 ^ (a + 1) * ((2 ^ (a + 1) - 1) * s) := by rw [hm_eq]
        _ = (2 ^ (a + 1) - 1) * (2 ^ (a + 1) * s) := by ring
    have hg : 0 < 2 ^ (a + 1) - 1 := by have hg1 := mersenne_gt_one a ha; omega
    exact mul_left_cancel₀ (ne_of_gt hg) h
  have hsig_ms : sigma m = m + s := by
    rw [hsig_s, hm_eq]
    have hp : 1 ≤ 2 ^ (a + 1) := Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 2) (a + 1))
    have hrel : 2 ^ (a + 1) = (2 ^ (a + 1) - 1) + 1 := (Nat.sub_add_cancel hp).symm
    nlinarith
  have hs0 : 0 < s := by
    rw [hn_eq] at hnpos
    have hmpos : 0 < m := Nat.pos_of_mul_pos_left hnpos
    have : 0 < (2 ^ (a + 1) - 1) * s := by rwa [← hm_eq]
    exact Nat.pos_of_mul_pos_left this
  have hs_ge1 : 1 ≤ s := by
    have hm1 : 1 < m := by
      have h31 : 3 ≤ 2 ^ (a + 1) - 1 := by
        have h4 : 4 ≤ 2 ^ (a + 1) := by
          have h : 2 ^ 2 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 2 ≤ a + 1)
          simpa using h
        omega
      nlinarith [h31, hs0]
    have hge : m + 1 ≤ sigma m := sigma_ge_add_one hm1
    omega
  have hs_le1 : s ≤ 1 := by
    by_contra hnot
    have hs1 : 1 < s := lt_of_not_ge hnot
    have hm1 : 1 < m := by
      have h31 : 3 ≤ 2 ^ (a + 1) - 1 := by
        have h4 : 4 ≤ 2 ^ (a + 1) := by
          have h : 2 ^ 2 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 2 ≤ a + 1)
          simpa using h
        omega
      nlinarith [h31, hs0]
    have hge2 : m + 1 + s ≤ sigma m := sigma_ge_add_one_add_s hm1 hs1
      (by
        rw [hm_eq]
        exact (by simpa [mul_comm] using (dvd_mul_left s (2 ^ (a + 1) - 1)) : s ∣ (2 ^ (a + 1) - 1) * s))
      (by
        have hg1 : 1 < 2 ^ (a + 1) - 1 := mersenne_gt_one a ha
        rw [hm_eq]
        exact lt_mul_of_one_lt_left hs0 hg1)
    omega
  have hs1 : s = 1 := by omega
  have hm : m = 2 ^ (a + 1) - 1 := by
    rw [hm_eq, hs1]
    simp
  have hprime : (2 ^ (a + 1) - 1).Prime := by
    have hsig : sigma m = m + 1 := by
      rw [hsig_s, hs1, hm]
      have hp : 1 ≤ 2 ^ (a + 1) := Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 2) (a + 1))
      rw [show (2 ^ (a + 1) - 1) + 1 = 2 ^ (a + 1) from (Nat.sub_add_cancel hp)]
      simp
    have hsum : ∑ x ∈ m.properDivisors, x = 1 := by
      unfold sigma at hsig
      have hsig2 : (∑ x ∈ m.properDivisors, x) + m = m + 1 := by
        rw [← sum_divisors_eq_sum_properDivisors_add_self]
        simpa [m] using hsig
      nlinarith [hsig2]
    have hprime_m : m.Prime := (Nat.sum_properDivisors_eq_one_iff_prime.mp hsum)
    simpa [hm] using hprime_m
  refine ⟨a + 1, hprime, ?_⟩
  have hpa : 2 ^ ((a + 1) - 1) = 2 ^ a := by
    congr 1
  calc
    n = 2 ^ a * m := hn_eq
    _ = 2 ^ a * (2 ^ (a + 1) - 1) := by rw [hm]
    _ = 2 ^ ((a + 1) - 1) * (2 ^ (a + 1) - 1) := by rw [hpa]


/-- **The full Euclid–Euler theorem:** an even number is perfect if and only if it has the
  Mersenne form `2^(p-1) * (2^p - 1)` with `2^p - 1` prime. -/
theorem euclid_euler {n : ℕ} (hnpos : 0 < n) (heven : Even n) :
    Nat.Perfect n ↔ ∃ p : ℕ, (2 ^ p - 1).Prime ∧ n = 2 ^ (p - 1) * (2 ^ p - 1) := by
  constructor
  · exact even_perfect_of_mersenne hnpos heven
  · rintro ⟨p, hp, rfl⟩
    exact perfect_of_mersenne_prime hp
end Nat
