/-
Copyright (c) 2025 Zhipeng Chen, Haolun Tang, Jing Yi Zhan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhipeng Chen, Haolun Tang, Jing Yi Zhan
-/
module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Unitary Divisors and the Unitary Divisor Sum Function

This file defines unitary divisors and the unitary divisor sum function σ*.

A divisor `d` of `n` is called a *unitary divisor* if `gcd(d, n/d) = 1`. The unitary
divisor sum function `σ*(n)` is the sum of all unitary divisors of `n`. This function
is multiplicative: `σ*(mn) = σ*(m) · σ*(n)` when `m` and `n` are coprime.

## Main Definitions

* `Nat.UnitaryDivisor d n`: Predicate stating that `d` is a unitary divisor of `n`.
* `Nat.unitaryDivisors n`: The `Finset` of all unitary divisors of `n`.
* `Nat.unitaryDivisorSum n`: The sum `σ*(n)` of all unitary divisors of `n`.

## Main Results

* `Nat.unitaryDivisorSum_mul`: Multiplicativity of `σ*` for coprime arguments.
* `Nat.unitaryDivisorSum_prime_pow`: For prime `p` and `k ≥ 1`, `σ*(p^k) = p^k + 1`.
* `Nat.unitaryDivisors_prime_pow`: The unitary divisors of `p^k` are exactly `{1, p^k}`.

## Implementation Notes

The definition uses `Nat.divisors` from Mathlib and filters by the coprimality condition.
The multiplicativity proof establishes an explicit bijection between unitary divisors of
a coprime product and pairs of unitary divisors.

## References

* Subbarao, M. V., & Warren, L. J. (1966). Unitary perfect numbers.
  Canadian Mathematical Bulletin, 9(2), 147-153.
* Wall, C. R. (1975). The fifth unitary perfect number.
  Canadian Mathematical Bulletin, 18(1), 115-122.

## Tags

unitary divisor, divisor sum, multiplicative function, number theory
-/

@[expose] public section

namespace Nat

open BigOperators Finset

/-! ### Basic Definitions -/

/-- A divisor `d` of `n` is a *unitary divisor* if `gcd(d, n/d) = 1`.
This means `d` and its complementary divisor share no common factor. -/
def UnitaryDivisor (d n : ℕ) : Prop :=
  d ∣ n ∧ n ≠ 0 ∧ Nat.gcd d (n / d) = 1

/-- The set of all unitary divisors of `n`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  (Nat.divisors n).filter fun d => Nat.gcd d (n / d) = 1

/-- The unitary divisor sum function `σ*(n)`, equal to the sum of all unitary divisors. -/
def unitaryDivisorSum (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

@[inherit_doc] scoped notation "σ*" => unitaryDivisorSum

/-! ### Basic Properties -/

/-- `1` is always a unitary divisor of any nonzero `n`. -/
theorem unitaryDivisor_one (n : ℕ) (hn : n ≠ 0) : UnitaryDivisor 1 n := by
  refine ⟨one_dvd n, hn, ?_⟩
  simp [Nat.div_one]

/-- Every nonzero `n` is a unitary divisor of itself. -/
theorem unitaryDivisor_self (n : ℕ) (hn : n ≠ 0) : UnitaryDivisor n n := by
  refine ⟨dvd_refl n, hn, ?_⟩
  rw [Nat.div_self (Nat.pos_of_ne_zero hn)]
  simp

/-- Membership in `unitaryDivisors` is equivalent to being a unitary divisor. -/
theorem mem_unitaryDivisors {d n : ℕ} (hn : n ≠ 0) :
    d ∈ unitaryDivisors n ↔ UnitaryDivisor d n := by
  simp only [unitaryDivisors, UnitaryDivisor, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · intro ⟨⟨hd, _⟩, hgcd⟩
    exact ⟨hd, hn, hgcd⟩
  · intro ⟨hd, _, hgcd⟩
    exact ⟨⟨hd, hn⟩, hgcd⟩

/-- `1` is in the unitary divisors of any nonzero number. -/
theorem one_mem_unitaryDivisors {n : ℕ} (hn : n ≠ 0) : 1 ∈ unitaryDivisors n :=
  (mem_unitaryDivisors hn).mpr (unitaryDivisor_one n hn)

/-- `n` is in its own unitary divisors when nonzero. -/
theorem self_mem_unitaryDivisors {n : ℕ} (hn : n ≠ 0) : n ∈ unitaryDivisors n :=
  (mem_unitaryDivisors hn).mpr (unitaryDivisor_self n hn)

/-! ### Multiplicativity -/

/-- A divisor of a coprime product decomposes as a product of gcd parts. -/
private lemma divisor_coprime_decompose {m n d : ℕ} (hcoprime : Nat.Coprime m n)
    (hdvd : d ∣ m * n) : d = Nat.gcd d m * Nat.gcd d n := by
  have h := Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime (x := d) hcoprime.symm
  have hdvd' : d ∣ n * m := by rw [mul_comm]; exact hdvd
  rw [mul_comm]
  exact (h.mpr hdvd').symm

/-- If `d₁ ∣ m` and `d₂ ∣ n` with `m`, `n` coprime, then `d₁` and `d₂` are coprime. -/
private lemma coprime_of_dvd_coprime {m n d₁ d₂ : ℕ} (hcoprime : Nat.Coprime m n)
    (h1 : d₁ ∣ m) (h2 : d₂ ∣ n) : Nat.Coprime d₁ d₂ :=
  Nat.Coprime.of_dvd_left h1 (Nat.Coprime.of_dvd_right h2 hcoprime)

/-- For a unitary divisor of a coprime product, `d = gcd(d,m) * gcd(d,n)`. -/
private lemma unitary_divisor_eq_gcd_mul_gcd {m n d : ℕ} (hcoprime : Nat.Coprime m n)
    (h : UnitaryDivisor d (m * n)) : d = Nat.gcd d m * Nat.gcd d n :=
  divisor_coprime_decompose hcoprime h.1

/-- The quotient `(m*n)/d` splits for unitary divisors of coprime products. -/
private lemma unitary_divisor_quotient_split {m n d : ℕ} (hcoprime : Nat.Coprime m n)
    (h : UnitaryDivisor d (m * n)) :
    (m * n) / d = (m / Nat.gcd d m) * (n / Nat.gcd d n) := by
  have hd_eq := unitary_divisor_eq_gcd_mul_gcd hcoprime h
  have hgcd_m_dvd : Nat.gcd d m ∣ m := Nat.gcd_dvd_right d m
  have hgcd_n_dvd : Nat.gcd d n ∣ n := Nat.gcd_dvd_right d n
  conv_lhs => rw [hd_eq]
  calc m * n / (Nat.gcd d m * Nat.gcd d n)
      = m * n / (Nat.gcd d n * Nat.gcd d m) := by rw [Nat.mul_comm (Nat.gcd d m)]
    _ = m * n / Nat.gcd d n / Nat.gcd d m := by rw [Nat.div_div_eq_div_mul]
    _ = m * (n / Nat.gcd d n) / Nat.gcd d m := by rw [Nat.mul_div_assoc _ hgcd_n_dvd]
    _ = (n / Nat.gcd d n) * m / Nat.gcd d m := by rw [Nat.mul_comm m]
    _ = (n / Nat.gcd d n) * (m / Nat.gcd d m) := by rw [Nat.mul_div_assoc _ hgcd_m_dvd]
    _ = (m / Nat.gcd d m) * (n / Nat.gcd d n) := by rw [Nat.mul_comm]

/-- `gcd(d,m)` is a unitary divisor of `m` when `d` is a unitary divisor of `m*n` (coprime). -/
private lemma gcd_unitaryDivisor_left {m n d : ℕ} (hcoprime : Nat.Coprime m n)
    (hm : m ≠ 0) (h : UnitaryDivisor d (m * n)) :
    UnitaryDivisor (Nat.gcd d m) m := by
  refine ⟨Nat.gcd_dvd_right d m, hm, ?_⟩
  have h_unitary := h.2.2
  have hgcd_m_dvd_d : Nat.gcd d m ∣ d := Nat.gcd_dvd_left d m
  have hm_quot_dvd : m / Nat.gcd d m ∣ (m * n) / d := by
    have hq := unitary_divisor_quotient_split hcoprime h
    rw [hq]
    exact Nat.dvd_mul_right _ _
  have h_cop : Nat.Coprime d ((m * n) / d) := h_unitary
  exact Nat.Coprime.coprime_dvd_left hgcd_m_dvd_d
    (Nat.Coprime.coprime_dvd_right hm_quot_dvd h_cop)

/-- `gcd(d,n)` is a unitary divisor of `n` when `d` is a unitary divisor of `m*n` (coprime). -/
private lemma gcd_unitaryDivisor_right {m n d : ℕ} (hcoprime : Nat.Coprime m n)
    (hn : n ≠ 0) (h : UnitaryDivisor d (m * n)) :
    UnitaryDivisor (Nat.gcd d n) n := by
  have h' : UnitaryDivisor d (n * m) := by rw [mul_comm] at h; exact h
  exact gcd_unitaryDivisor_left hcoprime.symm hn h'

/-- A product of unitary divisors of coprime numbers is a unitary divisor of the product. -/
theorem unitaryDivisor_mul_of_coprime {m n d₁ d₂ : ℕ} (hcoprime : Nat.Coprime m n)
    (hm : m ≠ 0) (hn : n ≠ 0) (h1 : UnitaryDivisor d₁ m) (h2 : UnitaryDivisor d₂ n) :
    UnitaryDivisor (d₁ * d₂) (m * n) := by
  refine ⟨Nat.mul_dvd_mul h1.1 h2.1, mul_ne_zero hm hn, ?_⟩
  have hq : (m * n) / (d₁ * d₂) = (m / d₁) * (n / d₂) := by
    rw [Nat.mul_comm d₁ d₂, ← Nat.div_div_eq_div_mul]
    rw [Nat.mul_div_assoc _ h2.1]
    rw [Nat.mul_comm m, Nat.mul_div_assoc _ h1.1]
    rw [mul_comm]
  suffices Nat.Coprime (d₁ * d₂) ((m / d₁) * (n / d₂)) by rw [hq]; exact this
  have hcop_d1_mq : Nat.Coprime d₁ (m / d₁) := h1.2.2
  have hcop_d2_nq : Nat.Coprime d₂ (n / d₂) := h2.2.2
  have hnq_dvd_n : n / d₂ ∣ n := Nat.div_dvd_of_dvd h2.1
  have hcop_d1_nq : Nat.Coprime d₁ (n / d₂) := coprime_of_dvd_coprime hcoprime h1.1 hnq_dvd_n
  have hmq_dvd_m : m / d₁ ∣ m := Nat.div_dvd_of_dvd h1.1
  have hcop_d2_mq : Nat.Coprime d₂ (m / d₁) := coprime_of_dvd_coprime hcoprime.symm h2.1 hmq_dvd_m
  have h1' : Nat.Coprime d₁ ((m / d₁) * (n / d₂)) := Nat.Coprime.mul_right hcop_d1_mq hcop_d1_nq
  have h2' : Nat.Coprime d₂ ((m / d₁) * (n / d₂)) := Nat.Coprime.mul_right hcop_d2_mq hcop_d2_nq
  exact Nat.Coprime.mul_left h1' h2'

/-- **Multiplicativity of σ***. For coprime `m` and `n`, `σ*(mn) = σ*(m) · σ*(n)`.

This is proved by establishing a bijection between unitary divisors of `m*n` and
pairs `(d₁, d₂)` of unitary divisors of `m` and `n` respectively. The bijection is
`d ↦ (gcd(d,m), gcd(d,n))` with inverse `(d₁, d₂) ↦ d₁ * d₂`. -/
theorem unitaryDivisorSum_mul {m n : ℕ} (hcoprime : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) :
    σ* (m * n) = σ* m * σ* n := by
  unfold unitaryDivisorSum
  let i : ℕ → ℕ × ℕ := fun d => (Nat.gcd d m, Nat.gcd d n)
  let j : ℕ × ℕ → ℕ := fun p => p.1 * p.2
  have h_sum_bij : ∑ d ∈ unitaryDivisors (m * n), d =
                   ∑ p ∈ unitaryDivisors m ×ˢ unitaryDivisors n, p.1 * p.2 := by
    apply Finset.sum_nbij' i j
    · intro d hd
      simp only [Finset.mem_product]
      have h_in : UnitaryDivisor d (m * n) := (mem_unitaryDivisors (mul_ne_zero hm hn)).mp hd
      have h1 := gcd_unitaryDivisor_left hcoprime hm h_in
      have h2 := gcd_unitaryDivisor_right hcoprime hn h_in
      exact ⟨(mem_unitaryDivisors hm).mpr h1, (mem_unitaryDivisors hn).mpr h2⟩
    · intro p hp
      simp only [Finset.mem_product] at hp
      have h1 : UnitaryDivisor p.1 m := (mem_unitaryDivisors hm).mp hp.1
      have h2 : UnitaryDivisor p.2 n := (mem_unitaryDivisors hn).mp hp.2
      exact (mem_unitaryDivisors (mul_ne_zero hm hn)).mpr
        (unitaryDivisor_mul_of_coprime hcoprime hm hn h1 h2)
    · intro d hd
      have h_in : UnitaryDivisor d (m * n) := (mem_unitaryDivisors (mul_ne_zero hm hn)).mp hd
      exact (unitary_divisor_eq_gcd_mul_gcd hcoprime h_in).symm
    · intro p hp
      simp only [Finset.mem_product] at hp
      have h1 : UnitaryDivisor p.1 m := (mem_unitaryDivisors hm).mp hp.1
      have h2 : UnitaryDivisor p.2 n := (mem_unitaryDivisors hn).mp hp.2
      have h1_dvd : p.1 ∣ m := h1.1
      have h2_dvd : p.2 ∣ n := h2.1
      have hg1_m : Nat.gcd p.1 m = p.1 := Nat.gcd_eq_left h1_dvd
      have hg2_m : Nat.gcd p.2 m = 1 := Nat.Coprime.coprime_dvd_left h2_dvd hcoprime.symm
      have hg1_n : Nat.gcd p.1 n = 1 := Nat.Coprime.coprime_dvd_left h1_dvd hcoprime
      have hg2_n : Nat.gcd p.2 n = p.2 := Nat.gcd_eq_left h2_dvd
      ext
      · change Nat.gcd (p.1 * p.2) m = p.1
        rw [mul_comm]
        exact Nat.gcd_mul_of_coprime_of_dvd hg2_m h1_dvd
      · change Nat.gcd (p.1 * p.2) n = p.2
        exact Nat.gcd_mul_of_coprime_of_dvd hg1_n h2_dvd
    · intro d hd
      have h_in : UnitaryDivisor d (m * n) := (mem_unitaryDivisors (mul_ne_zero hm hn)).mp hd
      exact unitary_divisor_eq_gcd_mul_gcd hcoprime h_in
  rw [h_sum_bij, Finset.sum_product', Finset.sum_mul_sum]

/-! ### Prime Powers -/

/-- For any `p`, `gcd(p^i, p^j) = p^(min i j)`. -/
private lemma gcd_pow_self (p i j : ℕ) : Nat.gcd (p ^ i) (p ^ j) = p ^ min i j := by
  by_cases h : i ≤ j
  · rw [min_eq_left h]
    exact Nat.gcd_eq_left (pow_dvd_pow p h)
  · push_neg at h
    rw [min_eq_right (Nat.le_of_lt h), Nat.gcd_comm]
    exact Nat.gcd_eq_left (pow_dvd_pow p (Nat.le_of_lt h))

/-- For `0 < i < k`, `p^i` is not a unitary divisor of `p^k`. -/
private lemma not_unitaryDivisor_prime_pow_intermediate {p k i : ℕ} (hp : Nat.Prime p)
    (hi : 0 < i) (hi_lt : i < k) :
    ¬UnitaryDivisor (p ^ i) (p ^ k) := by
  intro ⟨_, _, hgcd⟩
  have hquot : p ^ k / p ^ i = p ^ (k - i) := Nat.pow_div hi_lt.le hp.pos
  rw [hquot, gcd_pow_self] at hgcd
  have h_min_pos : 0 < min i (k - i) := by
    by_cases h_case : i ≤ k - i
    · rw [min_eq_left h_case]; exact hi
    · push_neg at h_case
      rw [min_eq_right (Nat.le_of_lt h_case)]
      exact Nat.sub_pos_of_lt hi_lt
  have h_ge_p : p ^ min i (k - i) ≥ p := by
    calc p ^ min i (k - i) ≥ p ^ 1 := Nat.pow_le_pow_right hp.pos h_min_pos
      _ = p := pow_one p
  have h_p_ge_2 : p ≥ 2 := hp.two_le
  omega

/-- Any divisor of `p^k` has the form `p^i` for some `i ≤ k`. -/
private lemma divisor_of_prime_pow {p k d : ℕ} (hp : Nat.Prime p) (hdvd : d ∣ p ^ k) :
    ∃ i : ℕ, i ≤ k ∧ d = p ^ i := by
  induction k generalizing d with
  | zero => simp only [pow_zero, dvd_one] at hdvd; exact ⟨0, le_refl 0, hdvd⟩
  | succ k ih =>
    by_cases hp_dvd_d : p ∣ d
    · obtain ⟨m, rfl⟩ := hp_dvd_d
      have hm_dvd : m ∣ p ^ k := by
        have : p * m ∣ p * p ^ k := by
          have heq : p ^ (k + 1) = p * p ^ k := by rw [pow_succ, mul_comm]
          rw [heq] at hdvd; exact hdvd
        exact Nat.dvd_of_mul_dvd_mul_left hp.pos this
      obtain ⟨j, hj_le, rfl⟩ := ih hm_dvd
      exact ⟨j + 1, by omega, by rw [pow_succ, mul_comm]⟩
    · have hgcd : Nat.gcd d p = 1 := by
        have : Nat.gcd d p ∣ p := Nat.gcd_dvd_right d p
        rcases hp.eq_one_or_self_of_dvd _ this with h | h
        · exact h
        · exact absurd (h ▸ Nat.gcd_dvd_left d p) hp_dvd_d
      have hgcd_pow : Nat.gcd d (p ^ (k + 1)) = 1 := by
        rw [Nat.gcd_comm] at hgcd
        exact (Nat.Coprime.pow_left (k + 1) hgcd).symm.gcd_eq_one
      have hd_eq_1 : d = 1 := by
        have : d ∣ Nat.gcd d (p ^ (k + 1)) := Nat.dvd_gcd (dvd_refl d) hdvd
        rw [hgcd_pow] at this
        exact Nat.eq_one_of_dvd_one this
      exact ⟨0, by omega, by simp [hd_eq_1]⟩

/-- The unitary divisors of `p^k` (for prime `p`) are exactly `{1, p^k}`. -/
theorem unitaryDivisors_prime_pow {p k : ℕ} (hp : Nat.Prime p) :
    unitaryDivisors (p ^ k) = {1, p ^ k} := by
  ext d
  constructor
  · intro hd
    simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hgcd⟩ := hd
    obtain ⟨i, hi_le, rfl⟩ := divisor_of_prime_pow hp hdvd
    by_cases hi_zero : i = 0
    · simp [hi_zero]
    · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
      by_cases hi_eq_k : i = k
      · simp [hi_eq_k]
      · have hi_lt : i < k := Nat.lt_of_le_of_ne hi_le hi_eq_k
        have h_is_unitary : UnitaryDivisor (p ^ i) (p ^ k) :=
          ⟨hdvd, pow_ne_zero k hp.ne_zero, hgcd⟩
        exact absurd h_is_unitary (not_unitaryDivisor_prime_pow_intermediate hp hi_pos hi_lt)
  · intro hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact (mem_unitaryDivisors (pow_ne_zero k hp.ne_zero)).mpr
        (unitaryDivisor_one _ (pow_ne_zero k hp.ne_zero))
    · exact (mem_unitaryDivisors (pow_ne_zero k hp.ne_zero)).mpr
        (unitaryDivisor_self _ (pow_ne_zero k hp.ne_zero))

/-- **Prime power formula**: For prime `p` and `k ≥ 1`, `σ*(p^k) = p^k + 1`. -/
theorem unitaryDivisorSum_prime_pow {p k : ℕ} (hp : Nat.Prime p) (hk : k ≠ 0) :
    σ* (p ^ k) = p ^ k + 1 := by
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
  unfold unitaryDivisorSum
  rw [unitaryDivisors_prime_pow hp]
  have h_ne : 1 ≠ p ^ k := by
    intro h_eq
    have hp_ge : p ≥ 2 := hp.two_le
    have hpk_ge : p ^ k ≥ p := by
      calc p ^ k ≥ p ^ 1 := Nat.pow_le_pow_right hp.pos hk_pos
        _ = p := pow_one p
    omega
  simp only [Finset.sum_insert (notMem_singleton.mpr h_ne), Finset.sum_singleton]
  ac_rfl

/-! ### Additional Properties -/

/-- `σ*(1) = 1`. -/
@[simp]
theorem unitaryDivisorSum_one : σ* 1 = 1 := by
  unfold unitaryDivisorSum unitaryDivisors
  simp only [Nat.divisors_one, Finset.filter_singleton, Nat.gcd_self,
    ite_true, Finset.sum_singleton]

end Nat
