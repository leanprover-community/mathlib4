import Mathlib

namespace Nat

theorem exponent_dvd_of_prime_pow_eq_pow {p a m n : ℕ} (hp : p.Prime) (h : p ^ m = a ^ n) : n ∣ m := by
  have := congrArg factorization h
  rw [Prime.factorization_pow hp, factorization_pow] at this
  have := congrFun (congrArg DFunLike.coe this) p
  simp at this
  exact Dvd.intro (a.factorization p) this.symm

theorem exists_k_base_eq_p_pow_k_of_prime_p_pow_eq_base_pow
    {p a m n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h : p ^ m = a ^ n) :
    ∃ k, a = p ^ k := by
  rcases exponent_dvd_of_prime_pow_eq_pow hp h with ⟨k, m_eq⟩
  rw [m_eq, pow_mul'] at h
  use k, pow_left_injective hn h.symm

theorem eq_of_factorization_eq' {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.factorization = b.factorization) : a = b := by
  exact eq_of_factorization_eq ha hb (congrFun (congrArg DFunLike.coe h))

theorem exists_eq_pow_of_exponent_coprime_of_pow_eq {a b m n : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hmn : m.Coprime n) (h : a ^ m = b ^ n) :
    ∃ c, a = c ^ n ∧ b = c ^ m := by
  have := congrArg factorization h
  rw [factorization_pow, factorization_pow] at this
  let c_factorization := a.factorization.mapRange (. / n) (Nat.zero_div n)
  --let factoriztion_prod (factorization : ℕ →₀ ℕ) := factorization.prod (. ^ .)
  let c := c_factorization.prod (. ^ .)
  use c
  constructor
  · --unfold c c_factoriztion
    suffices a.factorization = (c ^ n).factorization by
      refine eq_of_factorization_eq' ha ?_ this
      suffices c ≠ 0 by
        exact pow_ne_zero n this
      unfold c c_factorization
      simp
    suffices a.factorization = n • c_factorization by
      convert this
      rw [factorization_pow]
      suffices c.factorization = c_factorization by
        rw [this]
      unfold c
      refine prod_pow_factorization_eq_self ?_
      intro p p_mem
      --simp [c_factorization] at p_mem
      have : p ∈ a.factorization.support := by
        have : c_factorization.support ⊆ a.factorization.support := by
          exact Finsupp.support_mapRange
        exact this p_mem
      exact prime_of_mem_primeFactors this
    unfold c_factorization
    have : n • Finsupp.mapRange (fun x => x / n) (by simp) a.factorization =
        Finsupp.mapRange (fun x => x / n * n) (by simp) a.factorization := by
      --apply?
      sorry
    sorry
  · sorry

theorem exists_eq_pow_of_pow_eq {a b m n : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hmn : m ≠ 0 ∨ n ≠ 0) (h : a ^ m = b ^ n) :
    let g := gcd m n; ∃ c, a = c ^ (n / g) ∧ b = c ^ (m / g) := by
  intro g
  let m' := m / gcd m n
  let n' := n / gcd m n
  have coprime : m'.Coprime n' := by
    rcases hmn with hm | hn
    · exact gcd_div_gcd_div_gcd_of_pos_left (zero_lt_of_ne_zero hm)
    · exact gcd_div_gcd_div_gcd_of_pos_right (zero_lt_of_ne_zero hn)
  have eq : a ^ m' = b ^ n' := by
    conv_lhs at h => rw [show m = m' * g from (Nat.div_mul_cancel (gcd_dvd_left m n)).symm]
    conv_rhs at h => rw [show n = n' * g from (Nat.div_mul_cancel (gcd_dvd_right m n)).symm]
    rw [pow_mul, pow_mul] at h
    have : g ≠ 0 := by
      rcases hmn with hm | hn
      · exact gcd_ne_zero_left hm
      · exact gcd_ne_zero_right hn
    exact pow_left_injective this h
  exact exists_eq_pow_of_exponent_coprime_of_pow_eq ha hb coprime eq

end Nat

#check factorization
#check UniqueFactorizationMonoid.factors
#check UniqueFactorizationMonoid
section UniqueFactorizationMonoid

end UniqueFactorizationMonoid
