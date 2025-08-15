import Mathlib

namespace Nat

theorem exponent_dvd_of_prime_pow_eq_pow {p a m n : ℕ} (hp : p.Prime) (h : p ^ m = a ^ n) : n ∣ m := by
  have factorization_eq := congrArg factorization h
  rw [Prime.factorization_pow hp, factorization_pow] at factorization_eq
  have := congrFun (congrArg DFunLike.coe factorization_eq) p
  simp at this
  exact Dvd.intro (a.factorization p) this.symm

theorem exists_k_base_eq_p_pow_k_of_prime_p_pow_eq_base_pow
    {p a m n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h : p ^ m = a ^ n) :
    ∃ k, a = p ^ k := by
  rcases exponent_dvd_of_prime_pow_eq_pow hp h with ⟨k, m_eq⟩
  rw [m_eq, pow_mul'] at h
  use k, pow_left_injective hn h.symm

theorem exists_eq_pow_of_exponent_coprime_of_pow_eq {a b m n : ℕ} (hmn : m.Coprime n) (h : a ^ m = b ^ n) :
    ∃ c, a = c ^ n ∧ b = c ^ m := by
  have factorization_eq := congrArg factorization h

  sorry

theorem exists_eq_pow_of_pow_eq {a b m n : ℕ} (hmn : m ≠ 0 ∨ n ≠ 0) (h : a ^ m = b ^ n) :
    let g := gcd m n; ∃ c, a = c ^ (n / g) ∧ b = c ^ (m / g) := by
  intro g
  let m' := m / gcd m n
  let n' := n / gcd m n
  have coprime : m'.Coprime n' := by
    rcases hmn with hm | hn
    . exact gcd_div_gcd_div_gcd_of_pos_left (zero_lt_of_ne_zero hm)
    . exact gcd_div_gcd_div_gcd_of_pos_right (zero_lt_of_ne_zero hn)
  have eq : a ^ m' = b ^ n' := by
    conv_lhs at h => rw [show m = m' * g from (Nat.div_mul_cancel (gcd_dvd_left m n)).symm]
    conv_rhs at h => rw [show n = n' * g from (Nat.div_mul_cancel (gcd_dvd_right m n)).symm]
    rw [pow_mul', pow_mul'] at h
    sorry
  exact exists_eq_pow_of_exponent_coprime_of_pow_eq coprime eq

end Nat

#check factorization
#check UniqueFactorizationMonoid.factors
#check UniqueFactorizationMonoid

section UniqueFactorizationMonoid

end UniqueFactorizationMonoid
