import Mathlib

theorem exponent_dvd_of_prime_pow_eq_pow {p a m n : ℕ} (hp : p.Prime) (h : p ^ m = a ^ n) : n ∣ m := by
  have factorization_eq := congrArg Nat.factorization h
  rw [Nat.Prime.factorization_pow hp, Nat.factorization_pow] at factorization_eq
  have := congrFun (congrArg DFunLike.coe factorization_eq) p
  simp at this
  exact Dvd.intro (a.factorization p) this.symm

theorem exists_k_base_eq_p_pow_k_of_prime_p_pow_eq_base_pow
    {p a m n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h : p ^ m = a ^ n) :
    ∃ k, a = p ^ k := by
  rcases exponent_dvd_of_prime_pow_eq_pow hp h with ⟨k, m_eq⟩
  rw [m_eq, show p ^ (n * k) = (p ^ k) ^ n by ring] at h
  use k, Nat.pow_left_injective hn h.symm
