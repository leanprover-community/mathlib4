import Mathlib

namespace Nat

theorem m_eq_a_factorization_p_of_prime_p_of_p_pow_eq_pow
    {p a m n : ℕ} (hp : p.Prime) (h : p ^ m = a ^ n) : m = n * a.factorization p := by
  have := congrArg factorization h
  rw [Prime.factorization_pow hp, factorization_pow] at this
  have := congrFun (congrArg DFunLike.coe this) p
  simp at this
  exact this

theorem exponent_dvd_of_prime_pow_eq_pow
    {p a m n : ℕ} (hp : p.Prime) (h : p ^ m = a ^ n) : n ∣ m := by
  exact Dvd.intro (a.factorization p) (m_eq_a_factorization_p_of_prime_p_of_p_pow_eq_pow hp h).symm

theorem exists_k_base_eq_p_pow_k_of_prime_p_pow_eq_base_pow
    {p a m n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h : p ^ m = a ^ n) : ∃ k, a = p ^ k := by
  rcases exponent_dvd_of_prime_pow_eq_pow hp h with ⟨k, m_eq⟩
  rw [m_eq, pow_mul'] at h
  use k, pow_left_injective hn h.symm

theorem eq_of_factorization_eq' {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.factorization = b.factorization) : a = b := by
  exact eq_of_factorization_eq ha hb (congrFun (congrArg DFunLike.coe h))

theorem exists_eq_pow_of_exponent_coprime_of_pow_eq_pow
    {a b m n : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hmn : m.Coprime n) (h : a ^ m = b ^ n) :
    ∃ c, a = c ^ n ∧ b = c ^ m := by
  by_cases hn : n = 0
  · simp [hn] at h hmn
    simp [hmn] at h
    use b
    simp [h, hn, hmn]
  have factorization_pow_eq := congrArg factorization h
  rw [factorization_pow, factorization_pow] at factorization_pow_eq
  let c_factorization := a.factorization.mapRange (. / n) (Nat.zero_div n)
  let c := c_factorization.prod (. ^ .)
  use c
  have factorization_eq_n_smul_c_factorization_of_eq_c_pow_n
      x (hx : x ≠ 0) n (h : x.factorization = n • c_factorization) : x = c ^ n := by
    suffices x.factorization = (c ^ n).factorization by
      refine eq_of_factorization_eq' hx ?_ this
      suffices c ≠ 0 by exact pow_ne_zero n this
      simp [c, c_factorization]
    convert h
    rw [factorization_pow]
    suffices c.factorization = c_factorization by rw [this]
    unfold c
    refine prod_pow_factorization_eq_self ?_
    intro p p_mem
    exact prime_of_mem_primeFactors ((Finsupp.support_mapRange) p_mem)
  have mul_factorization_p_eq_and_n_dvd_a_factorization_p p :
      m * a.factorization p = n * b.factorization p ∧ n ∣ a.factorization p := by
    have := congrFun (congrArg DFunLike.coe factorization_pow_eq) p
    simp at this
    exact ⟨this, hmn.symm.dvd_of_dvd_mul_left (Dvd.intro (b.factorization p) this.symm)⟩
  constructor
  · apply factorization_eq_n_smul_c_factorization_of_eq_c_pow_n a ha n
    ext p
    simp [c_factorization]
    exact (Nat.mul_div_cancel' (mul_factorization_p_eq_and_n_dvd_a_factorization_p p).2).symm
  · apply factorization_eq_n_smul_c_factorization_of_eq_c_pow_n b hb m
    ext p
    simp [c_factorization]
    rcases mul_factorization_p_eq_and_n_dvd_a_factorization_p p with
      ⟨mul_factorization_p_eq, n_dvd_afp⟩
    rcases n_dvd_afp with ⟨k, afp_eq⟩
    have n_pos := zero_lt_of_ne_zero hn
    have := Nat.div_eq_of_eq_mul_right n_pos afp_eq
    rw [this]
    rw [afp_eq, Nat.mul_left_comm m n k] at mul_factorization_p_eq
    exact Nat.mul_left_cancel n_pos mul_factorization_p_eq.symm

theorem exists_eq_pow_of_pow_eq_pow
    {a b m n : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hmn : m ≠ 0 ∨ n ≠ 0) (h : a ^ m = b ^ n) :
    let g := gcd m n; ∃ c, a = c ^ (n / g) ∧ b = c ^ (m / g) := by
  intro g
  let m' := m / gcd m n
  let n' := n / gcd m n
  have coprime : m'.Coprime n' := by
    rcases hmn with hm | hn
    · exact gcd_div_gcd_div_gcd_of_pos_left (zero_lt_of_ne_zero hm)
    · exact gcd_div_gcd_div_gcd_of_pos_right (zero_lt_of_ne_zero hn)
  have pow_eq : a ^ m' = b ^ n' := by
    conv_lhs at h => rw [show m = m' * g from (Nat.div_mul_cancel (gcd_dvd_left m n)).symm]
    conv_rhs at h => rw [show n = n' * g from (Nat.div_mul_cancel (gcd_dvd_right m n)).symm]
    rw [pow_mul, pow_mul] at h
    have : g ≠ 0 := by
      rcases hmn with hm | hn
      · exact gcd_ne_zero_left hm
      · exact gcd_ne_zero_right hn
    exact pow_left_injective this h
  exact exists_eq_pow_of_exponent_coprime_of_pow_eq_pow ha hb coprime pow_eq

end Nat

section UniqueFactorizationMonoid

end UniqueFactorizationMonoid
