/-
Test file to verify that the theorems moved from PowEqTest.lean work correctly
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Factorization.Defs

namespace Nat

-- Test the prime power theorems
example (p a m n : ℕ) (hp : p.Prime) (h : p ^ m = a ^ n) : m = n * a.factorization p :=
  m_eq_a_factorization_p_of_prime_p_of_p_pow_eq_pow hp h

example (p a m n : ℕ) (hp : p.Prime) (h : p ^ m = a ^ n) : n ∣ m :=
  exponent_dvd_of_prime_pow_eq_pow hp h

example (p a m n : ℕ) (hp : p.Prime) (hn : n ≠ 0) (h : p ^ m = a ^ n) : ∃ k, a = p ^ k :=
  exists_k_base_eq_p_pow_k_of_prime_p_pow_eq_base_pow hp hn h

-- Test the factorization equality variant
example (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (h : a.factorization = b.factorization) : a = b :=
  eq_of_factorization_eq' ha hb h

-- Test the general power equation theorems
example (a b m n : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hmn : m.Coprime n) (h : a ^ m = b ^ n) :
    ∃ c, a = c ^ n ∧ b = c ^ m :=
  exists_eq_pow_of_exponent_coprime_of_pow_eq_pow ha hb hmn h

example (a b m n : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hmn : m ≠ 0 ∨ n ≠ 0) (h : a ^ m = b ^ n) :
    let g := gcd m n; ∃ c, a = c ^ (n / g) ∧ b = c ^ (m / g) :=
  exists_eq_pow_of_pow_eq_pow ha hb hmn h

end Nat
