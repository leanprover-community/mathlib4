import Mathlib

open Nat Finset

namespace Polynomial

section seven

instance Nat.fact_prime_seven : Fact (Nat.Prime 7) :=
  ⟨by norm_num⟩

theorem cyclotomic_7 : cyclotomic 7 ℤ = 1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 := by
  simp [cyclotomic_prime, sum_range_succ]

end seven

section eleven

instance Nat.fact_prime_eleven : Fact (Nat.Prime 11) :=
  ⟨by norm_num⟩

theorem cyclotomic_11 : cyclotomic 11 ℤ = 1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 +
    X ^ 8 + X ^ 9 + X ^ 10 := by
  simp [cyclotomic_prime, sum_range_succ]

end eleven

section thirteen

instance Nat.fact_prime_thirteen : Fact (Nat.Prime 13) :=
  ⟨by norm_num⟩

theorem cyclotomic_13 : cyclotomic 13 ℤ = 1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 +
    X ^ 8 + X ^ 9 + X ^ 10 + X ^ 11 + X ^ 12 := by
  simp [cyclotomic_prime, sum_range_succ]

end thirteen

section seventeen

instance Nat.fact_prime_fifteen : Fact (Nat.Prime 17) :=
  ⟨by norm_num⟩

theorem cyclotomic_17 : cyclotomic 17 ℤ = 1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 +
    X ^ 8 + X ^ 9 + X ^ 10 + X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14 + X ^ 15 + X ^ 16 := by
  simp [cyclotomic_prime, sum_range_succ]

end seventeen

section nineteen

instance Nat.fact_prime_nineteen : Fact (Nat.Prime 19) :=
  ⟨by norm_num⟩

theorem cyclotomic_19 : cyclotomic 19 ℤ = 1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 +
    X ^ 8 + X ^ 9 + X ^ 10 + X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14 + X ^ 15 + X ^ 16 + X ^ 17 +
    X ^ 18 := by
  simp [cyclotomic_prime, sum_range_succ]

end nineteen

end Polynomial
