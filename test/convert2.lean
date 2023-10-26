import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Interval

open BigOperators

example (h : False) (_h₁ : ∑ k in Finset.Icc 0 122, 0 = 0) : 0 ∣ 1 := by
  apply Nat.dvd_of_mul_dvd_mul_left zero_lt_one
  convert dvd_mul_left 0 1
  all_goals contradiction
