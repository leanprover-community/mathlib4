/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib

open Filter Nat Real
open scoped ArithmeticFunction

theorem log_stirling :
  Tendsto (fun n => Real.log (n)! - (n * Real.log n - n + Real.log n / 2)) atTop (nhds 0) := by
  sorry

-- incorrect, should be prime powers
theorem log_factorial (n : ℕ) :
  Real.log (n)! = ∑ p ∈ primesBelow n, ↑(n / p) * Real.log p  := by
  sorry

theorem sum_cheby_div_id :
  (fun n : ℕ ↦ (∑ k ≤ n, Λ k / k) - Real.log n) =O[atTop] fun _ ↦ (1:ℝ) := by
  sorry
