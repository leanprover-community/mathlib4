/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Field
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Ring.Real

/-!
# The ratio of consecutive Fibonacci numbers

We prove that the ratio of consecutive Fibonacci numbers tends to the golden ratio.
-/

public section

open Nat Real Filter Tendsto
open scoped Topology goldenRatio

/-- The limit of `fib (n + 1) / fib n` as `n → ∞` is the golden ratio. -/
theorem tendsto_fib_succ_div_fib_atTop :
    Tendsto (fun n ↦ (fib (n + 1) / fib n : ℝ)) atTop (𝓝 φ) := by
  have h₁ n : (fib (n + 1) / fib n : ℝ) = (φ - ψ * (ψ / φ) ^ n) / (1 - (ψ / φ) ^ n) := by
    simp only [coe_fib_eq, pow_succ, div_pow]
    field
  have h₂ := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := ψ / φ) <| by
    rw [abs_div, div_lt_one <| by positivity, abs_of_pos goldenRatio_pos, abs_lt]
    ring_nf
    bound
  rw [show φ = (φ - ψ * 0) / (1 - 0) by ring, funext h₁]
  exact const_sub _ (const_mul _ h₂) |>.div (const_sub _ h₂) <| by simp

/-- The limit of `fib n / fib (n + 1)` as `n → ∞` is the negative conjugate of the golden ratio. -/
theorem tendsto_fib_div_fib_succ_atTop :
    Tendsto (fun n ↦ (fib n / fib (n + 1) : ℝ)) atTop (𝓝 (-ψ)) := by
  convert tendsto_fib_succ_div_fib_atTop.inv₀ (by positivity) using 2
  · rw [inv_div]
  · rw [inv_goldenRatio]
