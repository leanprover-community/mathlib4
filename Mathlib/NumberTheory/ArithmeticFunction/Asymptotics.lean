/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # Asymptotics of Arithmetic Functions

This file is intended to host results about asymptotic estimates of various arithmetic functions.
-/

@[expose] public section

open Asymptotics Filter

namespace ArithmeticFunction

section sigma

open scoped sigma

theorem sigma_isBigO_pow_succ (k : ℕ) :
    (fun n ↦ (σ k n : ℝ)) =O[atTop] (fun n ↦ (n ^ (k + 1) : ℝ)) := by
  rw [isBigO_iff]
  use 1
  simp only [Real.norm_eq_abs, Nat.abs_cast, norm_pow, one_mul, eventually_atTop]
  use 0
  norm_cast
  grind [sigma_le_pow_succ]

end sigma

end ArithmeticFunction
