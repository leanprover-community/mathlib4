/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # Asymptotics of Arithmetic Functions

This file is intended to host results about asymptotic estimates of various arithmetic functions.
-/

public section

open Asymptotics Filter

namespace ArithmeticFunction

section sigma

open scoped sigma

theorem sigma_isBigOWith_pow_add_one (k : ℕ) :
    IsBigOWith 1 atTop (fun n ↦ (σ k n : ℝ)) (fun n ↦ (n ^ (k + 1) : ℝ)) := by
  apply isBigOWith_of_le
  intro n
  simp only [Real.norm_eq_abs, Nat.abs_cast, norm_pow]
  norm_cast
  exact sigma_le_pow_succ k n

end sigma

end ArithmeticFunction
