/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Extensions

open Inclusion

namespace Inclusion.Tests

def unitInterval : Interval Dyadic := ⟨1, 2⟩

section Constants

example : (0 : ℝ) ≤ 0 := by
  inclusion [core, interval_dyadic_real]

example : (1 : ℝ) ≤ 1 := by
  inclusion [core, interval_dyadic_real]

example : (2 : ℝ) ≤ 2 := by
  inclusion [core, interval_dyadic_real]

example : ((3 : ℕ) : ℝ) ≤ 3 := by
  inclusion [core, interval_dyadic_real]

example : ((-3 : ℤ) : ℝ) = -3 := by
  inclusion [core, interval_dyadic_real]

end Constants

section Arithmetic

example : (1 : ℝ) + 2 ≤ 3 := by
  inclusion [core, interval_dyadic_real]

example : (1 : ℝ) + 2 ≤ 3 := by
  inclusion [core, interval_dyadic_real, core, interval_dyadic_real]

example : -(2 : ℝ) ≤ -1 := by
  inclusion [core, interval_dyadic_real]

example : (3 : ℝ) - 1 ≤ 2 := by
  inclusion [core, interval_dyadic_real]

end Arithmetic

section Propositions

example : (1 : ℝ) ≤ 2 := by
  inclusion [core, interval_dyadic_real]

example : (2 : ℝ) ≥ 1 := by
  inclusion [core, interval_dyadic_real]

example : (1 : ℝ) < 2 := by
  inclusion [core, interval_dyadic_real]

example : (2 : ℝ) > 1 := by
  inclusion [core, interval_dyadic_real]

example : (1 : ℝ) = 1 := by
  inclusion [core, interval_dyadic_real]

example : (1 : ℝ) ∈ Set.Ici 1 := by
  inclusion [core, interval_dyadic_real]

example : (1 : ℝ) ∈ Set.Iic 1 := by
  inclusion [core, interval_dyadic_real]

example : (1 : ℝ) ∈ Set.Ioi 0 := by
  inclusion [core, interval_dyadic_real]

example : (1 : ℝ) ∈ Set.Iio 2 := by
  inclusion [core, interval_dyadic_real]

example : (1 : ℝ) ∈ Set.Icc 1 1 := by
  inclusion [core, interval_dyadic_real]

example : (1 : ℝ) ∈ Set.Ico 1 2 := by
  inclusion [core, interval_dyadic_real]

example : (1 : ℝ) ∈ Set.Ioc 0 1 := by
  inclusion [core, interval_dyadic_real]

example : (1 : ℝ) ∈ Set.Ioo 0 2 := by
  inclusion [core, interval_dyadic_real]

example : ¬¬(1 : ℝ) ≤ 2 := by
  inclusion [core, interval_dyadic_real]

example : ((1 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 3) := by
  inclusion [core, interval_dyadic_real]

example : ((2 : ℝ) ≤ 1 ∨ (2 : ℝ) ≤ 3) := by
  inclusion [core, interval_dyadic_real]

example : ¬(2 : ℝ) ≤ 1 := by
  inclusion [core, interval_dyadic_real]

example : ¬(2 : ℝ) < 1 := by
  inclusion [core, interval_dyadic_real]

example : (1 : ℝ) ≠ 2 := by
  inclusion [core, interval_dyadic_real]

example : ¬((2 : ℝ) ∈ Set.Icc 0 1) := by
  inclusion [core, interval_dyadic_real]

end Propositions

section Hypotheses

example {x : ℝ} (hx : x ∈ unitInterval) : x + x ≤ 4 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : x ∈ Set.Icc 1 2) : x + 1 ≤ 3 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : x = 2) : x + x ≤ 4 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : 1 ≤ x ∧ x ≤ 2) : x + x ≤ 4 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : x ≤ 2) : x ≤ 2 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : x ≥ 1) : x ≥ 1 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : x < 2) : x < 3 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : x > 1) : x > 0 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : x ∈ Set.Ici 1) : x ∈ Set.Ici 1 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : x ∈ Set.Iic 2) : x ∈ Set.Iic 2 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : x ∈ Set.Ioi 1) : x ∈ Set.Ici 1 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : x ∈ Set.Iio 2) : x ∈ Set.Iic 2 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : x ∈ Set.Icc 1 2) : x ∈ Set.Icc 1 2 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : x ∈ Set.Ico 1 2) : x ∈ Set.Icc 1 2 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : x ∈ Set.Ioc 1 2) : x ∈ Set.Icc 1 2 := by
  inclusion [core, interval_dyadic_real]

example {x : ℝ} (hx : x ∈ Set.Ioo 1 2) : x ∈ Set.Icc 1 2 := by
  inclusion [core, interval_dyadic_real]

example {x y : ℝ} (hx : x ∈ Set.Icc 2 3) (hy : y ∈ Set.Icc 0 1) : ¬x ≤ y := by
  inclusion [core, interval_dyadic_real]

example {x y : ℝ} (hx : x ∈ Set.Icc 2 3) (hy : y ∈ Set.Icc 1 2) : ¬x < y := by
  inclusion [core, interval_dyadic_real]

end Hypotheses

section Evaluation

example : (1 : ℝ) ≤ 2 := by
  inclusion +kernel [core, interval_dyadic_real]

example : ¬(2 : ℝ) ≤ 1 := by
  inclusion +kernel [core, interval_dyadic_real]

/-- info: The inclusion check succeeded. -/
#guard_msgs in
set_option linter.unusedTactic false in
example : (1 : ℝ) ≤ 2 := by
  inclusion? [core, interval_dyadic_real]
  inclusion [core, interval_dyadic_real]

/-- info: The inclusion check failed:
The proposition is provably false -/
#guard_msgs in
set_option linter.unusedTactic false in
example (h : False) : (2 : ℝ) ≤ 1 := by
  inclusion? [core, interval_dyadic_real]
  exact h.elim

end Evaluation

end Inclusion.Tests
