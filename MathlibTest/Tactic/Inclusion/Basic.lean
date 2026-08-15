/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
import Mathlib.Tactic.Inclusion.Extension.Extensions

open Inclusion

namespace Inclusion.Tests

def unitInterval : Interval Dyadic := ⟨1, 2⟩

example : (1 : ℝ) + 2 ≤ 3 := by
  inclusion [core, real.dyadic]

example : (1 : ℝ) + 2 ≤ 3 := by
  inclusion [core, real.dyadic, core, real.dyadic]

example : -(2 : ℝ) ≤ -1 := by
  inclusion [core, real.dyadic]

example : (3 : ℝ) - 1 ≤ 2 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ unitInterval) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x ∈ Set.Icc 1 2) : x + 1 ≤ 3 := by
  inclusion [core, real.dyadic]

example {x : ℝ} (hx : x = 2) : x + x ≤ 4 := by
  inclusion [core, real.dyadic]

example : (1 : ℝ) ≤ 2 := by
  inclusion +kernel [core, real.dyadic]

/-- info: The inclusion check succeeded. -/
#guard_msgs in
set_option linter.unusedTactic false in
example : (1 : ℝ) ≤ 2 := by
  inclusion? [core, real.dyadic]
  inclusion [core, real.dyadic]

/-- info: The inclusion check failed:
The proposition was not proven true or false. -/
#guard_msgs in
set_option linter.unusedTactic false in
example (h : False) : (2 : ℝ) ≤ 1 := by
  inclusion? [core, real.dyadic]
  exact h.elim

end Inclusion.Tests
