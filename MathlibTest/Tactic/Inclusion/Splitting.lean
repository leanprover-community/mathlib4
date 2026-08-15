/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
import Mathlib.Tactic.Inclusion.Extension.Extensions

open Inclusion

namespace Inclusion.Tests

def wideInterval : Interval Dyadic := ⟨0, 4⟩

example {x : ℝ} (_hx : x ∈ wideInterval) : True := by
  fail_if_success
    have : x - x ≤ 2 := by
      inclusion [core, real.dyadic]
  trivial

example {x : ℝ} (hx : x ∈ wideInterval) : x - x ≤ 2 := by
  inclusion [core, real.dyadic] (binSplit := 1)

example {x : ℝ} (hx : x ∈ wideInterval) : x - x ≤ 1 := by
  inclusion [core, real.dyadic] (binSplit := 2)

/-- info: The inclusion check succeeded. -/
#guard_msgs in
set_option linter.unusedTactic false in
example {x : ℝ} (hx : x ∈ wideInterval) : x - x ≤ 2 := by
  inclusion? [core, real.dyadic] (binSplit := 1)
  inclusion [core, real.dyadic] (binSplit := 1)

end Inclusion.Tests
