/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
import Mathlib.Tactic.Inclusion.Core.Elab
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses

open Inclusion

namespace Inclusion.Tests

-- This family can be used without importing dyadics or real numbers.
example : (2 : ℤ) ^ 100 - 2 ^ 100 + |-3| * (-4) = -12 := by
  inclusion +kernel [core, interval_int]

example {x y : ℤ} (hx : x ∈ Set.Ioo (-3) 2) (hy : 1 ≤ y ∧ y ≤ 3) :
    x ^ 2 * (y - 1) ^ 3 - (x - y) ^ 2 ∈ Set.Icc (-25) 32 ∧ |-x + y| ≤ 5 := by
  inclusion [core, interval_int]

-- Strict bounds are rounded inward before being intersected.
example {x : ℤ} (hx₀ : 0 ≤ x) (hx₁ : 1 < x) (hx₂ : x < 3) (hx₃ : x ≤ 4) :
    x = 2 := by
  inclusion [core, interval_int]

example {x y z : ℤ} (hx : x ∈ Set.Ico 0 2) (hy : y ∈ Set.Ioc 1 3)
    (hz : z ∈ Set.Ioo (-3) 0) : x + y + z ∈ Set.Icc 0 3 := by
  inclusion [core, interval_int]

example {w x y z : ℤ} (hw : w ∈ Set.Ici 1) (hx : x ∈ Set.Iic 2) (hy : y ∈ Set.Ioi 3)
    (hz : z ∈ Set.Iio 4) : w - x + y - z ∈ Set.Ici 0 := by
  inclusion [core, interval_int]

-- Powers and zero products retain useful bounds even for unbounded inputs.
example {x y : ℤ} (hx : x < -2) :
    x ^ 3 ∈ Set.Iic (-27) ∧ x ^ 4 ∈ Set.Ioi 80 ∧ 0 ≤ |y| ∧ 0 * y = 0 ∧ y ^ 0 = 1 := by
  inclusion [core, interval_int]

example {x y : ℤ} (hx : x ∈ (⟨(-2 : ℤ), 3⟩ : Interval ℤ)) (hy : y = -2) :
    x * y ∈ Set.Ico (-6) 5 ∧ -x ∈ Set.Ioc (-4) 2 ∧ x + y ∈ Set.Ioo (-5) 2 := by
  inclusion [core, interval_int]

example {x y : ℤ} (hx : 2 ≤ x) (hy : y < 2) : ¬x ≤ y ∧ x ≠ y := by
  inclusion [core, interval_int]

set_option linter.style.native false in
example {x : ℤ} (hx : x ∈ Set.Icc (-2) 3) : x ^ 2 + |x - 1| ≤ 12 := by
  inclusion +native [core, interval_int]

/-- error: The inclusion check failed:
The proposition is provably false -/
#guard_msgs in
example (h : False) : (3 : ℤ) < 2 := by
  inclusion? [core, interval_int]
  exact h.elim

/-- error: The inclusion check failed:
The proposition was not proven true or false. -/
#guard_msgs in
example (x : ℤ) (h : False) : x ≤ 1 := by
  inclusion? [core, interval_int]
  exact h.elim

end Inclusion.Tests
