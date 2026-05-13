/-
Copyright (c) 2025 Aakash Ali. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aakash Ali
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# Periodicity and surjectivity of linear maps modulo N

This file establishes basic properties of functions of the form
`t ↦ (slope * t + intercept) % N` over `ℕ`.

## Main results

- `LinearMod.linear_mod_periodic` : the map `t ↦ (slope * t + intercept) % N`
  is periodic with period `N`.
- `LinearMod.linear_mod_lt` : the output is always strictly less than `N`.
- `LinearMod.linear_mod_periodic_3_1_7` : concrete instance for slope=3, intercept=1, N=7.
- `LinearMod.linear_mod_surjective_3_1_7` : concrete surjectivity for the same instance,
  proved by explicit witnesses.
-/

namespace LinearMod

/-! ### Periodicity -/

/-- A linear map modulo `N` is periodic with period `N`. -/
theorem linear_mod_periodic (slope intercept N t : ℕ) (_ : 0 < N) :
    (slope * (t + N) + intercept) % N = (slope * t + intercept) % N := by
  have h1 : slope * (t + N) + intercept = slope * t + intercept + slope * N := by ring
  rw [h1, Nat.add_mul_mod_self_right]

/-- The concrete instance: `t ↦ (3 * t + 1) % 7` has period `7`. -/
theorem linear_mod_periodic_3_1_7 (t : ℕ) :
    (3 * (t + 7) + 1) % 7 = (3 * t + 1) % 7 := by
  have h1 : 3 * (t + 7) + 1 = 3 * t + 1 + 3 * 7 := by ring
  rw [h1, Nat.add_mul_mod_self_right]

/-! ### Boundedness -/

/-- The output of `(slope * t + intercept) % N` is strictly less than `N`. -/
theorem linear_mod_lt (slope intercept N t : ℕ) (hN : 0 < N) :
    (slope * t + intercept) % N < N :=
  Nat.mod_lt _ hN

/-! ### Surjectivity: concrete instance -/

/-- The map `t ↦ (3 * t + 1) % 7` is surjective onto `{0, ..., 6}`.

    Proved by explicit witnesses:
    - `r = 0`: `t = 2`, since `(3 * 2 + 1) % 7 = 0`
    - `r = 1`: `t = 0`, since `(3 * 0 + 1) % 7 = 1`
    - `r = 2`: `t = 5`, since `(3 * 5 + 1) % 7 = 2`
    - `r = 3`: `t = 3`, since `(3 * 3 + 1) % 7 = 3`
    - `r = 4`: `t = 1`, since `(3 * 1 + 1) % 7 = 4`
    - `r = 5`: `t = 6`, since `(3 * 6 + 1) % 7 = 5`
    - `r = 6`: `t = 4`, since `(3 * 4 + 1) % 7 = 6` -/
theorem linear_mod_surjective_3_1_7 (r : ℕ) (hr : r < 7) :
    ∃ t : ℕ, (3 * t + 1) % 7 = r := by
  interval_cases r
  · exact ⟨2, by norm_num⟩
  · exact ⟨0, by norm_num⟩
  · exact ⟨5, by norm_num⟩
  · exact ⟨3, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · exact ⟨6, by norm_num⟩
  · exact ⟨4, by norm_num⟩

end LinearMod
