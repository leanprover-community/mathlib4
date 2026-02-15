import Mathlib.Tactic.Eval
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Data.Rat.NatSqrt.Real

open Nat

/-
Unfortunately this test run extremely slowly under `lake test`, despite on taking a few seconds
in VSCode or under `lake build MathlibTest` or `lake env lean MathlibTest/sqrt.lean`.

While we investigate, we'll turn off the test.
/--
Compute an explicit rational approximation of `√10005`, accurate to 2 million decimal places.

(This is the square root appearing in the Chudnovsky formula for `π`,
see `Mathlib.Analysis.Real.Pi.Chudnovsky`.)
-/
def sqrt_10005_approx : ℚ := eval% ratSqrt 10005 (10^(2 * 10^6))

theorem sqrt_10005_approx_eq : sqrt_10005_approx = ratSqrt 10005 (10^(2 * 10^6)) := by
  norm_num [sqrt_10005_approx, ratSqrt]

theorem sqrt_10005 :
    √(10005 : ℝ) ∈
      Set.Ico (sqrt_10005_approx : ℝ)
              (sqrt_10005_approx + 1 / 10^(2 * 10^6) : ℝ) := by
  rw [sqrt_10005_approx_eq]
  exact_mod_cast realSqrt_mem_Ico 10005 (by norm_num)

-/
