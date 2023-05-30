import Mathlib.Tactic.GPT.Sagredo.Widget
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Complex.Exponential
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Digits

open BigOperators
open Real
open Nat
open Topology

-- Error: Real^Real
-- theorem mathd_algebra_247
--   (t s : ℝ)
--   (n : ℤ)
--   (h₀ : t = 2 * s - s^2)
--   (h₁ : s = n^2 - 2^n + 1)
--   (n = 3) :
--   t = 0 := by sagredo