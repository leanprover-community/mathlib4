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

-- Error: Real.logb
-- theorem aime_1994_p4
--   (n : ℕ)
--   (h₀ : 0 < n)
--   (h₀ : ∑ k in Finset.Icc 1 n, Int.floor (Real.logb 2 k) = 1994) :
--   n = 312 := by sagredo