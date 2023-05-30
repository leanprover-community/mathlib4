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

-- Error: irrational
-- theorem mathd_algebra_282
--   (f : ℝ → ℝ)
--   (h₀ : ∀ x, (¬ irrational x) → f x = abs (Int.floor x))
--   (h₁ : ∀ x, (irrational x) → f x = (Int.ceil x)^2) :
--   f (8^(1/3)) + f (-Real.pi) + f (Real.sqrt 50) + f (9/2) = 79 := by sagredo