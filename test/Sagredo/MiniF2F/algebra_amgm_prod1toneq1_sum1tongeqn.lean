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

theorem algebra_amgm_prod1toneq1_sum1tongeqn
  (a : ℕ → NNReal)
  (n : ℕ)
  (h₀ : Finset.prod (Finset.range (n)) a = 1) :
  Finset.sum (Finset.range (n)) a ≥ n := by sagredo