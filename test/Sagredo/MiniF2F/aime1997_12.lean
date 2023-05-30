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

theorem aime_1997_p11
  (x : ℝ)
  (h₀ : x = (∑ n in Finset.Icc (1 : ℕ) 44, Real.cos (n * π / 180)) / (∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * π / 180))) :
  Int.floor (100 * x) = 241 := by sagredo