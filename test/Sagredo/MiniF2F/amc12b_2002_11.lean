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

theorem amc12b_2002_p11
  (a b : ℕ)
  (h₀ : Nat.Prime a)
  (h₁ : Nat.Prime b)
  (h₂ : Nat.Prime (a + b))
  (h₃ : Nat.Prime (a - b)) :
  Nat.Prime (a + b + (a - b + (a + b))) := by sagredo