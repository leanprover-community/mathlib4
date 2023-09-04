import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card

open Finset

def SchnirelmannDensity (A : Set ℕ) : ℝ := sorry

open Real

-- hints from Bhavik

#check ⨅ (x : ℝ), (x + 1) -- is the Inf of (x + 1) as x ranges over ℝ
#check ⨅ (x : ℝ) (_ : x ≤ 1), x ^ 2 -- is the Inf of x ^ 2 as x ranges over ℝ with x ≤ 1

variable (A : Set ℕ) (n : ℕ) [DecidablePred (· ∈ A)]

#check ((Finset.range n).filter (· ∈ A))
#check Finset.card
