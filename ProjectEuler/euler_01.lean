/- Project Euler Problem 1: Multiples of 3 and 5

If we list all the natural numbers below 10 that are multiples of 3 or 5,
we get 3, 5, 6 and 9.  The sum of these multiples is 23.
Find the sum of all the multiples of 3 or 5 below 1000.
 -/

-- Using the Unicode ℕ symbol (requires import)
import Mathlib.Data.Nat.Basic

def sumMultiples (n : ℕ) : ℕ :=
  List.range n
  |> List.filter (fun x => x % 3 == 0 || x % 5 == 0)
  |> List.sum

#eval sumMultiples 1_000 -- 233168
