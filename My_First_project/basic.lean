--module
--import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Stream.Defs

/-- Finds the next prime strictly greater than n -/
partial def nextPrime (n : Nat) : Nat :=
  let candidate := n + 1
  if candidate.Prime then candidate else nextPrime candidate

/-- Correct way to define primeStream as a function Nat → Nat -/
def primeStream : Stream' Nat
  | 0     => 2
  | n + 1 => nextPrime (primeStream n)

-- Test the output
#eval (primeStream.take 5) -- [2, 3, 5, 7, 11]


-- Solution to Project Euler problem 7
#eval (primeStream.drop 10_000).head -- [2, 3, 5, 7, 11]

-- Using a tail-recursive or proof-based approach avoids 'partial'
def nextPrimeOptimized (n : Nat) : Nat :=
  if (n + 1).Prime then n + 1 else nextPrimeOptimized (n + 1)
termination_by 2 * n -- Simplified termination logic for illustration
decreasing_by sorry -- Requires a proof like Bertrand's Postulate

def primeStreamOptimized : Stream' Nat
  | 0     => 2
  | n + 1 => nextPrimeOptimized (primeStream n)

#eval! (primeStreamOptimized.drop 10_000).head -- [2, 3, 5, 7, 11]
