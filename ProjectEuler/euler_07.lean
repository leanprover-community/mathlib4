/- Project Euler Problem 7: 10001st prime

By listing the first six prime numbers: 2,3,5,7, 11 , and 13,
we can see that the 6th prime is 13. What is the  10,0001st prime number?
-/

-- import Init.Prelude
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Stream.Defs
--import Mathlib.Data.Nat.Fib.Basic

/-- Finds the next prime strictly greater than n -/
partial def nextPrime (n : Nat) : Nat :=
  let candidate := n + 1
  if candidate.Prime then candidate else nextPrime candidate


/-- Correct way to define primeStream as a function Nat → Nat -/
def primeStream : Stream' ℕ
  | 0     => 2
  | n + 1 => nextPrime (primeStream n)


-- Test the output
#eval (primeStream.drop 10_000) 0 -- 104743
