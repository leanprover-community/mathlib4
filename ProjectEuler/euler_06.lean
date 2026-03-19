/- Problem 6   -/
/- Project Euler Problem 6: Sum square difference
The sum of the squares of the first ten natural numbers is,
1² + 2² + ... + 10² = 385
The square of the sum of the first ten natural numbers is,
(1 + 2 + ... + 10)² = 55² = 3025
Hence the difference between the sum of the squares of the first ten natural numbers and the square of the sum is 3025 − 385 = 2640.
Find the difference between the sum of the squares of the first one hundred natural numbers and the square of the sum.
 -/

import Mathlib.Data.Nat.Prime.Basic

def sumOfSquares (n : Nat) : Nat :=
  List.range (n + 1)
  |> List.map (fun x => x * x)
  |> List.sum

def squareOfSum (n : Nat) : Nat :=
  List.range (n + 1)
  |> List.sum
  |> fun x => x * x

def difference (n : ℕ) : ℕ :=
  squareOfSum n - sumOfSquares n

#eval difference 100 -- 25164150
