/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Linarith.SimplexAlgorithm.SimplexAlgorithm
import Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss

/-!
# `linarith` certificate search a LP problem

`linarith` certificate search can easily be reduced to this LP problem: given the matrix `A` and the
list `strictIndexes`, find the non-negative vector `v` such that some of its coordinates from
the `strictIndexes` are positive and `A v = 0`.

The function `findPositiveVector` solves this problem.
-/

namespace Linarith.SimplexAlgorithm

/--
Given matrix `A` and list `strictIndexes` of strict inequalities' indexes, we want to state the
Linear Programming problem which solution produces solution for the initial problem (see
`findPositiveVector`).

As an objective function (that we are trying to maximize) we use sum of coordinates from
`strictIndexes`: it suffices to find the non-negative vector that makes this function positive.

We introduce two auxiliary variables and one constraint:
* The variable `y` is interpreted as "homogenized" `1`. We need it because dealing with a
  homogenized problem is easier, but having some "unit" is necessary.
* To bound the problem we add the constraint `x₁ + ... + xₘ + z = y` introducing new variable `z`.

The objective function also interpreted as an auxiliary variable with constraint
`f = ∑ i ∈ strictIndexes, xᵢ`.

The variable `f` has to always be basic while `y` has to be free. Our Gauss method implementation
greedy collects basic variables moving from left to right. So we place `f` before `x`-s and `y`
after them. We place `z` between `f` and `x` because in this case `z` will be basic and
`Gauss.getTable` produce table with non-negative last column, meaning that we are starting from
a feasible point.
-/
def stateLP {n m : Nat} (A : Matrix n m) (strictIndexes : List Nat) : Matrix (n + 2) (m + 3) :=
  Id.run do
  let mut objectiveRow : Array Rat := #[-1, 0] ++ (Array.mkArray m 0) ++ #[0]
  for idx in strictIndexes do
    objectiveRow := objectiveRow.set! (idx + 2) 1 -- +2 due to shifting by `f` and `z`

  let constraintRow : Array Rat := #[0, 1] ++ (Array.mkArray m 1) ++ #[-1]

  let data : Array (Array Rat) := #[objectiveRow, constraintRow]
    ++ A.data.map (#[0, 0] ++ · ++ #[0])

  return ⟨data⟩

/-- Extracts target vector from the table, putting auxilary variables aside (see `stateLP`). -/
def extractSolution (table : Table) : Array Rat := Id.run do
  let mut ans : Array Rat := Array.mkArray (table.basic.size + table.free.size - 3) 0
  for i in [1:table.mat.data.size] do
    ans := ans.set! (table.basic[i]! - 2) table.mat.data[i]!.back
  return ans

/--
Finds nonnegative vector `v`, such that `A v = 0` and some of its coordinates from `strictCoords`
are positive, in the case such `v` exists.
-/
def findPositiveVector {n m : Nat} (A : Matrix n m) (strictIndexes : List Nat) : Array Rat :=
  /- State the linear programming problem. -/
  let B := stateLP A strictIndexes

  /- Using Gaussian elimination split variable into free and basic forming the table that will be
  operated by Simplex Algorithm.  -/
  let initTable := Gauss.getTable B

  /- Run Simplex Algorithm and extract the solution. -/
  let resTable := runSimplexAlgorithm initTable
  extractSolution resTable

end Linarith.SimplexAlgorithm
