/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Lean.Meta.Basic
import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.SimplexAlgorithm
import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.Gauss

/-!
# `linarith` certificate search as an LP problem

`linarith` certificate search can easily be reduced to the following problem:
given the matrix `A` and the list `strictIndexes`,
find the nonnegative vector `v` such that some of its coordinates from
the `strictIndexes` are positive and `A v = 0`.

The function `findPositiveVector` solves this problem.

# Algorithm sketch

1. We translate the problem stated above to some Linear Programming problem. See `stateLP` for
  details. Let us denote the corresponding matrix `B`.

2. We solve the equation `B x = 0` using Gauss Elimination, splitting the set of variables into
  *free* variables, which can take any value,
  and *basic* variables which are linearly expressed through the free one.
  This gives us an initial tableau for the Simplex Algorithm.
  See `Linarith.SimplexAlgorithm.Gauss.getTableau`.

3. We run the Simplex Algorithm until it finds a solution.
  See the file `SimplexAlgorithm.lean`.

-/

namespace Mathlib.Tactic.Linarith.SimplexAlgorithm

variable {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]

/--
Given matrix `A` and list `strictIndexes` of strict inequalities' indexes, we want to state the
Linear Programming problem which solution would give us a solution for the initial problem (see
`findPositiveVector`).

As an objective function (that we are trying to maximize) we use sum of coordinates from
`strictIndexes`: it suffices to find the nonnegative vector that makes this function positive.

We introduce two auxiliary variables and one constraint:
* The variable `y` is interpreted as "homogenized" `1`. We need it because dealing with a
  homogenized problem is easier, but having some "unit" is necessary.
* To bound the problem we add the constraint `x₁ + ... + xₘ + z = y` introducing new variable `z`.

The objective function also interpreted as an auxiliary variable with constraint
`f = ∑ i ∈ strictIndexes, xᵢ`.

The variable `f` has to always be basic while `y` has to be free. Our Gauss method implementation
greedy collects basic variables moving from left to right. So we place `f` before `x`-s and `y`
after them. We place `z` between `f` and `x` because in this case `z` will be basic and
`Gauss.getTableau` produce tableau with nonnegative last column, meaning that we are starting from
a feasible point.
-/
def stateLP {n m : Nat} (A : matType n m) (strictIndexes : List Nat) : matType (n + 2) (m + 3) :=
  /- +2 due to shifting by `f` and `z` -/
  let objectiveRow : List (Nat × Nat × Rat) :=
    (0, 0, -1) :: strictIndexes.map fun idx => (0, idx + 2, 1)
  let constraintRow : List (Nat × Nat × Rat) :=
    [(1, 1, 1), (1, m + 2, -1)] ++ (List.range m).map (fun i => (1, i + 2, 1))

  let valuesA := getValues A |>.map fun (i, j, v) => (i + 2, j + 2, v)

  ofValues (objectiveRow ++ constraintRow ++ valuesA)

/-- Extracts target vector from the tableau, putting auxiliary variables aside (see `stateLP`). -/
def extractSolution (tableau : Tableau matType) : Array Rat := Id.run do
  let mut ans : Array Rat := Array.replicate (tableau.basic.size + tableau.free.size - 3) 0
  for h : i in [1:tableau.basic.size] do
    ans := ans.set! (tableau.basic[i] - 2) <| tableau.mat[(i, tableau.free.size - 1)]!
  return ans

/--
Finds a nonnegative vector `v`, such that `A v = 0` and some of its coordinates from
`strictCoords`
are positive, in the case such `v` exists. If not, throws the error. The latter prevents
`linarith` from doing useless post-processing.
-/
def findPositiveVector {n m : Nat} {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]
    (A : matType n m) (strictIndexes : List Nat) : Lean.Meta.MetaM <| Array Rat := do
  /- State the linear programming problem. -/
  let B := stateLP A strictIndexes

  /- Using Gaussian elimination split variable into free and basic forming the tableau that will be
  operated by the Simplex Algorithm. -/
  let initTableau ← Gauss.getTableau B

  /- Run the Simplex Algorithm and extract the solution. -/
  let res ← runSimplexAlgorithm.run initTableau
  if res.fst.isOk then
    return extractSolution res.snd
  else
    throwError "Simplex Algorithm failed"

end Mathlib.Tactic.Linarith.SimplexAlgorithm
