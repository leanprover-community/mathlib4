/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Linarith.SimplexAlgorithm.Datatypes

/-!
# Simplex Algorithm

To obtain required vector in `Linarith.SimplexAlgorithm.findPositiveVector` we run the Simplex
Algorithm. We use Bland's rule for pivoting, which guarantees that the algorithm terminates.
-/

namespace Linarith.SimplexAlgorithm

/-- An exception in the `SimplexAlgorithmM` monad. -/
inductive SimplexAlgorithmException
  /-- The solution is infeasible. -/
| infeasible : SimplexAlgorithmException

/-- The mutable state for the `SimplexAlgorithmM` monad. -/
structure SimplexAlgorithmState where
  /-- Current table. -/
  table : Table

/-- The monad for the Simplex Algorithm. -/
abbrev SimplexAlgorithmM := ExceptT SimplexAlgorithmException <| StateM SimplexAlgorithmState

-- def printtt (table : Table) : SimplexAlgorithmM Unit := do
--   dbg_trace "~~~~~~~~~~~~~~~~~~~~~~~~~~~"
--   dbg_trace s!"free: {table.free}"
--   dbg_trace s!"basic: {table.basic}"
--   for ⟨b, b_idx⟩ in table.basic.zipWithIndex do
--    let arr : List Rat := (List.range table.free.size).map fun idx => table.mat[b_idx]!.findD idx 0
--     dbg_trace arr
--   dbg_trace "~~~~~~~~~~~~~~~~~~~~~~~~~~~"

/--
Given indexes `exitIdx` and `enterIdx` of exiting and entering variables in the `basic` and `free`
arrays, performs pivot operation, i.e. expresses one through the other and makes the free one basic
and vice versa.
-/
def doPivotOperation (exitIdx enterIdx : Nat) : SimplexAlgorithmM Unit := do
  -- printtt (← get).table
  let mat := (← get).table.mat
  -- let intersectCoef := mat[exitIdx]![enterIdx]!
  let intersectCoef := mat[exitIdx]!.find! enterIdx

  let mut newCurRow := mat[exitIdx]!
  -- newCurRow := newCurRow.set! enterIdx (-1)
  newCurRow := newCurRow.insert enterIdx (-1)
  -- newCurRow := newCurRow.map (- · / intersectCoef)
  newCurRow := newCurRow.fold (fun cur k v => cur.insert k (-v / intersectCoef)) newCurRow
  let mut newData : Array (Lean.HashMap Nat Rat) := mat.data.map fun row =>
    -- let newRow := row.zipWith mat[exitIdx]! fun x y => x - row[enterIdx]! * y / intersectCoef
    let coef := (row.findD enterIdx 0) / intersectCoef
    let newRow := mat[exitIdx]!.fold (fun cur k v =>
      let newVal := (cur.findD k 0) - v * coef
      if newVal != 0 then cur.insert k newVal else cur.erase k
    ) row
    -- newRow.set! enterIdx <| row[enterIdx]! / intersectCoef
    newRow.insert enterIdx <| (row.findD enterIdx 0) / intersectCoef
  newData := newData.set! exitIdx newCurRow

  let newBasic : Array Nat := (← get).table.basic.set! exitIdx (← get).table.free[enterIdx]!
  let newFree : Array Nat := (← get).table.free.set! enterIdx (← get).table.basic[exitIdx]!

  let newMat : SparseMatrix newBasic.size newFree.size := ⟨newData⟩
  set ({← get with table := ⟨newBasic, newFree, newMat⟩} : SimplexAlgorithmState)

/--
Check if the solution is found: the objective function is positive and all basic variables are
nonnegative.
-/
def checkSuccess : SimplexAlgorithmM Bool := do
  -- return (← get).table.mat[0]!.back > 0 && (← get).table.mat.data.all (fun row => row.back >= 0)
  let lastIdx := (← get).table.free.size - 1
  return (← get).table.mat[0]!.findD lastIdx 0 > 0 &&
    (← get).table.mat.data.all (fun row => row.findD lastIdx 0 >= 0)

/--
Chooses an entering variable: among the variables with a positive coefficient in the objective
function, the one with the smallest index (in the initial indexing).
-/
def chooseEnteringVar : SimplexAlgorithmM Nat := do
  let mut enterIdxOpt : Option Nat := .none -- index of entering variable in the `free` array
  let mut minIdx := 0
  for i in [:(← get).table.free.size - 1] do
    if (← get).table.mat[0]!.findD i 0 > 0 &&
        (enterIdxOpt.isNone || (← get).table.free[i]! < minIdx) then
      enterIdxOpt := i
      minIdx := (← get).table.free[i]!

  /- If there is no such variable the solution does not exist for sure. -/
  match enterIdxOpt with
  | .none => throw SimplexAlgorithmException.infeasible
  | .some enterIdx => return enterIdx

/--
Chooses an exiting variable: the variable imposing the strictest limit on the increase of the
entering variable, breaking ties by choosing the variable with smallest index.
-/
def chooseExitingVar (enterIdx : Nat) : SimplexAlgorithmM Nat := do
  let mut exitIdxOpt : Option Nat := .none -- index of entering variable in the `basic` array
  let mut minCoef := 0
  let mut minIdx := 0
  for i in [1:(← get).table.mat.data.size] do
    if (← get).table.mat[i]!.findD enterIdx 0 >= 0 then
      continue
    let lastIdx := (← get).table.free.size - 1
    let coef := -(← get).table.mat[i]!.findD lastIdx 0 / (← get).table.mat[i]!.find! enterIdx
    if exitIdxOpt.isNone || coef < minCoef ||
        (coef == minCoef && (← get).table.basic[i]! < minIdx) then
      exitIdxOpt := i
      minCoef := coef
      minIdx := (← get).table.basic[i]!
  return exitIdxOpt.get! -- such variable always exists because our problem is bounded

/--
Chooses entering and exiting variables using Bland's rule that guarantees that the Simplex
Algorithm terminates.
-/
def choosePivots : SimplexAlgorithmM (Nat × Nat) := do
  let enterIdx ← chooseEnteringVar
  let exitIdx ← chooseExitingVar enterIdx
  return ⟨exitIdx, enterIdx⟩

/--
Runs Simplex Algorithm starting with `initTable`. It always terminates, finding solution if
such exists.
-/
def runSimplexAlgorithm : SimplexAlgorithmM Unit := do
  -- printtt (← get).table
  while !(← checkSuccess) do
    let ⟨exitIdx, enterIdx⟩ ← choosePivots
    doPivotOperation exitIdx enterIdx

end Linarith.SimplexAlgorithm
