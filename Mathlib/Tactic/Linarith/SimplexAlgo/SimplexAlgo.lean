/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Linarith.SimplexAlgo.Datatypes

/-!
# Simplex Algorithm

To obtain required vector in `Linarith.SimplexAlgo.findPositiveVector` we run the Simplex Algorithm.
We use Bland's rule for pivoting, which guarantees that the algorithm terminates.
-/

namespace Linarith.SimplexAlgo

/-- An exception in the `SimplexAlgoM` monad. -/
inductive SimplexAlgoException
| infeasible : SimplexAlgoException

/-- The mutable state for the `SimplexAlgoM` monad. -/
structure SimplexAlgoState where
  /-- Current table. -/
  table : Table

/-- The monad for the Simplex Algorithm. -/
abbrev SimplexAlgoM := ExceptT SimplexAlgoException <| StateM SimplexAlgoState

/--
Given indexes `exitIdx` and `enterIdx` of exiting and entering variables in the `basic` and `free`
arrays, performs pivot operation, i.e. expresses one through the other and makes the free one basic
and vice versa.
-/
def doPivotOperation (exitIdx enterIdx : Nat) : SimplexAlgoM Unit := do
  let mat := (← get).table.mat
  let intersectCoef := mat[exitIdx]![enterIdx]!

  let mut newCurRow := mat[exitIdx]!
  newCurRow := newCurRow.set! enterIdx (-1)
  newCurRow := newCurRow.map (- · / intersectCoef)
  let mut newData : Array (Array Rat) := mat.data.map fun row =>
    let newRow := row.zipWith mat[exitIdx]! fun x y => x - row[enterIdx]! * y / intersectCoef
    newRow.set! enterIdx <| row[enterIdx]! / intersectCoef
  newData := newData.set! exitIdx newCurRow

  let newBasic : Array Nat := (← get).table.basic.set! exitIdx (← get).table.free[enterIdx]!
  let newFree : Array Nat := (← get).table.free.set! enterIdx (← get).table.basic[exitIdx]!

  let newMat : Matrix newBasic.size newFree.size := ⟨newData⟩
  set ({← get with table := ⟨newBasic, newFree, newMat⟩} : SimplexAlgoState)

/--
Check if the solution is found: the objective function is positive and all basic variables are
nonnegative.
-/
def checkSuccess : SimplexAlgoM Bool := do
  return (← get).table.mat[0]!.back > 0 && (← get).table.mat.data.all (fun row => row.back >= 0)

/--
Chooses an entering variable: among the variables with a positive coefficient in the objective
function, the one with the smallest index (in the initial indexing).
-/
def chooseEnteringVar : SimplexAlgoM Nat := do
  let mut enterIdxOpt : Option Nat := .none -- index of entering variable in the `free` array
  let mut minIdx := 0
  for i in [:(← get).table.mat[0]!.size - 1] do
    if (← get).table.mat[0]![i]! > 0 && (enterIdxOpt.isNone || (← get).table.free[i]! < minIdx) then
      enterIdxOpt := i
      minIdx := (← get).table.free[i]!

  /- If there is no such variable the solution does not exist for sure. -/
  match enterIdxOpt with
  | .none => throw SimplexAlgoException.infeasible
  | .some enterIdx => return enterIdx

/--
Chooses an exiting variable: the variable imposing the strictest limit on the increase of the
entering variable, breaking ties by choosing the variable with smallest index.
-/
def chooseExitingVar (enterIdx : Nat) : SimplexAlgoM Nat := do
  let mut exitIdxOpt : Option Nat := .none -- index of entering variable in the `basic` array
  let mut minCoef := 0
  let mut minIdx := 0
  for i in [1:(← get).table.mat.data.size] do
    if (← get).table.mat[i]![enterIdx]! >= 0 then
      continue
    let coef := -(← get).table.mat[i]!.back / (← get).table.mat[i]![enterIdx]!
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
def choosePivots : SimplexAlgoM (Nat × Nat) := do
  let enterIdx ← chooseEnteringVar
  let exitIdx ← chooseExitingVar enterIdx
  return ⟨exitIdx, enterIdx⟩

/-- Implementation of `runSimplexAlgo` in `SimplexAlgoM` monad. -/
def runSimplexAlgoImp : SimplexAlgoM Unit := do
  while !(← checkSuccess) do
    let ⟨exitIdx, enterIdx⟩ ← try
      choosePivots
    catch | .infeasible => return
    doPivotOperation exitIdx enterIdx

/--
Runs Simplex Algorithm starting with `initTable`. It always terminates, finding solution if
such exists. Returns the table obtained at the last step.
-/
def runSimplexAlgo (initTable : Table) : Table := Id.run do
  return (← runSimplexAlgoImp.run ⟨initTable⟩).snd.table

end Linarith.SimplexAlgo
