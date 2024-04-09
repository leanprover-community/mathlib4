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
Given indexes `bvarIdx` and `fvarIdx` of exiting and entering variables in `bound` and `free`
arrays, performs pivot operation, i.e. expresses one through the other and makes the free one basic
and vice versa.
-/
def doPivotOperation (bvarIdx fvarIdx : Nat) : SimplexAlgoM Unit := do
  let mut newCurRow := (← get).table.mat[bvarIdx]!
  newCurRow := newCurRow.set! fvarIdx (-1)
  let intersectCoef := (← get).table.mat[bvarIdx]![fvarIdx]!
  newCurRow := newCurRow.map (- · / intersectCoef)

  let mut newData : Array (Array Rat) := #[]
  for i in [:(← get).table.basic.size] do
    if i == bvarIdx then
      newData := newData.push newCurRow
      continue
    let mut newRow : Array Rat := #[]
    for j in [:(← get).table.free.size] do
      if j == fvarIdx then
        newRow := newRow.push <| (← get).table.mat[i]![fvarIdx]! / intersectCoef
        continue
      newRow := newRow.push <|
        (← get).table.mat[i]![j]!
        - (← get).table.mat[i]![fvarIdx]! * (← get).table.mat[bvarIdx]![j]! / intersectCoef
    newData := newData.push newRow

  let newBasic := (← get).table.basic.set! bvarIdx (← get).table.free[fvarIdx]!
  let newFree := (← get).table.free.set! fvarIdx (← get).table.basic[bvarIdx]!

  let newMat : Matrix newBasic.size newFree.size := ⟨newData⟩
  set ({← get with table := ⟨newBasic, newFree, newMat⟩} : SimplexAlgoState)

/-- Check if the solution is found. -/
def checkSuccess : SimplexAlgoM Bool := do
  if (← get).table.mat[0]!.back <= 0 then
    return false
  for row in (← get).table.mat.data do
    if row.back < 0 then
      return false
  return true

/--
Chooses entering and exiting variables using Bland's rule that guarantees that the Simplex
Algorithm terminates.
-/
def choosePivots : SimplexAlgoM (Nat × Nat) := do
  /- Entering variable: choose among the variables with a positive coefficient in the objective
  function, the one with the smallest index (in the initial indexing). -/
  let mut fvarIdxOpt : Option Nat := .none
  let mut minIdx := 0
  for i in [:(← get).table.mat[0]!.size - 1] do
    if (← get).table.mat[0]![i]! > 0 && (fvarIdxOpt.isNone || (← get).table.free[i]! < minIdx) then
      fvarIdxOpt := i
      minIdx := (← get).table.free[i]!

  /- If there is no such variable the solution does not exist for sure. -/
  match fvarIdxOpt with
  | .none =>
    throw SimplexAlgoException.infeasible
    return ⟨0, 0⟩
  | .some fvarIdx =>

  /- Exiting variable: choose the variable imposing the strictest limit on the increase of the
  entering variable, breaking ties by choosing the variable with smallest index. -/
  let mut bvarIdxOpt : Option Nat := .none
  let mut minCoef := 0
  minIdx := 0
  for i in [1:(← get).table.mat.data.size] do
    if (← get).table.mat[i]![fvarIdx]! >= 0 then
      continue
    let coef := -(← get).table.mat[i]!.back / (← get).table.mat[i]![fvarIdx]!
    if bvarIdxOpt.isNone || coef < minCoef ||
        (coef == minCoef && (← get).table.basic[i]! < minIdx) then
      bvarIdxOpt := i
      minCoef := coef
      minIdx := (← get).table.basic[i]!
  let bvarIdx := bvarIdxOpt.get!

  return ⟨bvarIdx, fvarIdx⟩

/-- Implementation of `runSimplexAlgo` in `SimplexAlgoM` monad. -/
def runSimplexAlgoImp : SimplexAlgoM Unit := do
  while True do
    if ← checkSuccess then
      return
    let ⟨bvarIdx, fvarIdx⟩ ← try
      choosePivots
    catch | .infeasible => return
    doPivotOperation bvarIdx fvarIdx
  return

/--
Runs Simplex Algorithm strarting with `initTable`. It always terminates, finding solution if
such exists. Returns the table obtained at the last step.
-/
def runSimplexAlgo (initTable : Table) : Table := Id.run do
  return (← runSimplexAlgoImp.run ⟨initTable⟩).snd.table

end Linarith.SimplexAlgo
