import Mathlib.Tactic.Linarith.SimplexAlgo.Gauss

open Linarith.SimplexAlgo.Gauss

namespace Linarith.SimplexAlgo

structure SimplexAlgoState where
  table : Table
  status : String

abbrev SimplexAlgoM := StateM SimplexAlgoState

def SimplexAlgoM.run' {α : Type} (x : SimplexAlgoM α) (table : Table) : α := Id.run do
  pure (← x.run (⟨table, "Running"⟩ : SimplexAlgoState)).fst

def doPivotOperation (bvarIdx fvarIdx : Nat) : SimplexAlgoM Unit := do
  let mut newCurRow := (← get).table.mat.data[bvarIdx]!
  newCurRow := newCurRow.set! fvarIdx (-1)
  let intersectCoef := (← get).table.mat.data[bvarIdx]![fvarIdx]!
  newCurRow := newCurRow.map (fun x => -x / intersectCoef)

  let mut newData : Array (Array Rat) := #[]
  for i in [:(← get).table.bound.size] do
    if i == bvarIdx then
      newData := newData.push newCurRow
      continue
    let mut newRow : Array Rat := #[]
    for j in [:(← get).table.free.size] do
      if j == fvarIdx then
        newRow := newRow.push <| (← get).table.mat.data[i]![fvarIdx]! / intersectCoef
        continue
      newRow := newRow.push <|
        (← get).table.mat.data[i]![j]!
        - (← get).table.mat.data[i]![fvarIdx]! * (← get).table.mat.data[bvarIdx]![j]! / intersectCoef
    newData := newData.push newRow

  let newBound := (← get).table.bound.set! bvarIdx (← get).table.free[fvarIdx]!
  let newFree := (← get).table.free.set! fvarIdx (← get).table.bound[bvarIdx]!

  let newMat : Matrix newBound.size newFree.size := ⟨newData⟩
  set ({← get with table := ⟨newBound, newFree, newMat⟩} : SimplexAlgoState)

/- check if we found solution -/
def checkSuccess : SimplexAlgoM Bool := do
  if (← get).table.mat.data[0]!.back <= 0 then
    return false
  for row in (← get).table.mat.data do
    if row.back < 0 then
      return false
  return true

def getPivots : SimplexAlgoM (Nat × Nat) := do
  let mut fvarIdxOpt : Option Nat := .none
  -- let mut maxCoef := (← get).table.mat.data[0]![0]!
  for i in [:(← get).table.mat.data[0]!.size - 1] do
    -- let elem := (← get).table.mat.data[0]![i]!
    -- if (← get).table.mat.data[0]![i]! > maxCoef then
    --   maxCoef := elem
    --   fvarIdx := i
    if (← get).table.mat.data[0]![i]! > 0 then
      fvarIdxOpt := i
      break

  if fvarIdxOpt.isNone then
    set {← get with status := "Unfeasible"}
    return ⟨0, 0⟩
  let fvarIdx := fvarIdxOpt.get!

  let mut bvarIdxOpt : Option Nat := .none
  let mut minCoef := 0
  for i in [1:(← get).table.mat.data.size] do
    if (← get).table.mat.data[i]![fvarIdx]! >= 0 then
      continue
    let coef := -(← get).table.mat.data[i]!.back / (← get).table.mat.data[i]![fvarIdx]!
    if bvarIdxOpt.isNone || coef < minCoef then
      minCoef := coef
      bvarIdxOpt := i
  let bvarIdx := bvarIdxOpt.get!

  return ⟨bvarIdx, fvarIdx⟩

def simplexAlgo : SimplexAlgoM Table := do
  while true do
    -- dbg_trace ""
    -- dbg_trace (← get).table.mat.data
    -- dbg_trace (← get).table.bound
    -- dbg_trace (← get).table.free
    if ← checkSuccess then
      set {← get with status := "Finished"}
      return (← get).table
    let ⟨bvarIdx, fvarIdx⟩ := ← getPivots
    -- dbg_trace bvarIdx
    -- dbg_trace fvarIdx
    if (← get).status == "Unfeasible" then
      return (← get).table
    doPivotOperation bvarIdx fvarIdx
  return (← get).table

end Linarith.SimplexAlgo
