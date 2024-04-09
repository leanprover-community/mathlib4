/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Linarith.SimplexAlgo.Datatypes

/-!
# Gaussian Elimination algorithm

The first step of `Linarith.SimplexAlgo.findPositiveVector` is finding initial feasible solution
that is done by standard Gaussian Elimination algorithm implemented in this file.
-/

namespace Linarith.SimplexAlgo.Gauss

/-- The mutable state for the `GaussM` monad. -/
structure GaussState (n m : Nat) where
  /-- Current matrix. -/
  mat : Matrix n m
  /-- Positions of units corresponding to basic variables in the `mat`. Used to obtain `Table` from
  the processed matrix. -/
  basicPositions : Array (Nat × Nat)
  /-- Current row. -/
  currentRow : Nat
  /-- Current column. -/
  currentColumn : Nat

/-- The monad for the Gaussian Elimination algorithm. -/
abbrev GaussM (n m : Nat) := StateM <| GaussState n m

/-- Gets current row. -/
def curRow {n m : Nat} : GaussM n m Nat := do
  return (← get).currentRow

/-- Gets current column. -/
def curCol {n m : Nat} : GaussM n m Nat := do
  return (← get).currentColumn

/-- Increments current row. -/
def incRow {n m : Nat} : GaussM n m Unit :=
  modify fun s => {s with currentRow := s.currentRow + 1}

/-- Increments current column. -/
def incCol {n m : Nat} : GaussM n m Unit :=
  modify fun s => {s with currentColumn := s.currentColumn + 1}

/-- Pushes position to `basicPositions`. -/
def pushToBasicPos {n m : Nat} (i j : Nat) : GaussM n m Unit :=
  modify fun s => {s with basicPositions := s.basicPositions.push ⟨i, j⟩}

/-- Finds the first row starting from the current column with nonzero element in current column. -/
def findNonzeroRow {n m : Nat} : GaussM n m <| Option Nat := do
  for i in [← curRow:n] do
    if (← get).mat[i]![← curCol]! != 0 then
      return i
  return .none

/-- Swaps two rows. -/
def swapRows {n m : Nat} (i j : Nat) : GaussM n m Unit := do
  if i == j then
    return
  modify fun s =>
    let swapped : Matrix n m := ⟨s.mat.data.swap! i j⟩
    {s with mat := swapped}

/-- Subtracts `i`-th row * `coef` from `j`-th row. -/
def subtractRow {n m : Nat} (i j : Nat) (coef : Rat) : GaussM n m Unit :=
  modify fun s =>
    let new_row := s.mat[j]!.zip s.mat[i]! |>.map fun ⟨x, y⟩ => x - coef * y
    let subtractedMat : Matrix n m := ⟨s.mat.data.set! j new_row⟩
    {s with mat := subtractedMat}

/-- Divides row by `coef`. -/
def divideRow {n m : Nat} (i : Nat) (coef : Rat) : GaussM n m Unit :=
  modify fun s =>
    let new_row : Array Rat := s.mat[i]!.map (· / coef)
    let subtractedMat : Matrix n m := ⟨s.mat.data.set! i new_row⟩
    {s with mat := subtractedMat}

/-- Implementation of `getTable` in `GaussM` monad. -/
def getTableImp {n m : Nat} : GaussM n m Table := do
  let mut free : Array Nat := #[]
  let mut basic : Array Nat := #[]

  while (← curRow) < n && (← curCol) < m do
    match ← findNonzeroRow with
    | .none =>
      free := free.push (← curCol)
      incCol
      continue
    | .some rowToSwap =>
      swapRows (← curRow) rowToSwap

    divideRow (← curRow) (← get).mat[← curRow]![← curCol]!

    for i in [:n] do
      if i == (← curRow) then
        continue
      let coef := (← get).mat[i]![← curCol]!
      subtractRow (← curRow) i coef

    pushToBasicPos (← curRow) (← curCol)
    basic := basic.push (← curCol)
    incRow
    incCol

  for i in [← curCol:m] do
    free := free.push i

  let mut ansData : Array (Array Rat) := #[]
  for ⟨row, _⟩ in (← get).basicPositions do
    let mut newRow := #[]
    for f in free do
      newRow := newRow.push <| -(← get).mat[row]![f]!
    ansData := ansData.push newRow

  return {
    free := free
    basic := basic
    mat := ⟨ansData⟩
  }

/--
Given matrix `A`, solves the linear equation `A x = 0` and returns the solution as a table where
some variables are free and others (basic) variable are expressed as linear combinations of the free
ones.
-/
def getTable {n m : Nat} (A : Matrix n m) : Table := Id.run do
  let s : GaussState n m := {
    mat := A
    basicPositions := #[]
    currentRow := 0
    currentColumn := 0
  }
  return (← getTableImp.run s).fst

end Linarith.SimplexAlgo.Gauss
