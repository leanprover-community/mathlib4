/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Linarith.SimplexAlgorithm.Datatypes

/-!
# Gaussian Elimination algorithm

The first step of `Linarith.SimplexAlgorithm.findPositiveVector` is finding initial feasible
solution which is done by standard Gaussian Elimination algorithm implemented in this file.
-/

namespace Linarith.SimplexAlgorithm.Gauss

/-- The monad for the Gaussian Elimination algorithm. -/
abbrev GaussM (n m : Nat) := StateM <| Matrix n m

/-- Finds the first row starting from the current row with nonzero element in current column. -/
def findNonzeroRow (row col : Nat) {n m : Nat} : GaussM n m <| Option Nat := do
  for i in [row:n] do
    if (← get)[i]![col]! != 0 then
      return i
  return .none

/-- Swaps two rows. -/
def swapRows {n m : Nat} (i j : Nat) : GaussM n m Unit := do
  if i != j then
    modify fun mat =>
      let swapped : Matrix n m := ⟨mat.data.swap! i j⟩
      swapped

/-- Subtracts `i`-th row * `coef` from `j`-th row. -/
def subtractRow {n m : Nat} (i j : Nat) (coef : Rat) : GaussM n m Unit :=
  modify fun mat =>
    let newData : Array (Array Rat) := mat.data.modify j fun row =>
      row.zipWith mat[i]! fun x y => x - coef * y
    ⟨newData⟩

/-- Divides row by `coef`. -/
def divideRow {n m : Nat} (i : Nat) (coef : Rat) : GaussM n m Unit :=
  modify fun mat =>
    let newData : Array (Array Rat) := mat.data.modify i (·.map (· / coef))
    ⟨newData⟩

/-- Implementation of `getTable` in `GaussM` monad. -/
def getTableImp {n m : Nat} : GaussM n m Table := do
  let mut free : Array Nat := #[]
  let mut basic : Array Nat := #[]

  let mut row : Nat := 0
  let mut col : Nat := 0

  while row < n && col < m do
    match ← findNonzeroRow row col with
    | .none =>
      free := free.push col
      col := col + 1
      continue
    | .some rowToSwap =>
      swapRows row rowToSwap

    divideRow row (← get)[row]![col]!

    for i in [:n] do
      if i == row then
        continue
      let coef := (← get)[i]![col]!
      subtractRow row i coef

    basic := basic.push col
    row := row + 1
    col := col + 1

  for i in [col:m] do
    free := free.push i

  let ansData : Array (Array Rat) := ← do
    let mat := (← get)
    return Array.ofFn (fun row : Fin row => free.map fun f => -mat[row]![f]!)

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
  return (← getTableImp.run A).fst

end Linarith.SimplexAlgorithm.Gauss
