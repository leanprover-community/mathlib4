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
abbrev GaussM (n m : Nat) (matType : Nat → Nat → Type) := StateM <| matType n m

variable {n m : Nat} {matType : Nat → Nat → Type} [IsMatrix matType]

/-- Finds the first row starting from the current row with nonzero element in current column. -/
def findNonzeroRow (row col : Nat) : GaussM n m matType <| Option Nat := do
  for i in [row:n] do
    if (← get)[(i, col)]! != 0 then
      return i
  return .none

/-- Implementation of `getTable` in `GaussM` monad. -/
def getTableImp : GaussM n m matType <| Table matType := do
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
      modify fun mat => swapRows mat row rowToSwap

    modify fun mat => divideRow mat row mat[(row, col)]!

    for i in [:n] do
      if i == row then
        continue
      let coef := (← get)[(i, col)]!
      modify fun mat => subtractRow mat row i coef

    basic := basic.push col
    row := row + 1
    col := col + 1

  for i in [col:m] do
    free := free.push i

  let ansMatrix : matType basic.size free.size := ← do
    let mat := (← get)
    let arr : Array (Array (Nat × Nat × Rat)) := Array.ofFn fun bIdx : Fin row =>
      free.mapIdx fun fIdx f =>
        ((bIdx : Nat), (fIdx : Nat), -mat[((bIdx : Nat), f)]!)
    return ofValues arr.flatten.toList

  return ⟨basic, free, ansMatrix⟩

/--
Given matrix `A`, solves the linear equation `A x = 0` and returns the solution as a table where
some variables are free and others (basic) variable are expressed as linear combinations of the free
ones.
-/
def getTable (A : matType n m) : Table matType := Id.run do
  return (← getTableImp.run A).fst

end Linarith.SimplexAlgorithm.Gauss
