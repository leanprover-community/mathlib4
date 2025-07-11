/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.Datatypes

/-!
# Gaussian Elimination algorithm

The first step of `Linarith.SimplexAlgorithm.findPositiveVector` is finding initial feasible
solution which is done by standard Gaussian Elimination algorithm implemented in this file.
-/

namespace Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss

/-- The monad for the Gaussian Elimination algorithm. -/
abbrev GaussM (n m : Nat) (matType : Nat → Nat → Type) := StateT (matType n m) Lean.CoreM

variable {n m : Nat} {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]

/-- Finds the first row starting from the `rowStart` with nonzero element in the column `col`. -/
def findNonzeroRow (rowStart col : Nat) : GaussM n m matType <| Option Nat := do
  for i in [rowStart:n] do
    if (← get)[(i, col)]! != 0 then
      return i
  return .none

/-- Implementation of `getTableau` in `GaussM` monad. -/
def getTableauImp : GaussM n m matType <| Tableau matType := do
  let mut free : Array Nat := #[]
  let mut basic : Array Nat := #[]

  let mut row : Nat := 0
  let mut col : Nat := 0

  while row < n && col < m do
    Lean.Core.checkSystem decl_name%.toString
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
      if coef != 0 then
        modify fun mat => subtractRow mat row i coef

    basic := basic.push col
    row := row + 1
    col := col + 1

  for i in [col:m] do
    free := free.push i

  let ansMatrix : matType basic.size free.size := ← do
    let vals := getValues (← get) |>.filterMap fun (i, j, v) =>
      if j == basic[i]! then
        .none
      else
        .some (i, free.findIdx? (· == j) |>.get!, -v)
    return ofValues vals

  return ⟨basic, free, ansMatrix⟩

/--
Given matrix `A`, solves the linear equation `A x = 0` and returns the solution as a tableau where
some variables are free and others (basic) variable are expressed as linear combinations of the free
ones.
-/
def getTableau (A : matType n m) : Lean.CoreM (Tableau matType) := do
  return (← getTableauImp.run A).fst

end Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss
