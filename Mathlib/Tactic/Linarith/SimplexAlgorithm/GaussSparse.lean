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

namespace Linarith.SimplexAlgorithm.GaussSparse

/-- The monad for the Gaussian Elimination algorithm. -/
abbrev GaussM (n m : Nat) := StateM <| SparseMatrix n m

/-- Finds the first row starting from the `row` with nonzero element in column `col`. -/
def findNonzeroRow (row col : Nat) {n m : Nat} : GaussM n m <| Option Nat := do
  for i in [row:n] do
    if (← get).data[i]!.contains col then
      return i
  return .none

/-- Swaps two rows. -/
def swapRows {n m : Nat} (i j : Nat) : GaussM n m Unit := do
  if i != j then
    modify fun mat =>
      let swapped : SparseMatrix n m := ⟨mat.data.swap! i j⟩
      swapped


-- delete me! for debug
local instance : ToString <| Lean.HashMap Nat Rat := {
  toString := fun hm : Lean.HashMap Nat Rat  => hm.fold (fun cur k v => cur ++ s!" ⟨{k}: {v}⟩ ") ""
}

/-- Subtracts `i`-th row * `coef` from `j`-th row. -/
def subtractRow {n m : Nat} (i j : Nat) (coef : Rat) : GaussM n m Unit := do
  if coef != 0 then
    modify fun mat =>
      let newData : Array (Lean.HashMap Nat Rat) := mat.data.modify j fun row =>
        mat.data[i]!.fold (fun cur k val =>
          -- dbg_trace s!"cur : {cur}; {cur.findD k 0}"
          let newVal := (cur.findD k 0) - coef * val
          -- dbg_trace s!"{k}: {val}; {newVal}"
          if newVal != 0 then cur.insert k newVal else cur.erase k
        ) row
      ⟨newData⟩

/-- Divides row by `coef`. -/
def divideRow {n m : Nat} (i : Nat) (coef : Rat) : GaussM n m Unit :=
  modify fun mat =>
    let newData : Array (Lean.HashMap Nat Rat) := mat.data.modify i fun row =>
      row.fold (fun cur k v => cur.insert k (v / coef)) row
    ⟨newData⟩

/-- Implementation of `getTable` in `GaussM` monad. -/
def getTableImp {n m : Nat} : GaussM n m Table := do
  let mut free : Array Nat := #[]
  let mut basic : Array Nat := #[]

  let mut row : Nat := 0
  let mut col : Nat := 0

  while row < n && col < m do
    -- dbg_trace s!"{row} {col}"
    -- dbg_trace (← get).data
    match ← findNonzeroRow row col with
    | .none =>
      free := free.push col
      col := col + 1
      continue
    | .some rowToSwap =>
      swapRows row rowToSwap

    divideRow row <| (← get).data[row]!.find! col

    for i in [:n] do
      if i == row then
        continue
      let coef := (← get).data[i]!.findD col 0
      -- dbg_trace s!"subtractRow {row} {i} {coef}"
      subtractRow row i coef

    basic := basic.push col
    row := row + 1
    col := col + 1

  for i in [col:m] do
    free := free.push i

  let ansData : Array (Array Rat) := ← do
    let mat := (← get)
    return Array.ofFn (fun row : Fin row => free.map fun f => -mat.data[row]!.findD f 0)

  -- dbg_trace s!"free : {free}; basic : {basic}"
  -- dbg_trace ansData
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
def getTable {n m : Nat} (A : SparseMatrix n m) : Table := Id.run do
  return (← getTableImp.run A).fst

end Linarith.SimplexAlgorithm.GaussSparse
