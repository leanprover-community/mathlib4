/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Init
import Std.Data.HashMap.Basic

/-!
# Datatypes for the Simplex Algorithm implementation
-/

namespace Mathlib.Tactic.Linarith.SimplexAlgorithm

/--
Specification for matrix types over ℚ which can be used in the Gauss Elimination and the Simplex
Algorithm. It was introduced to unify dense matrices and sparse matrices.
-/
class UsableInSimplexAlgorithm (α : Nat → Nat → Type) where
  /-- Returns `mat[i, j]`. -/
  getElem {n m : Nat} (mat : α n m) (i j : Nat) : Rat
  /-- Sets `mat[i, j]`. -/
  setElem {n m : Nat} (mat : α n m) (i j : Nat) (v : Rat) : α n m
  /-- Returns the list of elements of `mat` in the form `(i, j, mat[i, j])`. -/
  getValues {n m : Nat} (mat : α n m) : List (Nat × Nat × Rat)
  /-- Creates a matrix from a list of elements in the form `(i, j, mat[i, j])`. -/
  ofValues {n m : Nat} (values : List (Nat × Nat × Rat)) : α n m
  /-- Swaps two rows. -/
  swapRows {n m : Nat} (mat : α n m) (i j : Nat) : α n m
  /-- Subtracts `i`-th row multiplied by `coef` from `j`-th row. -/
  subtractRow {n m : Nat} (mat : α n m) (i j : Nat) (coef : Rat) : α n m
  /-- Divides the `i`-th row by `coef`. -/
  divideRow {n m : Nat} (mat : α n m) (i : Nat) (coef : Rat) : α n m

export UsableInSimplexAlgorithm (setElem getValues ofValues swapRows subtractRow divideRow)

instance (n m : Nat) (matType : Nat → Nat → Type) [UsableInSimplexAlgorithm matType] :
    GetElem (matType n m) (Nat × Nat) Rat fun _ p => p.1 < n ∧ p.2 < m where
  getElem mat p _ := UsableInSimplexAlgorithm.getElem mat p.1 p.2

/--
Structure for matrices over ℚ.

So far it is just a 2d-array carrying dimensions (that are supposed to match with the actual
dimensions of `data`), but the plan is to add some `Prop`-data and make the structure strict and
safe.

Note: we avoid using `Matrix` because it is far more efficient to store a matrix as its entries than
as function between `Fin`-s.
-/
structure DenseMatrix (n m : Nat) where
  /-- The content of the matrix. -/
  data : Array (Array Rat)

instance : UsableInSimplexAlgorithm DenseMatrix where
  getElem mat i j := mat.data[i]![j]!
  setElem mat i j v := ⟨mat.data.modify i fun row => row.set! j v⟩
  getValues mat :=
    mat.data.zipIdx.foldl (init := []) fun acc (row, i) =>
      let rowVals := Array.toList <| row.zipIdx.filterMap fun (v, j) =>
        if v != 0 then
          some (i, j, v)
        else
          none
      rowVals ++ acc
  ofValues {n m : Nat} vals : DenseMatrix _ _ := Id.run do
    let mut data : Array (Array Rat) := Array.replicate n <| Array.replicate m 0
    for ⟨i, j, v⟩ in vals do
      data := data.modify i fun row => row.set! j v
    return ⟨data⟩
  swapRows mat i j := ⟨mat.data.swapIfInBounds i j⟩
  subtractRow mat i j coef :=
    let newData : Array (Array Rat) := mat.data.modify j fun row =>
      Array.zipWith (fun x y => x - coef * y) row mat.data[i]!
    ⟨newData⟩
  divideRow mat i coef := ⟨mat.data.modify i (·.map (· / coef))⟩

/--
Structure for sparse matrices over ℚ, implemented as an array of hashmaps, containing only nonzero
values.
-/
structure SparseMatrix (n m : Nat) where
  /-- The content of the matrix. -/
  data : Array <| Std.HashMap Nat Rat

instance : UsableInSimplexAlgorithm SparseMatrix where
  getElem mat i j := mat.data[i]!.getD j 0
  setElem mat i j v :=
    if v == 0 then
      ⟨mat.data.modify i fun row => row.erase j⟩
    else
      ⟨mat.data.modify i fun row => row.insert j v⟩
  getValues mat :=
    mat.data.zipIdx.foldl (init := []) fun acc (row, i) =>
      let rowVals := row.toList.map fun (j, v) => (i, j, v)
      rowVals ++ acc
  ofValues {n _ : Nat} vals := Id.run do
    let mut data : Array (Std.HashMap Nat Rat) := Array.replicate n ∅
    for ⟨i, j, v⟩ in vals do
      if v != 0 then
        data := data.modify i fun row => row.insert j v
    return ⟨data⟩
  swapRows mat i j := ⟨mat.data.swapIfInBounds i j⟩
  subtractRow mat i j coef :=
    let newData := mat.data.modify j fun row =>
      mat.data[i]!.fold (fun cur k val =>
        let newVal := (cur.getD k 0) - coef * val
        if newVal != 0 then cur.insert k newVal else cur.erase k
      ) row
    ⟨newData⟩
  divideRow mat i coef :=
    let newData : Array (Std.HashMap Nat Rat) := mat.data.modify i fun row =>
      row.fold (fun cur k v => cur.insert k (v / coef)) row
    ⟨newData⟩

/--
`Tableau` is a structure the Simplex Algorithm operates on. The `i`-th row of `mat` expresses the
variable `basic[i]` as a linear combination of variables from `free`.
-/
structure Tableau (matType : Nat → Nat → Type) [UsableInSimplexAlgorithm matType] where
  /-- Array containing the basic variables' indexes -/
  basic : Array Nat
  /-- Array containing the free variables' indexes -/
  free : Array Nat
  /-- Matrix of coefficients the basic variables expressed through the free ones. -/
  mat : matType basic.size free.size

end Mathlib.Tactic.Linarith.SimplexAlgorithm
