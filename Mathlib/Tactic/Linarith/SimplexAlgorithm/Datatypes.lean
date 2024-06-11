/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Batteries.Data.Rat.Basic

/-!
# Datatypes for the Simplex Algorithm implementation
-/

namespace Linarith.SimplexAlgorithm

/--
Specification for matrix types over ℚ which can be used in the Gauss Elimination and the Simplex
Algorithm. It was introduced to unify dense matrices and sparse matrices.
-/
class UsableInSimplexAlgorithm (α : Nat → Nat → Type) where
  /-- Returns `mat[i, j]`. -/
  getElem {n m : Nat} (mat : α n m) (i j : Nat) : Rat
  /-- Sets `mat[i, j]`. -/
  setElem {n m : Nat}  (mat : α n m) (i j : Nat) (v : Rat) : α n m
  /-- Creates a matrix from the list of elements of the form `(i, j, mat[i, j])`. -/
  ofValues {n m : Nat} (values : List (Nat × Nat × Rat)) : α n m
  /-- Swaps two rows. -/
  swapRows {n m : Nat} (mat : α n m) (i j : Nat) : α n m
  /-- Subtracts `i`-th row * `coef` from `j`-th row. -/
  subtractRow {n m : Nat} (mat : α n m) (i j : Nat) (coef : Rat) : α n m
  /-- Divides `i`-th row by `coef`. -/
  divideRow {n m : Nat} (mat : α n m) (i : Nat) (coef : Rat) : α n m

export UsableInSimplexAlgorithm (setElem ofValues swapRows subtractRow divideRow)

instance (n m : Nat) (matType : Nat → Nat → Type) [UsableInSimplexAlgorithm matType] :
    GetElem (matType n m) (Nat × Nat) Rat fun _ p => p.1 < n ∧ p.2 < m where
  getElem mat p _ := UsableInSimplexAlgorithm.getElem mat p.1 p.2

/--
Structure for matrices over ℚ.

So far it is just a 2d-array carrying dimensions (that are supposed to match with the actual
dimensions of `data`), but the plan is to add some `Prop`-data and make the structure strict and
safe.

Note: we avoid using the `Matrix` from `Mathlib.Data.Matrix` because it is far more efficient to
store matrix as its entries than as function between `Fin`-s.
-/
structure Matrix (n m : Nat) where
  /-- The content of the matrix. -/
  data : Array (Array Rat)

instance : UsableInSimplexAlgorithm Matrix where
  getElem mat i j := mat.data[i]![j]!
  setElem mat i j v := ⟨mat.data.set! i <| mat.data[i]!.set! j v⟩
  ofValues {n m : Nat} vals : Matrix _ _ := Id.run do
    let mut data : Array (Array Rat) := Array.mkArray n <| Array.mkArray m 0
    for ⟨i, j, v⟩ in vals do
      data := data.set! i <| data[i]!.set! j v
    return ⟨data⟩
  swapRows mat i j := ⟨mat.data.swap! i j⟩
  subtractRow mat i j coef :=
    let newData : Array (Array Rat) := mat.data.modify j fun row =>
      row.zipWith mat.data[i]! fun x y => x - coef * y
    ⟨newData⟩
  divideRow mat i coef := ⟨mat.data.modify i (·.map (· / coef))⟩

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

end Linarith.SimplexAlgorithm
