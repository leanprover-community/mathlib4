/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public meta import Mathlib.Data.Rat.Init

/-!
# Reduction of a matrix over ℚ to Hessenberg form

`reduce` computes, for a square matrix `A` over `ℚ`, a sequence of row and column swaps, a unit
lower triangular matrix `L` and an upper Hessenberg matrix `H` such that `Aσ * L = L * H`, where
`Aσ := A.submatrix σ σ` is `A` with its rows and columns permuted by the swaps.

## Implementation notes

`reduce` follows steps 1 to 4 of [Cohen][cohen1993], Algorithm 2.2.9.

## References

* [H. Cohen, *A Course in Computational Algebraic Number Theory*][cohen1993], Algorithm 2.2.9
-/

public meta section

namespace Mathlib.Tactic.Hessenberg

/-- A similarity `Aσ * L = L * H` of a rational matrix `A` to upper Hessenberg form, where
`Aσ := A.submatrix σ σ` for the arrangement `σ` of the interchanges. -/
structure Reduction where
  /-- The row and column interchanges, in order. The permutation `σ` is their product. -/
  swaps : Array (ℕ × ℕ)
  /-- The unit lower triangular transform. -/
  L : Array (Array Rat)
  /-- The upper Hessenberg form. -/
  H : Array (Array Rat)

/-- The row and column swaps of a `Reduction` represented as an indexed array. An entry `e` at index
`i` means that row and column `e` of the original matrix move to position `i`. -/
def Reduction.perm (d : Reduction) : Array ℕ :=
  d.swaps.foldl (fun ord (a, b) => ord.swapIfInBounds a b) (Array.range d.L.size)

/-- Reduce the `n × n` matrix `A` over `ℚ`, given as an array of rows, to upper Hessenberg form by
Gaussian elimination with row and column swaps. -/
def reduce (n : ℕ) (A : Array (Array Rat)) : Reduction := Id.run do
  let getEntry (M : Array (Array Rat)) (i j : ℕ) : Rat := (M.getD i #[]).getD j 0
  let mut H := A
  let mut L : Array (Array Rat) :=
    Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j => if i == j then 1 else 0
  let mut swaps : Array (ℕ × ℕ) := #[]
  for m in 1...(n - 1) do
    let mut p? : Option ℕ := none
    for q in m...n do
      if getEntry H q (m - 1) != 0 then
        p? := some q
        break
    if let some p := p? then
      if p ≠ m then
        H := (H.swapIfInBounds m p).map (·.swapIfInBounds m p)
        L := L.swapIfInBounds m p
        L := (L.modify m (·.swapIfInBounds m p)).modify p (·.swapIfInBounds m p)
        swaps := swaps.push (m, p)
      let t := getEntry H m (m - 1)
      for i in m<...n do
        if getEntry H i (m - 1) != 0 then
          let u := getEntry H i (m - 1) / t
          H := H.set! i (Array.zipWith (fun a b => a - u * b) (H.getD i #[]) (H.getD m #[]))
          H := H.map fun row => row.set! m (row.getD m 0 + u * row.getD i 0)
          L := L.modify i (·.set! m u)
  return { swaps, L, H }

end Mathlib.Tactic.Hessenberg

end
