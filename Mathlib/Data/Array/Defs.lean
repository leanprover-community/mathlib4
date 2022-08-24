/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Floris van Doorn
-/

/-!
## Definitions on Arrays

This file contains various definitions on `Array`. It does not contain
proofs about these definitions, those are contained in other files in `Mathlib.Data.Array`.
-/

namespace Array

/-- The array `#[f 0, ..., f n]` -/
def ofFn (n : Nat) (f : Fin n → α) : Array α :=
  loop 0 (mkEmpty n)
where
  /-- Implementation detail of `Array.ofFn`. -/
  loop (i : Nat) (acc : Array α) : Array α :=
    if h : i < n then
      let acc := acc.push (f ⟨i, h⟩)
      loop (i + 1) acc
    else
      acc
termination_by
  loop i acc => n - i

/-- The array `#[0, 1, ..., n - 1]`. -/
def range (n : Nat) : Array Nat :=
  n.fold (flip Array.push) #[]

/-- Drop `none`s from a Array, and replace each remaining `some a` with `a`. -/
def reduceOption (l : Array (Option α)) : Array α :=
  l.filterMap id

/-- Turns `#[#[a₁, a₂, ⋯], #[b₁, b₂, ⋯], ⋯]` into `#[a₁, a₂, ⋯, b₁, b₂, ⋯]` -/
def flatten (arr : Array (Array α)) : Array α :=
  arr.foldl (init := #[]) fun acc a => acc.append a

end Array
