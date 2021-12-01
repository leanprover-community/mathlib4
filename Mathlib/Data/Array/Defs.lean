/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Lean
import Mathlib.Init.Data.Nat.Basic

/-!
## Definitions on Arrays

This file contains various definitions on `Array`. It does not contain
proofs about these definitions, those are contained in other files in `Mathlib.Data.Array`.
-/

variable {α β : Type _}

namespace Array

/-- The array `#[0, 1, ..., n - 1]`. -/
def range (n : Nat) : Array ℕ :=
(List.range n).toArray

/-- Given a function `f : ℕ → α → β` and `as : Array α`, `as = #[a₀, a₁, ...]`, returns the Array
`#[f 0 a₀, f 1 a₁, ...]`. -/
def mapWithIndex (f : ℕ → α → β) (as : Array α) : Array β :=
(as.zip $ range as.size).map λ p => f p.2 p.1

/-- Monad variant of `mapWithIndex` (this could be generalized to `Applicative`). -/
def mapWithIndexM {m : Type v → Type w} [Monad m] (f : ℕ → α → m β) (as : Array α) :
  m (Array β) :=
(as.zip $ range as.size).mapM λ p => f p.2 p.1

/-- Drop `none`s from a Array, and replace each remaining `some a` with `a`. -/
def reduceOption (l : Array (Option α)) : Array α :=
l.filterMap id

end Array
