/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Lean
import Mathlib.Init.Data.Nat.Basic

/-!
## Definitions on Lists

This file contains various definitions on `List`. It does not contain
proofs about these definitions, those are contained in other files in `Mathlib.Data.List`.
-/

namespace List

/-- Given a function `f : ℕ → α → β` and `as : list α`, `as = [a₀, a₁, ...]`, returns the list
`[f 0 a₀, f 1 a₁, ...]`. -/
def mapIdx (as : List α) (f : ℕ → α → β) : List β :=
  let rec loop : ℕ → List α → List β
  | _,  [] => []
  | n, a :: as => f n a :: loop (n + 1) as
  loop 0 as

/-- Applicative variant of `mapWithIndex`. -/
def mapIdxM {m : Type v → Type w} [Applicative m] (as : List α) (f : ℕ → α → m β) :
  m (List β) :=
  let rec loop : ℕ → List α → m (List β)
  | _,  [] => []
  | n, a :: as => List.cons <$> f n a <*> loop (n + 1) as
  loop 0 as

/-- Drop `none`s from a list, and replace each remaining `some a` with `a`. -/
def reduceOption (l : List (Option α)) : List α :=
l.filterMap id

end List
