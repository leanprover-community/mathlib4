/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename
import Mathlib.Init.Data.Nat.Notation
import Std.Data.Nat.Lemmas
import Std.Data.List.Basic
/-!
Definitions for `List` not (yet) in `Std`
-/


open Decidable List

universe u v w

namespace List



open Option Nat

/-- Optionally return nth element of a list. -/
@[simp]
def nth : List α → ℕ → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, n + 1 => nth l n
#align list.nth List.nth

/-- nth element of a list `l` given `n < l.length`. -/
def nthLe : ∀ (l : List α) (n), n < l.length → α
  | [], n, h => absurd h n.not_lt_zero
  | a :: _, 0, _ => a
  | _ :: l, n + 1, h => nthLe l n (le_of_succ_le_succ h)
#align list.nth_le List.nthLe

/-- Mapping a pair of lists under a curried function of two variables. -/
@[simp]
def map₂ (f : α → β → γ) : List α → List β → List γ
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => f x y :: map₂ f xs ys

/-- Auxiliary function for `mapWithIndex`. -/
def mapWithIndexCore (f : ℕ → α → β) : ℕ → List α → List β
  | _, [] => []
  | k, a :: as => f k a :: mapWithIndexCore f (k + 1) as
#align list.map_with_index_core List.mapWithIndexCore

/-- Given a function `f : ℕ → α → β` and `as : list α`, `as = [a₀, a₁, ...]`, returns the list
`[f 0 a₀, f 1 a₁, ...]`. -/
def mapWithIndex (f : ℕ → α → β) (as : List α) : List β :=
  mapWithIndexCore f 0 as
#align list.map_with_index List.mapWithIndex

/-- Find index of element with given property. -/
def findIndex (p : α → Prop) [DecidablePred p] : List α → ℕ
  | [] => 0
  | a :: l => if p a then 0 else succ (findIndex p l)
#align list.find_index List.findIndex

/-- Update the nth element of a list. -/
def updateNth : List α → ℕ → α → List α
  | _ :: xs, 0, a => a :: xs
  | x :: xs, i + 1, a => x :: updateNth xs i a
  | [], _, _ => []
#align list.update_nth List.updateNth

/-- Big or of a list of Booleans. -/
def bor (l : List Bool) : Bool :=
  any l id
#align list.bor List.bor

/-- Big and of a list of Booleans. -/
def band (l : List Bool) : Bool :=
  all l id
#align list.band List.band

/-- List consisting of an element `a` repeated a specified number of times. -/
@[simp]
def «repeat» (a : α) : Nat → List α
  | 0 => []
  | succ n => a :: «repeat» a n
#align list.repeat List.repeat

/-- The last element of a non-empty list. -/
def last : ∀ l : List α, l ≠ [] → α
  | [], h => absurd rfl h
  | [a], _ => a
  | _ :: b :: l, _ => last (b :: l) fun h => List.noConfusion h
#align list.last List.last

/-- The last element of a list, with the default if list empty -/
def ilast [Inhabited α] : List α → α
  | [] => default
  | [a] => a
  | [_, b] => b
  | _ :: _ :: l => ilast l
#align list.ilast List.ilast

/-- Initial segment of a list, i.e., with the last element dropped. -/
def init : List α → List α
  | [] => []
  | [_] => []
  | a :: l => a :: init l
#align list.init List.init

/-- List with a single given element. -/
@[inline]
protected def ret {α : Type u} (a : α) : List α :=
  [a]
#align list.ret List.ret

/-- `≤` implies not `>` for lists. -/
theorem le_eq_not_gt [LT α] : ∀ l₁ l₂ : List α, (l₁ ≤ l₂) = ¬l₂ < l₁ := fun _ _ => rfl
#align list.le_eq_not_gt List.le_eq_not_gt


end List
