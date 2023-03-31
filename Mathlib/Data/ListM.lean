/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Keeley Hoek, Simon Hudon, Scott Morrison

! This file was ported from Lean 3 source module data.mllist
! leanprover-community/mathlib commit 8f6fd1b69096c6a587f745d354306c0d46396915
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Option.Defs

/-! # Monadic lazy lists.

Lazy lists with "lazyness" controlled by an arbitrary monad.

The inductive construction is unsafe (indeed, we can build infinite objects).
This isn't so bad, as the typical use is with the tactic monad, in any case.
Typical usage will be to do computations in `ListM`, and then eventually extract
the first result (with `head` or `firstM`), first several results (using `take`),
or all results (using `force`). At this point you can use the `unsafe` term elaborator
from `Std.Util.TermUnsafe` to return to the "safe" world.

As we're unsafe anyway, we don't bother with proofs about these constructions.
-/

universe u v

/-- A monadic lazy list, controlled by an arbitrary monad. -/
unsafe inductive ListM (m : Type u → Type u) (α : Type u) : Type u
  | nil : ListM m α
  | cons : m (Option α × ListM m α) → ListM m α
#align tactic.mllist ListM

namespace ListM

variable {α β : Type u} {m : Type u → Type u}

/-- Construct a `ListM` recursively. -/
unsafe def fix [Alternative m] (f : α → m α) : α → ListM m α
| x => cons <| (fun a => (some x, fix f a)) <$> f x <|> pure (some x, nil)
#align tactic.mllist.fix ListM.fix

variable [Monad m]

/-- Repeatedly apply a function `f : α → m (α × List β)` to an initial `a : α`,
accumulating the elements of the resulting `list β` as a single monadic lazy list.

(This variant allows starting with a specified `List β` of elements, as well. )-/
unsafe def fixl_with [Alternative m] (f : α → m (α × List β)) : α → List β → ListM m β
  | s, b :: rest => cons <| pure (some b, fixl_with f s rest)
  | s, [] =>
  cons <|
    (do
      let (s', l) ← f s
      match l with
        | b :: rest => pure (some b, fixl_with f s' rest)
        | [] => pure (none, fixl_with f s' [])) <|>
      pure (none, nil)
#align tactic.mllist.fixl_with ListM.fixl_with

/-- Repeatedly apply a function `f : α → m (α × : List β)` to an initial `a : α`,
accumulating the elements of the resulting `List β` as a single monadic lazy list. -/
unsafe def fixl [Alternative m] (f : α → m (α × List β)) (s : α) : ListM m β :=
fixl_with f s []
#align tactic.mllist.fixl ListM.fixl

/-- Deconstruct a `ListM`, returning inside the monad an optional pair `α × ListM m α`
representing the head and tail of the list. -/
unsafe def uncons {α : Type u} : ListM m α → m (Option (α × ListM m α))
  | nil => pure none
  | cons l => do
    let (x, xs) ← l
    let some x ← pure x | uncons xs
    return (x, xs)
#align tactic.mllist.uncons ListM.uncons

/-- Compute, inside the monad, whether a `ListM` is empty. -/
unsafe def empty {α : Type u} (xs : ListM m α) : m (ULift Bool) :=
(ULift.up ∘ Option.isSome) <$> uncons xs
#align tactic.mllist.empty ListM.empty

/-- Convert a `List` to a `ListM`. -/
unsafe def ofList {α : Type u} : List α → ListM m α
  | [] => nil
  | h :: t => cons (pure (h, ofList t))
#align tactic.mllist.of_list ListM.ofList

/-- Convert a `List` of values inside the monad into a `ListM`. -/
unsafe def ofListM {α : Type u} : List (m α) → ListM m α
  | [] => nil
  | h :: t => cons ((fun x => (x, ofListM t)) <$> some <$> h)
#align tactic.mllist.m_of_list ListM.ofListM

/-- Extract a list inside the monad from a `ListM`. -/
unsafe def force {α} : ListM m α → m (List α)
  | nil => pure []
  | cons l => do
    let (x, xs) ← l
    let some x ← pure x |
      force xs
    (· :: ·) x <$> force xs
#align tactic.mllist.force ListM.force

/-- Take the first `n` elements, as a list inside the monad. -/
unsafe def take {α} : ListM m α → Nat → m (List α)
  | nil, _ => pure []
  | _, 0 => pure []
  | cons l, n + 1 => do
    let (x, xs) ← l
    let some x ← pure x |
      take xs (n + 1)
    (· :: ·) x <$> take xs n
#align tactic.mllist.take ListM.take

/-- Apply a function to every element of a `ListM`. -/
unsafe def map {α β : Type u} (f : α → β) : ListM m α → ListM m β
  | nil => nil
  | cons l =>
    cons do
      let (x, xs) ← l
      pure (f <$> x, map f xs)
#align tactic.mllist.map ListM.map

/-- Apply a function which returns values in the monad to every element of a `ListM`. -/
unsafe def mapM {α β : Type u} (f : α → m β) : ListM m α → ListM m β
  | nil => nil
  | cons l =>
    cons do
      let (x, xs) ← l
      let b ← x.traverse f
      return (b, mapM f xs)
#align tactic.mllist.mmap ListM.mapM

/-- Filter a `ListM`. -/
unsafe def filter {α : Type u} (p : α → Prop) [DecidablePred p] : ListM m α → ListM m α
  | nil => nil
  | cons l =>
    cons do
      let (a, r) ← l
      let some a ← pure a |
        return (none, filter p r)
      return (if p a then some a else none, filter p r)
#align tactic.mllist.filter ListM.filter

/-- Filter a `ListM` using a function which returns values in the (alternative) monad.
Whenever the function "succeeds", we accept the element, and reject otherwise. -/
unsafe def filterM [Alternative m] {α β : Type u} (p : α → m β) : ListM m α → ListM m α
  | nil => nil
  | cons l =>
    cons do
      let (a, r) ← l
      let some a ← pure a |
        return (none, filterM p r)
      (do _ ← p a; return (a, filterM p r)) <|> return (none, filterM p r)
#align tactic.mllist.mfilter ListM.filterM

/-- Filter and transform a `ListM` using an `Option` valued function. -/
unsafe def filterMap {α β : Type u} (f : α → Option β) : ListM m α → ListM m β
  | nil => nil
  | cons l =>
    cons do
      let (a, r) ← l
      let some a ← pure a |
        return (none, filterMap f r)
      match f a with
        | some b => return (some b, filterMap f r)
        | none => return (none, filterMap f r)
#align tactic.mllist.filter_map ListM.filterMap

/-- Filter and transform a `ListM` using a function that returns values inside the monad.
We discard elements where the function fails. -/
unsafe def filterMapM [Alternative m] {α β : Type u} (f : α → m β) : ListM m α → ListM m β
  | nil => nil
  | cons l =>
    cons do
      let (a, r) ← l
      let some a ← pure a |
        return (none, filterMapM f r)
      (f a >>= fun b => return (some b, filterMapM f r)) <|> return (none, filterMapM f r)
#align tactic.mllist.mfilter_map ListM.filterMapM

/-- Concatenate two monadic lazy lists. -/
unsafe def append {α : Type u} : ListM m α → ListM m α → ListM m α
  | nil, ys => ys
  | cons xs, ys =>
    cons do
      let (x, xs) ← xs
      return (x, append xs ys)
#align tactic.mllist.append ListM.append

/-- Join a monadic lazy list of monadic lazy lists into a single monadic lazy list. -/
unsafe def join {α : Type u} : ListM m (ListM m α) → ListM m α
  | nil => nil
  | cons l =>
    cons do
      let (xs, r) ← l
      let some xs ← pure xs |
        return (none, join r)
      match xs with
        | nil => return (none, join r)
        | cons m => do
          let (a, n) ← m
          return (a, join (cons <| return (n, r)))
#align tactic.mllist.join ListM.join

/-- Lift a monadic lazy list inside the monad to a monadic lazy list. -/
unsafe def squash {α} (t : m (ListM m α)) : ListM m α :=
(ListM.ofListM [t]).join
#align tactic.mllist.squash ListM.squash

/-- Enumerate the elements of a monadic lazy list, starting at a specified offset. -/
unsafe def enum_from {α : Type u} : Nat → ListM m α → ListM m (Nat × α)
  | _, nil => nil
  | n, cons l =>
    cons do
      let (a, r) ← l
      let some a ← pure a |
        return (none, enum_from n r)
      return ((n, a), enum_from (n + 1) r)
#align tactic.mllist.enum_from ListM.enum_from

/-- Enumerate the elements of a monadic lazy list. -/
unsafe def enum {α : Type u} : ListM m α → ListM m (Nat × α) :=
enum_from 0
#align tactic.mllist.enum ListM.enum

/-- The infinite monadic lazy list of natural numbers.-/
unsafe def range {m : Type → Type} [Alternative m] : ListM m Nat :=
ListM.fix (fun n => pure (n + 1)) 0
#align tactic.mllist.range ListM.range

/-- Add one element to the end of a monadic lazy list. -/
unsafe def concat {α : Type u} : ListM m α → α → ListM m α
  | L, a => (ListM.ofList [L, ListM.ofList [a]]).join
#align tactic.mllist.concat ListM.concat

/-- Apply a function returning a monadic lazy list to each element of a monadic lazy list,
joining the results. -/
unsafe def bind {α β : Type u} : ListM m α → (α → ListM m β) → ListM m β
  | nil, _ => nil
  | cons ll, f =>
    cons do
      let (x, xs) ← ll
      let some x ← pure x |
        return (none, bind xs f)
      return (none, append (f x) (bind xs f))
#align tactic.mllist.bind_ ListM.bind

/-- Convert any value in the monad to the singleton monadic lazy list. -/
unsafe def monad_lift {α} (x : m α) : ListM m α :=
cons <| (flip Prod.mk nil ∘ some) <$> x
#align tactic.mllist.monad_lift ListM.monad_lift

/-- Return the head of a monadic lazy list, as a value in the monad. -/
unsafe def head [Alternative m] {α} (L : ListM m α) : m α := do
  let some (r, _) ← L.uncons |
    failure
  return r
#align tactic.mllist.head ListM.head

/-- Apply a function returning values inside the monad to a monadic lazy list,
returning only the first successful result. -/
unsafe def firstM [Alternative m] {α β} (L : ListM m α) (f : α → m β) : m β :=
(L.filterMapM f).head
#align tactic.mllist.mfirst ListM.firstM

end ListM
