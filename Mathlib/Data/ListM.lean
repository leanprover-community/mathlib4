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

unsafe instance : EmptyCollection (ListM m α) := ⟨nil⟩

/-- The implementation of `ForIn`, which enables `for a in L do ...` notation. -/
@[specialize] protected unsafe def forIn [Monad m] [Monad n] [MonadLiftT m n]
    (as : ListM m α) (init : δ) (f : α → δ → n (ForInStep δ)) : n δ :=
  match as with
  | nil => pure init
  | cons l => do match ← l with
    | (none, t) => t.forIn init f
    | (some a, t) => match (← f a init) with
      | ForInStep.done d  => pure d
      | ForInStep.yield d => t.forIn d f

unsafe instance [Monad m] [MonadLiftT m n] : ForIn n (ListM m α) α where
  forIn := ListM.forIn

/-- Construct a `ListM` recursively. -/
unsafe def fix [Alternative m] (f : α → m α) : α → ListM m α
  | x => cons <| (fun a => (some x, fix f a)) <$> f x <|> pure (some x, nil)
#align tactic.mllist.fix ListM.fix

variable [Monad m]

/-- Construct a `ListM` by iteration. (`m` must be a stateful monad for this to be useful.) -/
unsafe def iterate (f : m α) : ListM m α :=
  cons do pure (← f, iterate f)

/-- Repeatedly apply a function `f : α → m (α × List β)` to an initial `a : α`,
accumulating the elements of the resulting `List β` as a single monadic lazy list.

(This variant allows starting with a specified `List β` of elements, as well. )-/
unsafe def fixl_with [Alternative m] (f : α → m (α × List β)) : α → List β → ListM m β
  | s, b :: rest => cons <| pure (some b, fixl_with f s rest)
  | s, [] => cons <| (do
    let (s', l) ← f s
    match l with
      | b :: rest => pure (some b, fixl_with f s' rest)
      | [] => pure (none, fixl_with f s' [])) <|>
    pure (none, nil)
#align tactic.mllist.fixl_with ListM.fixl_with

/-- Repeatedly apply a function `f : α → m (α × List β)` to an initial `a : α`,
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
unsafe def isEmpty {α : Type u} (xs : ListM m α) : m (ULift Bool) :=
  (ULift.up ∘ Option.isSome) <$> uncons xs
#align tactic.mllist.empty ListM.isEmpty

/-- Convert a `List` to a `ListM`. -/
unsafe def ofList {α : Type u} : List α → ListM m α
  | [] => nil
  | h :: t => cons (pure (h, ofList t))
#align tactic.mllist.of_list ListM.ofList

/-- The empty `ListM`. -/
unsafe def empty {α : Type u} : ListM m α := ofList []

/-- Convert a `list` of values inside the monad into a `ListM`. -/
unsafe def ofListM {α : Type u} : List (m α) → ListM m α
  | [] => nil
  | h :: t => cons ((fun x => (x, ofListM t)) <$> some <$> h)
#align tactic.mllist.m_of_list ListM.ofListM

/-- Extract a list inside the monad from a `ListM`. -/
unsafe def force {α} (L : ListM m α) : m (List α) := do
  match ← uncons L with
  | none => pure []
  | some (x, xs) => (x :: ·) <$> force xs
#align tactic.mllist.force ListM.force

/-- Gives the monadic lazy list consisting all of folds of a function on a given initial element.
Thus `[a₀, a₁, ...].foldsM f b` will give `[b, ← f b a₀, ← f (← f b a₀) a₁, ...]`. -/
unsafe def foldsM (f : β → α → m β) (init : β) (L : ListM m α) : ListM m β :=
  cons do match ← uncons L with
  | none => return (some init, empty)
  | some (x, xs) => do
    let b ← f init x
    return (some init, foldsM f b xs)

/-- Gives the monadic lazy list consisting all of folds of a function on a given initial element.
Thus `[a₀, a₁, ...].foldsM f b` will give `[b, f b a₀, f (f b a₀) a₁, ...]`. -/
unsafe def folds (f : β → α → β) (init : β) (L : ListM m α) : ListM m β :=
  L.foldsM (fun b a => pure (f b a)) init

/-- Take the first `n` elements, as a list inside the monad. -/
unsafe def takeAsList {α} : ListM m α → Nat → m (List α)
  | _,  0 => pure []
  | xs, n+1 => do
    match ← uncons xs with
    | some (x, xs) => (x :: ·) <$> takeAsList xs n
    | none => pure []
#align tactic.mllist.take ListM.takeAsList

/-- Take the first `n` elements. -/
unsafe def take : ListM m α → Nat → ListM m α
  | _,  0    => empty
  | xs, n+1 => cons do
    match ← uncons xs with
    | some (x, xs) => return (x, xs.take n)
    | none => return (none, empty)

/-- Drop the first `n` elements. -/
unsafe def drop : ListM m α → Nat → ListM m α
  | xs, 0    => xs
  | xs, n+1 => cons do
    match ← uncons xs with
    | some (_, xs) => return (none, drop xs n)
    | none => return (none, empty)

/-- Apply a function which returns values in the monad to every element of a `ListM`. -/
unsafe def mapM {α β : Type u} (f : α → m β) (L : ListM m α) : ListM m β :=
  cons do match ← uncons L with
  | some (x, xs) => return (← f x, mapM f xs)
  | none => return (none, empty)
#align tactic.mllist.mmap ListM.mapM

/-- Apply a function to every element of a `ListM`. -/
unsafe def map {α β : Type u} (f : α → β) (L : ListM m α) : ListM m β :=
  L.mapM fun a => pure (f a)
#align tactic.mllist.map ListM.map

/-- Filter a `ListM` using a monadic function. -/
unsafe def filterM {α : Type u} (p : α → m (ULift Bool)) (L : ListM m α) : ListM m α :=
  cons do match ← uncons L with
  | some (x, xs) => return (if (← p x).down then some x else x, filterM p xs)
  | none => return (none, empty)
#align tactic.mllist.mfilter ListM.filterM

/-- Filter a `ListM`. -/
unsafe def filter {α : Type u} (p : α → Bool) (L : ListM m α) : ListM m α :=
  L.filterM fun a => pure <| .up (p a)
#align tactic.mllist.filter ListM.filter

/-- Filter and transform a `ListM` using a function that returns values inside the monad. -/
-- Note that the type signature has changed since Lean 3, when we allowed `f` to fail.
-- Use `try?` from `Mathlib.Control.Basic` to lift a possibly failing function to `Option`.
unsafe def filterMapM {α β : Type u} (f : α → m (Option β)) (L : ListM m α) : ListM m β :=
  cons do match ← uncons L with
  | none => return (none, empty)
  | some (x, xs) => match ← f x with
    | none => return (none, xs.filterMapM f)
    | some b => return (some b, xs.filterMapM f)
#align tactic.mllist.mfilter_map ListM.filterMapM

/-- Filter and transform a `ListM` using an `Option` valued function. -/
unsafe def filterMap {α β : Type u} (f : α → Option β) : ListM m α → ListM m β :=
  filterMapM fun a => do pure (f a)
#align tactic.mllist.filter_map ListM.filterMap

/-- Take the initial segment of the lazy list, until the function `f` first returns `false`. -/
unsafe def takeWhileM [Alternative m] (f : α → m (ULift Bool)) (L : ListM m α) : ListM m α :=
  cons do match ← uncons L with
  | none => return (none, empty)
  | some (x, xs) => return if (← f x).down then (some x, xs) else (none, empty)

/-- Take the initial segment of the lazy list, until the function `f` first returns `false`. -/
unsafe def takeWhile [Alternative m] (f : α → Bool) : ListM m α → ListM m α :=
  takeWhileM fun a => pure (.up (f a))

/-- Concatenate two monadic lazy lists. -/
unsafe def append {α : Type u} (L M : ListM m α) : ListM m α :=
  cons do match ← uncons L with
  | none => return (none, M)
  | some (x, xs) => return (some x, append xs M)
#align tactic.mllist.append ListM.append

/-- Join a monadic lazy list of monadic lazy lists into a single monadic lazy list. -/
unsafe def join {α : Type u} (L : ListM m (ListM m α)) : ListM m α :=
  cons do match ← uncons L with
  | none => return (none, empty)
  | some (x, xs) => match ← uncons x with
    | none => return (none, xs.join)
    | some (y, ys) => return (some y, cons (pure (some ys, xs)) |>.join)
#align tactic.mllist.join ListM.join

/-- Lift a monadic lazy list inside the monad to a monadic lazy list. -/
unsafe def squash (t : m (ListM m α)) : ListM m α :=
  (ListM.ofListM [t]).join
#align tactic.mllist.squash ListM.squash

/-- Enumerate the elements of a monadic lazy list, starting at a specified offset. -/
unsafe def enum_from {α : Type u} (n : Nat) (L : ListM m α) : ListM m (Nat × α) :=
  cons do match ← uncons L with
  | none => return (none, empty)
  | some (x, xs) => return (some (n, x), xs.enum_from (n+1))
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

/-- Take the product of two monadic lazy lists. -/
unsafe def zip (L : ListM m α) (M : ListM m β) : ListM m (α × β) :=
  squash do match ← uncons L, ← uncons M with
    | some (a, L'), some (b, M') => pure <| cons <| pure ((a, b), L'.zip M')
    | _, _ => pure nil

/-- Apply a function returning a monadic lazy list to each element of a monadic lazy list,
joining the results. -/
unsafe def bind {α β : Type u} (L : ListM m α) (f : α → ListM m β) : ListM m β :=
  cons do match ← uncons L with
  | none => return (none, empty)
  | some (x, xs) => match ← uncons (f x) with
    | none => return (none, (xs.bind f))
    | some (y, ys) => return (some y, append ys (xs.bind f))
#align tactic.mllist.bind_ ListM.bind

/-- Convert any value in the monad to the singleton monadic lazy list. -/
unsafe def monadLift (x : m α) : ListM m α :=
  cons <| (flip Prod.mk nil ∘ some) <$> x
#align tactic.mllist.monad_lift ListM.monadLift

/-- Lift the monad of a lazy list. -/
unsafe def liftM [Monad n] [MonadLift m n] (L : ListM m α) : ListM n α :=
  squash do match ← (uncons L : m _) with
    | none => pure empty
    | some (a, L') => pure <| cons do pure (a, L'.liftM)

/-- Given a lazy list in a state monad, run it on some initial state, recording the states. -/
unsafe def runState {σ α : Type u} (L : ListM (StateT.{u} σ m) α) (s : σ) : ListM m (α × σ) :=
  squash do match ← StateT.run (uncons L) s with
    | (none, _) => pure empty
    | (some (a, L'), s') => pure <| cons do pure (some (a, s'), L'.runState s')

/-- Given a lazy list in a state monad, run it on some initial state. -/
unsafe def runState' {σ α : Type u} (L : ListM (StateT.{u} σ m) α) (s : σ) : ListM m α :=
  L.runState s |>.map (·.1)

/-- Return the head of a monadic lazy list if it exists, as an `Option` in the monad. -/
unsafe def head? (L : ListM m α) : m (Option α) := do
  pure <| (← L.uncons).map (·.1)

/-- Take the initial segment of the lazy list,
up to and including the first place where `f` gives `true`. -/
unsafe def takeUpToFirstM (L : ListM m α) (f : α → m (ULift Bool)) : ListM m α :=
  cons do match ← uncons L with
  | none => return (none, empty)
  | some (x, xs) =>
    if (← (f x)).down then
      return (some x, empty)
    else
      return (some x, xs.takeUpToFirstM f)

/-- Take the initial segment of the lazy list,
up to and including the first place where `f` gives `true`. -/
unsafe def takeUpToFirst (L : ListM m α) (f : α → Bool) : ListM m α :=
  L.takeUpToFirstM fun a => pure (.up (f a))

/-- Gets the last element of a monadic lazy list, as an option in the monad.
This will run forever if the list is infinite. -/
unsafe def getLast? (L : ListM m α) : m (Option α) := do
  match ← uncons L with
  | none => return none
  | some (x, xs) => aux x xs
where aux (x : α) (L : ListM m α) : m (Option α) := do
  match ← uncons L with
  | none => return (some x)
  | some (y, ys) => aux y ys

/-- Gets the last element of a monadic lazy list, or the default value if the list is empty.
This will run forever if the list is infinite. -/
unsafe def getLast! [Inhabited α] (L : ListM m α) : m α :=
  Option.get! <$> L.getLast?

/-- Folds a binary function across a monadic lazy list, from an initial starting value.
This will run forever if the list is infinite. -/
unsafe def foldM (f : β → α → m β) (init : β) (L : ListM m α) : m β :=
  (L.foldsM f init |>.getLast?) <&> (·.getD init) -- `foldsM` is always non-empty, anyway.

/-- Folds a binary function across a monadic lazy list, from an initial starting value.
This will run forever if the list is infinite. -/
unsafe def fold (f : β → α → β) (init : β) (L : ListM m α) : m β :=
  L.foldM (fun b a => pure (f b a)) init

section Alternative
variable [Alternative m]

/--
Return the head of a monadic lazy list, as a value in the monad.
Fails if the list is empty.
-/
unsafe def head (L : ListM m α) : m α := do
  let some (r, _) ← L.uncons | failure
  return r
#align tactic.mllist.head ListM.head

/--
Apply a function returning values inside the monad to a monadic lazy list,
returning only the first successful result.
-/
unsafe def firstM (L : ListM m α) (f : α → m (Option β)) : m β :=
  (L.filterMapM f).head
#align tactic.mllist.mfirst ListM.firstM

/-- Return the first value on which a predicate returns true. -/
unsafe def first (L : ListM m α) (p : α → Bool) : m α :=
  (L.filter p).head

end Alternative

unsafe instance : Monad (ListM m) where
  pure := fun a => .ofList [a]
  seq := fun fs as => fs.zip (as ()) |>.map fun ⟨f, a⟩ => f a
  bind := bind

unsafe instance : Alternative (ListM m) where
  failure := nil
  orElse := fun L M => L.append (M ())

unsafe instance : MonadLift m (ListM m) where
  monadLift := monadLift
