/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
import Mathlib.Algebra.Group.Defs

/-!
# Freer Monad and Common Instances

This file defines a general `Freer` monad construction and several canonical instances:
`State`, `Writer`, and `Continuation` monads implemented via this construction.

## Main Definitions

- `Freer`: The general Freer monad.
- `FreerState`: State monad using the `Free` construction.
- `FreerWriter`: Writer monad using the `Free` construction.
- `FreerCont`: Continuation monad using the `Free` construction.

## Implementation Notes

The `Free` monad is defined using an inductive type with constructors `pure` and `bind`.
We implement `Functor` and `Monad` instances, and prove the corresponding `LawfulFunctor`
and `LawfulMonad` instances.

The monads `FreerState`, `FreerWriter`, and `FreerCont` are built by supplying appropriate functors
to the `Free` constructor. They are equipped with interpreters and helper functions.


## Tags

Freee monad, freer monad, state monad, writer monad, continuation monad
-/

/-- The Freer monad over a functor `f`.

A `Freer f a` is a tree of operations from the functor `f`, with leaves of type `a`.
It has two constructors: `pure` for wrapping a value of type `a`, and `bind` for
representing a functor operation followed by a continuation.

This construction provides a free monad for any functor `f`, allowing for composable
effect descriptions that can be interpreted later. -/
inductive Freer (f : Type → Type) (a : Type) where
| pure : a → Freer f a
| bind : ∀ x, f x → (x → Freer f a) → Freer f a

/-- Map a function over a `Free` monad. -/
def Freer.map {α β : Type} (F : Type → Type) (f : α → β) : Freer F α → Freer F β :=
fun FFa =>
  match FFa with
  | pure a => Freer.pure (f a)
  | bind X Fx k => Freer.bind X Fx (fun z => Freer.map F f (k z))

instance {F : Type → Type} : Functor (Freer F) where
  map := Freer.map F

instance {F : Type → Type} : LawfulFunctor (Freer F) where
  map_const := by
    intro α β
    simp [Functor.mapConst, Functor.map]
  id_map := by
    intro α x
    simp [Functor.map]
    induction x
    case pure a => simp [Freer.map]
    case bind X Fx f ih => simp [Freer.map, ih]
  comp_map := by
    intro α β γ g h x
    simp [Functor.map]
    induction x
    case pure a => simp [Freer.map]
    case bind X Fx f ih => simp [Freer.map, ih]

/-- Bind operation for the `Free` monad. -/
def bindFree {a b : Type} (F : Type → Type) (x : Freer F a) (f : a → Freer F b) : Freer F b :=
  match x with
  | .pure a => f a
  | .bind X Fx k => .bind X Fx (fun z => bindFree F (k z) f)

instance FreeMonad (F : Type → Type) : Monad (Freer F) where
  pure := Freer.pure
  bind := bindFree F

instance FreeLawfulMonad (F : Type → Type) : LawfulMonad (Freer F) where
  bind_pure_comp := by
    intro α β x y; simp [Functor.map, bind, pure]; induction y
    · case pure a => simp [bindFree, Freer.map]
    · case bind X Fx k ih => simp [bindFree, Freer.map, ih]
  bind_map := by
    intro α β f x; simp [bind, Seq.seq]
  pure_bind := by
    intro α x a f; simp [bind, pure, bindFree]
  bind_assoc := by
    intro α β γ x f g; simp [bind]; induction x
    case pure a => simp [bindFree, Freer.map]
    case bind X Fx k ih => simp [bindFree, Freer.map, ih]
  seqLeft_eq := by
    intro α β x y; simp [Functor.map, SeqLeft.seqLeft, Seq.seq]; induction x
    case pure a =>
      simp [bindFree, Freer.map]
      induction y
      case pure b => simp [bindFree, Freer.map]
      case bind X Fy k ih => simp [bindFree, Freer.map, ih]
    case bind X Fx k ih => simp [bindFree, Freer.map, ih]
  seqRight_eq := by
    intro α β x y; simp [Functor.map, bindFree, Freer.map]; induction x
    case pure a =>
      simp [bindFree, Freer.map]
      induction y
      case pure b => simp [SeqRight.seqRight, Seq.seq, Functor.map, bindFree, Freer.map]
      case bind X Fy k ih =>
        simp [SeqRight.seqRight, Seq.seq, Functor.map, bindFree, Freer.map, ih] at ih ⊢
        apply funext; intro x; exact ih x
    case bind X Fx k ih =>
      simp [Freer.map, Seq.seq, bindFree, Functor.map, SeqRight.seqRight] at ih ⊢
      apply funext; intro x; exact ih x
  pure_seq := by
    intro α β f x; simp [Seq.seq, Functor.map, pure, bindFree]

/-! ### State Monad via `Free` -/

/-- Functor for state operations. -/
inductive StateF (s : Type) (a : Type) where
| get : (s → a) → StateF s a
| put : s → a → StateF s a

instance {s : Type} : Functor (StateF s) where
  map f
  | StateF.get k => StateF.get (f ∘ k)
  | StateF.put st a => StateF.put st (f a)

/-- State monad via the `Free` monad. -/
def FreerState (s : Type) := Freer (StateF s)

namespace FreerState

instance {s : Type} : Monad (FreerState s) := FreeMonad (StateF s)
instance {s : Type} : LawfulMonad (FreerState s) := FreeLawfulMonad (StateF s)

/-- Get the current state. -/
def get {s : Type} : FreerState s s :=
  Freer.bind s (StateF.get id) Freer.pure

/-- Set the state. -/
def put {s : Type} (newState : s) : FreerState s PUnit :=
  Freer.bind PUnit (StateF.put newState PUnit.unit) Freer.pure

/-- Modify the state. -/
def modify {s : Type} (f : s → s) : FreerState s PUnit :=
  bindFree (StateF s) get (fun s => put (f s))

/-- Run a Freer state computation. -/
def runState {s a : Type} (computation : FreerState s a) (initialState : s) : a × s :=
  match computation with
  | Freer.pure a => (a, initialState)
  | Freer.bind _ (StateF.get k) cont =>
      runState (cont (k initialState)) initialState
  | Freer.bind _ (StateF.put newState p) cont =>
      runState (cont p) newState

/-- Evaluate a computation, returning the result. -/
def evalState {s a : Type} (computation : FreerState s a) (initialState : s) : a :=
  (runState computation initialState).1

/-- Evaluate a computation, returning the final state. -/
def execState {s a : Type} (computation : FreerState s a) (initialState : s) : s :=
  (runState computation initialState).2

end FreerState

/-! ### Writer Monad via `Free` -/

/-- Functor for writer operations. -/
inductive WriterF (w : Type) (a : Type) where
| tell : w → a → WriterF w a

instance {w : Type} : Functor (WriterF w) where
  map f
  | WriterF.tell log a => WriterF.tell log (f a)

/-- Writer monad via the `Free` monad. -/
def FreerWriter (w : Type) := Freer (WriterF w)

namespace FreerWriter

instance {w : Type} : Monad (FreerWriter w) := FreeMonad (WriterF w)
instance {w : Type} : LawfulMonad (FreerWriter w) := FreeLawfulMonad (WriterF w)

/-- Append to the log. -/
def tell {w : Type} (log : w) : FreerWriter w PUnit :=
  Freer.bind PUnit (WriterF.tell log PUnit.unit) Freer.pure

/-- Run a writer computation, returning the result and log. -/
def runWriter {w a : Type} [Monoid w] (computation : FreerWriter w a) : a × w :=
  match computation with
  | Freer.pure a => (a, 1)
  | Freer.bind _ (WriterF.tell log p) cont =>
      let (result, accLog) := runWriter (cont p)
      (result, log * accLog)

/-- Return only the result of a writer computation. -/
def execWriter {w a : Type} [Monoid w] (computation : FreerWriter w a) : a :=
  (runWriter computation).1

/-- Return result and log as a value inside the `Free` monad. -/
def listen {w a : Type} [Monoid w] (computation : FreerWriter w a) : FreerWriter w (a × w) :=
  Freer.pure (runWriter computation)

end FreerWriter

/-! ### Continuation Monad via `Free` -/

/-- CPS functor encoding one continuation-passing step. -/
@[simp]
def ContF (r : Type) (α : Type) : Type := (α → r) → r

/-- Continuation monad via the `Free` monad. -/
abbrev FreerCont (r : Type) (α : Type) := Freer (ContF r) α

namespace FreerCont

instance {r : Type} : Monad (FreerCont r) := FreeMonad (ContF r)
instance {r : Type} : LawfulMonad (FreerCont r) := FreeLawfulMonad (ContF r)

/-- Run a `FreerCont` program with a final continuation. -/
@[simp, reducible]
def run {r α} : FreerCont r α → (α → r) → r
| .pure a => fun k => k a
| .bind _ k cont => fun h => k (fun x => run (cont x) h)

end FreerCont
