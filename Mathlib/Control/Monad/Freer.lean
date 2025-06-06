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
- `FreerState`: State monad using the `Freer` construction.
- `FreerWriter`: Writer monad using the `Freer` construction.
- `FreerCont`: Continuation monad using the `Freer` construction.

## Implementation Notes

The `Freer` monad is defined using an inductive type with constructors `pure` and `impure`.
We implement `Functor` and `Monad` instances, and prove the corresponding `LawfulFunctor`
and `LawfulMonad` instances.

The monads `FreerState`, `FreerWriter`, and `FreerCont` are built by supplying appropriate functors
to the `Freer` constructor. They are equipped with interpreters and helper functions.


## Tags

Free monad, freer monad, state monad, writer monad, continuation monad
-/

/-- The Freer monad over a type constructor `f`.

A `Freer f a` is a tree of operations from the type constructor `f`, with leaves of type `a`.
It has two constructors: `pure` for wrapping a value of type `a`, and `impure` for
representing an operation from `f` followed by a continuation.

This construction provides a free monad for any type constructor `f`, allowing for composable
effect descriptions that can be interpreted later. Unlike the traditional Free monad,
this does not require `f` to be a functor. -/

inductive Freer (f : Type → Type) (α : Type) where
  | pure : α → Freer f α
  | impure (ι : Type) (op : f ι) (cont : ι → Freer f α) : Freer f α

namespace Freer

/-- Map a function over a `Freer` monad. -/
def map {α β : Type} (F : Type → Type) (f : α → β) : Freer F α → Freer F β :=
fun FFa =>
  match FFa with
  | .pure a => .pure (f a)
  | .impure ι op cont => .impure ι op (fun z => Freer.map F f (cont z))

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
    case impure ι op cont ih => simp [Freer.map, ih]
  comp_map := by
    intro α β γ g h x
    simp [Functor.map]
    induction x
    case pure a => simp [Freer.map]
    case impure ι op cont ih => simp [Freer.map, ih]

/-- Bind operation for the `Freer` monad. -/
def bindFree {a b : Type} (F : Type → Type) (x : Freer F a) (f : a → Freer F b) : Freer F b :=
  match x with
  | .pure a => f a
  | .impure ι op cont => .impure ι op (fun z => bindFree F (cont z) f)

instance {F : Type → Type} : Monad (Freer F) where
  pure := Freer.pure
  bind := bindFree F

instance FreeLawfulMonad {F : Type → Type} : LawfulMonad (Freer F) where
  bind_pure_comp := by
    intro α β x y; simp [Functor.map, bind, pure]; induction y
    · case pure a => simp [bindFree, map, Pure.pure]
    · case impure X Fx k ih => simp [bindFree, Freer.map, ih]
  bind_map := by
    intro α β f x; simp [bind, Seq.seq]
  pure_bind := by
    intro α x a f; simp [bind, pure, bindFree]
  bind_assoc := by
    intro α β γ x f g; simp [bind]; induction x
    case pure a => simp [bindFree, Freer.map]
    case impure X Fx k ih => simp [bindFree, Freer.map, ih]
  seqLeft_eq := by
    intro α β x y; simp [Functor.map, SeqLeft.seqLeft, Seq.seq]; induction x
    case pure a =>
      simp [bindFree, Freer.map]
      induction y
      case pure b => simp [bindFree, Freer.map]
      case impure X Fy k ih => simp [bindFree, Freer.map, ih]
    case impure X Fx k ih => simp [bindFree, Freer.map, ih]
  seqRight_eq := by
    intro α β x y; simp [Functor.map, bindFree, Freer.map]; induction x
    case pure a =>
      simp [bindFree, Freer.map]
      induction y
      case pure b => simp [SeqRight.seqRight, Seq.seq, Functor.map, bindFree, Freer.map]
      case impure X Fy k ih =>
        simp [SeqRight.seqRight, Seq.seq, Functor.map, bindFree, Freer.map, ih] at ih ⊢
        apply funext; intro x; exact ih x
    case impure X Fx k ih =>
      simp [Freer.map, Seq.seq, bindFree, Functor.map, SeqRight.seqRight] at ih ⊢
      apply funext; intro x; exact ih x
  pure_seq := by
    intro α β f x; simp [Seq.seq, Functor.map, pure, bindFree]

/-! ### State Monad via `Freer` -/

/-- Type constructor for state operations. -/
inductive StateF (σ : Type) (α : Type) where
  /-- Get the current state, passing it to the continuation. -/
  | get : (σ → α) → StateF σ α
  /-- Set the state to a new value, continuing with the given result. -/
  | put : σ → α → StateF σ α

instance {σ : Type} : Functor (StateF σ) where
  map f
  | .get k => .get (f ∘ k)
  | .put st a => .put st (f a)

/-- State monad via the `Freer` monad. -/
abbrev FreerState (σ : Type) := Freer (StateF σ)

namespace FreerState

instance {σ : Type} : Monad (FreerState σ) := inferInstance
instance {σ : Type} : LawfulMonad (FreerState σ) := inferInstance

instance {σ : Type} : MonadStateOf σ (FreerState σ) where
  get := Freer.impure σ (StateF.get id) Freer.pure
  set newState := Freer.impure PUnit (StateF.put newState PUnit.unit) Freer.pure
  modifyGet f := Freer.impure σ (StateF.get id) (fun s =>
    let (a, s') := f s
    Freer.impure PUnit (StateF.put s' PUnit.unit) (fun _ => Freer.pure a))

instance {σ : Type} : MonadState σ (FreerState σ) := inferInstance

/-- Modify the state using a function. -/
def modify {σ : Type} (f : σ → σ) : FreerState σ PUnit := do
  let s ← get
  set (f s)

/-- Run a state computation, returning both the result and final state. -/
def runState {σ α : Type} (computation : FreerState σ α) (initialState : σ) : α × σ :=
  match computation with
  | Freer.pure a => (a, initialState)
  | Freer.impure _ (StateF.get k) cont => runState (cont (k initialState)) initialState
  | Freer.impure _ (StateF.put newState p) cont => runState (cont p) newState

/-- Run a state computation, returning only the result. -/
def evalState {σ α : Type} (computation : FreerState σ α) (initialState : σ) : α :=
  (runState computation initialState).1

/-- Run a state computation, returning only the final state. -/
def execState {σ α : Type} (computation : FreerState σ α) (initialState : σ) : σ :=
  (runState computation initialState).2

end FreerState

/-! ### Writer Monad via `Freer` -/

/-- Type constructor for writer operations. -/
inductive WriterF (w : Type) (α : Type) where
  /-- Append a value to the log, continuing with the given result. -/
  | tell : w → α → WriterF w α

instance {w : Type} : Functor (WriterF w) where
  map f
  | .tell log a => .tell log (f a)

/-- Writer monad via the `Freer` monad. -/
abbrev FreerWriter (w : Type) := Freer (WriterF w)

namespace FreerWriter

instance {w : Type} : Monad (FreerWriter w) := inferInstance
instance {w : Type} : LawfulMonad (FreerWriter w) := inferInstance

/-- Append to the log. -/
def tell {w : Type} (log : w) : FreerWriter w PUnit :=
  Freer.impure PUnit (WriterF.tell log PUnit.unit) Freer.pure

/-- Run a writer computation, returning the result and log. -/
def runWriter {w α : Type} [AddMonoid w] (computation : FreerWriter w α) : α × w :=
  match computation with
  | Freer.pure a => (a, 0)
  | Freer.impure _ (WriterF.tell log p) cont =>
      let (result, accLog) := runWriter (cont p)
      (result, log + accLog)

/-- Run a writer computation, returning only the log. -/
def execWriter {w α : Type} [AddMonoid w] (computation : FreerWriter w α) : w :=
  (runWriter computation).2

/-- Run a writer computation and return the result along with the log it produced. -/
def listen {w α : Type} [AddMonoid w] (computation : FreerWriter w α) : FreerWriter w (α × w) :=
  Freer.pure (runWriter computation)

end FreerWriter

/-! ### Continuation Monad via `Freer` -/

/-- Type constructor for continuation operations. -/
inductive ContF (r : Type) (α : Type) where
  /-- Call with current continuation: provides access to the current continuation. -/
  | callCC : ((α → r) → r) → ContF r α

instance {r : Type} : Functor (ContF r) where
  map f
  | .callCC g => .callCC (fun k => g (k ∘ f))

/-- Continuation monad via the `Freer` monad. -/
abbrev FreerCont (r : Type) := Freer (ContF r)

namespace FreerCont

instance {r : Type} : Monad (FreerCont r) := inferInstance
instance {r : Type} : LawfulMonad (FreerCont r) := inferInstance

/-- Run a continuation computation with the given continuation. -/
def run {r α : Type} : FreerCont r α → (α → r) → r
  | .pure a, k => k a
  | .impure _ (ContF.callCC g) cont, k => g (fun a => run (cont a) k)

end FreerCont

/-! ### Basic Examples -/

-- Example FreerState computations
example : FreerState.evalState (do
  let s ← get
  set (s + 1)
  return s : FreerState Nat Nat) 5 = 5 := rfl

example : FreerState.execState (do
  let s ← get
  set (s + 1)
  return s : FreerState Nat Nat) 5 = 6 := rfl

example : FreerState.runState (do
  let s ← get
  set (s + 1)
  return s : FreerState Nat Nat) 5 = (5, 6) := rfl

-- Example FreerCont computation
example : FreerCont.run (return 42 : FreerCont Nat Nat) id = 42 := rfl

end Freer
