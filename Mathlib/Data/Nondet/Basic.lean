/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Tactic.Lint
import Std.Data.MLList.Basic
import Mathlib.Data.MLList.Basic

/-!
# A nondeterminism monad.

We represent nondeterministic values in a type `α` as a single field structure containing an
`MLList m (σ × α)`, i.e. as a monadic lazy list of possible values,
each equipped with the backtrackable state
required to run further computations in the ambient monad.

We provide an `Alternative` `Monad` instance, as well as functions `bind`, `mapM`, and `filterMapM`,
and functions `singletonM`, `ofListM`, `ofOptionM`, and `firstM`
for entering and leaving the nondeterministic world.

Operations on the nondeterministic value via `bind`, `mapM`, and `filterMapM`
run with the appropriate backtrackable state, and are responsible for updating the state themselves
(typically this doesn't need to be done explicitly,
but just happens as a side effect in the monad `m`).
-/

set_option autoImplicit true

open Lean

/--
`Nondet m α` is variation on `MLList m α` suitable for use with backtrackable monads `m`.

We think of `Nondet m α` as a nondeterministic value in `α`,
with the possible alternatives stored in a monadic lazy list.

Along with each `a : α` we store the backtrackable state, and ensure that monadic operations
on alternatives run with the appropriate state.

Operations on the nondeterministic value via `bind`, `mapM`, and `filterMapM`
run with the appropriate backtrackable state, and are responsible for updating the state themselves
(typically this doesn't need to be done explicitly,
but just happens as a side effect in the monad `m`).
-/
@[nolint unusedArguments]
structure Nondet (m : Type → Type) [MonadBacktrack σ m] (α : Type) : Type where
  /--
  Convert a non-deterministic value into a lazy list, keeping the backtrackable state.
  Be careful that monadic operations on the `MLList` will not respect this state!
  -/
  toMLList : MLList m (α × σ)

namespace Nondet

variable {m : Type → Type} [Monad m] [MonadBacktrack σ m]

/-- The empty nondeterministic value. -/
def nil : Nondet m α := .mk .nil

instance : Inhabited (Nondet m α) := ⟨.nil⟩

/--
Squash a monadic nondeterministic value to a nondeterministic value.
-/
def squash (L : Unit → m (Nondet m α)) : Nondet m α :=
  .mk <| MLList.squash fun _ => return (← L ()).toMLList

/--
Bind a nondeterministic function over a nondeterministic value,
ensuring the function is run with the relevant backtrackable state at each value.
-/
partial def bind (L : Nondet m α) (f : α → Nondet m β) : Nondet m β := .squash fun _ => do
  match ← L.toMLList.uncons with
  | none => pure .nil
  | some (⟨x, s⟩, xs) => do
    let r := (Nondet.mk xs).bind f
    restoreState s
    match ← (f x).toMLList.uncons with
    | none => return r
    | some (y, ys) => return .mk <| .cons y (ys.append (fun _ => r.toMLList))

/-- Convert any value in the monad to the singleton nondeterministic value. -/
def singletonM (x : m α) : Nondet m α :=
  .mk <| .singletonM do
    let a ← x
    return (a, ← saveState)

/-- Convert a value to the singleton nondeterministic value. -/
def singleton (x : α) : Nondet m α := singletonM (pure x)

/-- `Nondet m` is a monad. -/
instance : Monad (Nondet m) where
  pure a := singletonM (pure a)
  bind := bind

/-- `Nondet m` is an alternative monad. -/
instance : Alternative (Nondet m) where
  failure := .nil
  orElse x y := .mk <| x.toMLList.append fun _ => (y ()).toMLList

instance : MonadLift m (Nondet m) where
  monadLift := singletonM

/--
Lift a list of monadic values to a nondeterministic value.
We ensure that each monadic value is evaluated with the same backtrackable state.
-/
def ofListM (L : List (m α)) : Nondet m α :=
  .squash fun _ => do
    let s ← saveState
    return .mk <| MLList.ofListM <| L.map fun x => do
      restoreState s
      let a ← x
      pure (a, ← saveState)

/--
Lift a list of values to a nondeterministic value.
(The backtrackable state in each will be identical:
whatever the state was when we first read from the result.)
-/
def ofList (L : List α) : Nondet m α := ofListM (L.map pure)

/-- Apply a function which returns values in the monad to every alternative of a `Nondet m α`. -/
partial def mapM (f : α → m β) (L : Nondet m α) : Nondet m β :=
  L.bind fun a => singletonM (f a)

/-- Apply a function to each alternative in a `Nondet m α` . -/
def map (f : α → β) (L : Nondet m α) : Nondet m β :=
  L.mapM fun a => pure (f a)

/-- Convert a monadic optional value to a nondeterministic value. -/
def ofOptionM (x : m (Option α)) : Nondet m α := .squash fun _ => do
  match ← x with
  | none => return .nil
  | some a => return singleton a

/-- Convert an optional value to a nondeterministic value. -/
def ofOption (x : Option α) : Nondet m α := ofOptionM (pure x)

/-- Filter and map a nondeterministic value using a monadic function which may return `none`. -/
partial def filterMapM (f : α → m (Option β)) (L : Nondet m α) : Nondet m β :=
  L.bind fun a => ofOptionM (f a)

/-- Filter and map a nondeterministic value. -/
def filterMap (f : α → Option β) (L : Nondet m α) : Nondet m β :=
  L.filterMapM fun a => pure (f a)

/-- Filter a nondeterministic value using a monadic predicate. -/
partial def filterM (p : α → m (ULift Bool)) (L : Nondet m α) : Nondet m α :=
  L.filterMapM fun a => do
    if (← p a).down then
      pure (some a)
    else
      pure none

/-- Filter a nondeterministic value. -/
def filter (p : α → Bool) (L : Nondet m α) : Nondet m α :=
  L.filterM fun a => pure <| .up (p a)

/--
All iterations of a non-deterministic function on an initial value.

(That is, depth first search.)
-/
partial def iterate (f : α → Nondet m α) (a : α) : Nondet m α :=
  singleton a <|> (f a).bind (iterate f)

/--
Find the first alternative in a nondeterministic value, as a monadic value.
-/
def head [Alternative m] (L : Nondet m α) : m α := do
  let (x, s) ← L.toMLList.head
  restoreState s
  return x

/--
Find the value of a monadic function on the first alternative in a nondeterministic value
where the function succeeds.
-/
def firstM [Alternative m] (L : Nondet m α) (f : α → m (Option β)) : m β :=
  L.filterMapM f |>.head

/--
Convert a non-deterministic value into a lazy list, by discarding the backtrackable state.
-/
def toMLList' (L : Nondet m α) : MLList m α := L.toMLList.map (·.1)

/--
Convert a non-deterministic value into a list in the monad, retaining the backtrackable state.
-/
def toList (L : Nondet m α) : m (List (α × σ)) := L.toMLList.force

/--
Convert a non-deterministic value into a list in the monad, by discarding the backtrackable state.
-/
def toList' (L : Nondet m α) : m (List α) := L.toMLList.map (·.1) |>.force

end Nondet

/-- The `Id` monad is trivially backtrackable, with state `Unit`. -/
-- This is useful so we can use `Nondet Id α` instead of `List α`
-- as the basic non-determinism monad.
instance : MonadBacktrack Unit Id where
  saveState := pure ()
  restoreState _ := pure ()
