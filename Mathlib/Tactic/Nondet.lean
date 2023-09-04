/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean
import Std.Tactic.Lint
import Std.Data.MLList.Basic

/-!
# A nondeterminism monad.

We represent nondeterministic values in a type `α` as `MLList m (σ × α)`,
i.e. as a monadic lazy list of possible values, each equipped with the backtrackable state
required to run further computations in the ambient monad.

We define the type synonym `Nondet m α` for this, as we need to equip it with a different
`Monad` instance (that backtracks state appropriately in `bind`) than the default provided
for `MLList`.

Similarly, various monadic functions need to be redefined (e.g. `mapM` and `filterMapM`),
and to avoid confusion resulting from using the `MLList` API,
we eventually mark `Nondet` as irreducible.
-/

set_option autoImplicit true

namespace MLList

def singletonM [Monad m] (x : m α) : MLList m α :=
  .squash fun _ => do return .cons (← x) .nil

def singleton [Monad m] (x : α) : MLList m α :=
  .singletonM (pure x)

end MLList

open Lean

/--
`Nondet m α` is variation on `MLList m α` suitable for use with backtrackable monads `m`.

We think of `Nondet m α` as a nondeterministic value in `α`,
with the possible alternatives stored in a monadic lazy list.

Along with each `a : α` we store the backtrackable state, and ensure that monadic operations
on alternatives run with the appropriate state.
-/
@[nolint unusedArguments]
def Nondet (m : Type → Type) [MonadBacktrack σ m] (α : Type) : Type := MLList m (σ × α)

namespace Nondet

variable {m : Type → Type} [Monad m] [MonadBacktrack σ m]

instance : Inhabited (Nondet m α) := ⟨MLList.nil⟩

/--
Bind a nondeterministic function over a nondeterministic value,
ensuring the function is run with the relevant backtrackable state at each value.
-/
partial def bind (L : Nondet m α) (f : α → Nondet m β) : Nondet m β :=
  L.casesM
    (fun _ => pure .nil)
    (fun ⟨s, x⟩ xs => do match ← (do restoreState s; MLList.uncons (f x)) with
    | none => return bind xs f
    | some (y, ys) => return .cons y (ys.append (fun _ => bind xs f)))

/-- `Nondet m` is a monad. -/
instance : Monad (Nondet m) where
  pure a := .singletonM do return (← saveState, a)
  bind := bind

/-- `Nondet m` is an alternative monad. -/
instance : Alternative (Nondet m) where
  failure := MLList.nil
  orElse := MLList.append

/-- Convert any value in the monad to the singleton nondeterministic value. -/
def monadLift (x : m α) : Nondet m α :=
  .singletonM do
    let a ← x
    return (← saveState, a)

instance : MonadLift m (Nondet m) where
  monadLift := monadLift

/--
Lift a list of monadic values to a nondeterministic value.
We ensure that each monadic value is evaluated with the same backtrackable state.
-/
def ofMLList [Alternative m] (L : List (m α)) : Nondet m α :=
  MLList.squash fun _ => do
    let s ← saveState
    return MLList.ofList L |>.mapM fun x => do
      restoreState s
      let a ← x
      pure (← saveState, a)

/--
Lift a list of values to a nondeterministic value.
(The backtrackable state in each will be identical:
whatever the state was when we first read from the result.)
-/
def ofList [Alternative m] (L : List α) : Nondet m α := ofMLList (L.map pure)

/--
Squash a monadic nondeterministic value to a nondeterministic value.
-/
def squash (L : Unit → m (Nondet m α)) : Nondet m α := MLList.squash L

/--
Lift a list of monadic values in the monad to a nondeterministic value.
-/
def ofMLList' [Alternative m] (L : m (List (m α))) : Nondet m α :=
  .squash fun _ => (.ofMLList <$> L)

/-- Apply a function which returns values in the monad to every alternative of a `Nondet m α`. -/
partial def mapM (f : α → m β) (L : Nondet m α) : Nondet m β :=
  L.casesM
    (fun _ => return .nil)
    (fun ⟨s, x⟩ xs => do
      restoreState s
      let r ← f x
      let s' ← saveState
      return .cons (s', r) (Nondet.mapM f xs))

/-- Apply a function to each alternative in a `Nondet m α` . -/
def map (f : α → β) (L : Nondet m α) : Nondet m β :=
  L.mapM fun a => pure (f a)

/-- Filter a nondeterministic value using a monadic predicate. -/
partial def filterM (p : α → m (ULift Bool)) (L : Nondet m α) : Nondet m α :=
  L.casesM
    (fun _ => return .nil)
    (fun ⟨s, x⟩ xs => do
      restoreState s
      let r := (← p x).down
      let s' ← saveState
      return if r then do
        .cons (s', x) (filterM p xs)
      else
        (filterM p xs))

/-- Filter a nondeterministic value. -/
def filter (p : α → Bool) (L : Nondet m α) : Nondet m α :=
  L.filterM fun a => pure <| .up (p a)

/-- Filter and map a nondeterministic value using a monadic function which may return `none`. -/
partial def filterMapM (f : α → m (Option β)) (L : Nondet m α) : Nondet m β :=
  L.casesM
    (fun _ => return .nil)
    (fun ⟨s, x⟩ xs => do
      restoreState s
      match ← f x with
      | some b => do return .cons (← saveState, b) (filterMapM f xs)
      | none => return filterMapM f xs)

/-- Filter and map a nondeterministic value. -/
def filterMap (f : α → Option β) (L : Nondet m α) : Nondet m β :=
  L.filterMapM fun a => pure <| (f a)

/--
Find the first alternative in a nondeterministic value, as a monadic value.
-/
def head [Alternative m] (L : Nondet m α) : m α := (·.2) <$> MLList.head L

/--
Find the value of a monadic function on the first alternative in a nondeterministic value
where the function succeeds.
-/
def firstM [Alternative m] (L : Nondet m α) (f : α → m (Option β)) : m β :=
  MLList.firstM L (fun (s, a) => do restoreState s; f a)

/--
Convert a non-deterministic value into a lazy list, keeping the backtrackable state.
Be careful that monadic operations on the `MLList` will not respect this state!
-/
def toMLList' (L : Nondet m α) : MLList m (σ × α) := L

/--
Convert a non-deterministic value into a lazy list, by discarding the backtrackable state.
-/
def toMLList (L : Nondet m α) : MLList m α := MLList.map (fun (_, a) => a) L

end Nondet

/-!
As parts of the general `MLList` API may modify state incorrectly, we mark `Nondet` irreducible
here to prevent accidental usage of the rest of the API.
-/
attribute [irreducible] Nondet
