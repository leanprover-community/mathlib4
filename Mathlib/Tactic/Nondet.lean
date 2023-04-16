/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.ListM.Basic

/-!
# A nondeterminism monad.

We represent nondeterministic values in a type `α` as `ListM m (σ × α)`,
i.e. as a monadic lazy list of possible values, each equipped with the backtrackable state
required to run further computations in the ambient monad.

We define the type synonym `Nondet m α` for this, as we need to equip it with a different
`Monad` instance (that backtracks state appropriately in `bind`) than the default provided
for `ListM`.

Similarly, various monadic functions need to be redefined (e.g. `mapM` and `filterMapM`),
and to avoid confusion resulting from using the `ListM` API,
we eventually mark `Nondet` as irreducible.
-/

open Lean

/--
`Nondet m α` is variation on `ListM m α` suitable for use with backtrackable monads `m`.

We think of `Nondet m α` as a nondeterministic value in `α`,
with the possible alternatives stored in a monadic lazy list.

Along with each `a : α` we store the backtrackable state, and ensure that monadic operations
on alternatives run with the appropriate state.
-/
unsafe def Nondet (m : Type → Type) [MonadBacktrack σ m] (α : Type) : Type := ListM m (σ × α)

namespace Nondet

variable {m : Type → Type} [Monad m] [MonadBacktrack σ m]

/--
Bind a nondeterministic function over a nondeterministic value,
ensuring the function is run with the relevant backtrackable state at each value.
-/
unsafe def bind (L : Nondet m α) (f : α → Nondet m β) : Nondet m β :=
  ListM.cons do match ← ListM.uncons L with
  | none => return (none, ListM.nil)
  | some ((s, x), xs) => match ← (do restoreState s; ListM.uncons (f x)) with
    | none => return (none, (bind xs f))
    | some (y, ys) => return (some y, ListM.append ys (bind xs f))

/-- `Nondet m` is a monad. -/
unsafe instance : Monad (Nondet m) where
  pure a := ListM.cons do return (some (← saveState, a), ListM.nil)
  bind := bind

/-- `Nondet m` is an alternative monad. -/
unsafe instance : Alternative (Nondet m) where
  failure := ListM.nil
  orElse := ListM.orElse

/-- Convert any value in the monad to the singleton nondeterministic value. -/
unsafe def monadLift (x : m α) : Nondet m α :=
  ListM.cons do
    let a ← x
    return (some (← saveState, a), ListM.nil)

unsafe instance : MonadLift m (Nondet m) where
  monadLift := monadLift

/--
Lift a list of monadic values to a nondeterministic value.
We ensure that each monadic value is evaluated with the same backtrackable state.
-/
unsafe def ofListM [Alternative m] (L : List (m α)) : Nondet m α :=
  ListM.squash do
    return aux (← saveState) L
where aux (s : σ) : List (m α) → Nondet m α
  | [] => ListM.nil
  | h :: t => ListM.cons do
      restoreState s
      let r ← some <$> h <|> pure none
      pure (← r.mapM fun r => do pure (← saveState, r), aux s t)

/--
Squash a monadic nondeterministic value to a nondeterministic value.
-/
unsafe def squash (L : m (Nondet m α)) : Nondet m α := ListM.squash L

/--
Lift a list of monadic values in the monad to a nondeterministic value.
-/
unsafe def ofListM' [Alternative m] (L : m (List (m α))) : Nondet m α := .squash (.ofListM <$> L)

/-- If `L` is empty, return a default value `M`,
otherwise bind a function `f` over each alternative. -/
unsafe def bindOrElse [Monad m] (L : Nondet m α) (f : α → Nondet m β) (M : Nondet m β) :
    Nondet m β :=
  squash do match ← ListM.uncons L with
  | none => return M
  | some ((s, x), xs) => match ← (do restoreState s; ListM.uncons (f x)) with
    | none => return bind xs f
    | some (y, ys) => return ListM.cons <| pure (some y, ListM.orElse ys fun _ => bind xs f)

/-- Apply a function which returns values in the monad to every alternative of a `Nondet m α`. -/
unsafe def mapM (f : α → m β) (L : Nondet m α) : Nondet m β :=
  ListM.cons do match ← ListM.uncons L with
  | some ((s, x), xs) => do
      restoreState s
      let r ← f x
      let s' ← saveState
      return ((s', r), mapM f xs)
  | none => return (none, ListM.nil)

/-- Apply a function to each alternative in a `Nondet m α` . -/
unsafe def map (f : α → β) (L : Nondet m α) : Nondet m β :=
  L.mapM fun a => pure (f a)

unsafe def filterM (p : α → m (ULift Bool)) (L : Nondet m α) : Nondet m α :=
  ListM.cons do match ← ListM.uncons L with
  | none => return (none, ListM.nil)
  | some ((s, x), xs) => do
      restoreState s
      let r := (← p x).down
      return (if r then some (← saveState , x) else none, filterM p xs)

/-- Filter a `ListM`. -/
unsafe def filter (p : α → Bool) (L : Nondet m α) : Nondet m α :=
  L.filterM fun a => pure <| .up (p a)

/--
Find the first alternative in a nondeterministic value, as a monadic value.
-/
unsafe def head [Alternative m] (L : Nondet m α) : m α := (·.2) <$> ListM.head L

/--
Find the value of a monadic function on the first alternative in a nondeterministic value
where the function succeeds.
-/
unsafe def firstM [Alternative m] (L : Nondet m α) (f : α → m (Option β)) : m β :=
  ListM.firstM L (fun (s, a) => do restoreState s; f a)

end Nondet

/-!
As parts of the general `ListM` API may modify state incorrectly, we mark `Nondet` irreducible
here to prevent accidental usage of the rest of the API.
-/
attribute [irreducible] Nondet
