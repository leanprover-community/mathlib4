/-
Copyright (c) 2023 J. W. Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. W. Gerbscheid
-/

import Mathlib.Init

/-!
The combined state and list monad transformer.
`StateListT σ α` is equivalent to `StateT σ (ListT α)` but more efficient.

WARNING: `StateListT σ α m` is only a monad if `m` is a commutative monad.
For example,
```
def problem : StateListT Unit (StateM (Array Nat)) Unit := do
  Alternative.orElse (pure ()) (fun _ => pure ())
  StateListT.lift $ modify (·.push 0)
  StateListT.lift $ modify (·.push 1)

#eval ((problem.run' ()).run #[]).2
```
will yield either `#[0,1,0,1]`, or `#[0,0,1,1]`, depending on the order in which the actions
in the do block are combined.

-/

/-! StateList -/

namespace Mathlib.Meta.FunProp

universe u v

/-- `StateList` is a List with a state associated to each element.
This is used instead of `List (α × σ)` as it is more efficient. -/
inductive StateList (σ α : Type u) where
  /-- .nil is the empty list. -/
  | nil : StateList σ α
  /-- If `a : α`, `s : σ` and `l : List α`, then `.cons a s l`, is the
  list with first element `a` with state `s` and `l` as the rest of the list. -/
  | cons : α → σ → StateList σ α → StateList σ α

variable {α β σ : Type u}

namespace StateList

private def toList : StateList σ α → List (α × σ)
  | .cons a s l => (a, s) :: l.toList
  | .nil => []

private def toList' : StateList σ α → List α
  | .cons a _ l => a :: l.toList'
  | .nil => []

private def map (f : α → β) : StateList σ α → StateList σ β
  | .cons a s l   => .cons (f a) s (l.map f)
  | .nil => .nil

private def append : (xs ys : StateList σ α) → StateList σ α
  | .nil,         bs => bs
  | .cons a s l, bs => .cons a s (l.append bs)

instance : Append (StateList σ α) := ⟨StateList.append⟩

@[specialize]
private def foldrM {m} [Monad m] : (f : α → σ → β → m β) → (init : β) → StateList σ α → m β
  | _, b, .nil     => pure b
  | f, b, .cons a s l => do
    f a s (← l.foldrM f b)

end StateList

/-- The combined state and list monad transformer. -/
def StateListT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (StateList σ α)

variable {m : Type u → Type v} [Monad m]

/-- Run `x` on a given state `s`, returning the list of values with corresponding states. -/
@[always_inline, inline]
def StateListT.run [Functor m] (x : StateListT σ m α) (s : σ) : m (List (α × σ)) :=
  StateList.toList <$> x s

/-- Run `x` on a given state `s`, returning the list of values. -/
@[always_inline, inline]
def StateListT.run' [Functor m] (x : StateListT σ m α) (s : σ) : m (List α) :=
  StateList.toList' <$> x s

/-- The combined state and list monad. -/
abbrev StateListM (σ α : Type u) : Type u := StateListT σ Id α

namespace StateListT
section

@[always_inline, inline]
private def pure (a : α) : StateListT σ m α :=
  fun s => return StateList.nil.cons a s

/-- Separately handling lists of length 1 is important to avoid a stack overflow. -/
@[always_inline, inline]
private def bind (x : StateListT σ m α) (f : α → StateListT σ m β) : StateListT σ m β :=
  fun s => do match ← x s with
    | .nil => return .nil
    | .cons a s .nil => f a s
    | x => x.foldrM (fun a s bs => return (← f a s) ++ bs) .nil

@[always_inline, inline]
private def map (f : α → β) (x : StateListT σ m α) : StateListT σ m β :=
  fun s => StateList.map f <$> x s

@[always_inline]
instance : Monad (StateListT σ m) where
  pure := StateListT.pure
  bind := StateListT.bind
  map  := StateListT.map

@[always_inline, inline]
private def orElse (x : StateListT σ m α) (y : Unit → StateListT σ m α) : StateListT σ m α :=
  fun s => (· ++ ·) <$> x s <*> y () s

@[always_inline, inline]
private def failure : StateListT σ m α :=
  fun _ => return .nil

instance : Alternative (StateListT σ m) where
  failure := StateListT.failure
  orElse  := StateListT.orElse

/-- Return the state from `StateListT σ m`. -/
@[always_inline, inline]
protected def get : StateListT σ m σ :=
  fun s => return StateList.nil.cons s s

/-- Set the state in `StateListT σ m`. -/
@[always_inline, inline]
protected def set : σ → StateListT σ m PUnit :=
  fun s' _ => return StateList.nil.cons ⟨⟩ s'

/-- Modify and get the state in `StateListT σ m`. -/
@[always_inline, inline]
protected def modifyGet (f : σ → α × σ) : StateListT σ m α :=
  fun s => let a := f s; return StateList.nil.cons a.1 a.2

/-- Lift an action from `m α` to `StateListT σ m α`. -/
@[always_inline, inline]
protected def lift (t : m α) : StateListT σ m α :=
  fun s => do let a ← t; return StateList.nil.cons a s

instance : MonadLift m (StateListT σ m) := ⟨StateListT.lift⟩

@[always_inline]
instance : MonadFunctor m (StateListT σ m) := ⟨fun f x s => f (x s)⟩

@[always_inline]
instance{ε} [MonadExceptOf ε m] : MonadExceptOf ε (StateListT σ m) := {
  throw    := StateListT.lift ∘ throwThe ε
  tryCatch := fun x c s => tryCatchThe ε (x s) (fun e => c e s)
}

end
end StateListT


instance : MonadStateOf σ (StateListT σ m) where
  get       := StateListT.get
  set       := StateListT.set
  modifyGet := StateListT.modifyGet


@[always_inline]
instance StateListT.monadControl : MonadControl m (StateListT σ m) where
  stM      := StateList σ
  liftWith := fun f => do let s ← get; liftM (f (fun x => x s))
  restoreM := fun x _ => x

end Mathlib.Meta.FunProp
