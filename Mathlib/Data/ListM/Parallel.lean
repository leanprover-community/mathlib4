/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.ListM.Basic

/-!
# Parallel map over a lazy list.
-/

/-- A monad in which we can launch a task, to run with a copy of the current state. -/
class MonadTask (m : Type u → Type u) where
  asTask : m α → (prio : Task.Priority := .default) → m (Task (Except IO.Error α))

open Lean Core Meta

instance : MonadTask IO where
  asTask x prio := IO.asTask x prio

instance : MonadTask CoreM where
  asTask x prio := do
    let ctx ← read
    let σ ← getThe Core.State
    IO.asTask (CoreM.toIO x ctx σ <&> (·.1)) prio

instance : MonadTask MetaM where
  asTask x prio := do
    let ctx ← read
    let σ ← getThe Meta.State
    (MonadTask.asTask (MetaM.run' x ctx σ) prio : CoreM _)

namespace ListM

/--
Map a monadic function over a lazy list,
using a high priority task to read elements from the lazy list,
and normal priority tasks to compute the function in parallel.

Works at most `numThreads` steps ahead of the consumer.

When `outOfOrder = false` (the default behaviour),
the elements are produced in the same order as the original list.
When `outOfOrder = true`, elements will be produced in the order their computations complete.
-/
partial def parallelMapM [Monad m] [MonadTask m] [MonadLiftT BaseIO m]
    (L : ListM m α) (f : α → m β) (numThreads : Nat := 32) (outOfOrder : Bool := false) :
    ListM m (Except IO.Error β) :=
  squash do
    return run (← unconsAsTask L) []
where
  unconsAsTask (L : ListM m α) : m (Task (Option (α × ListM m α))) := do
    let t ← MonadTask.asTask (prio := .max) L.uncons
    return t.map fun e => match e with
    | .ok r => r
    | .error _ => none
  /- `uncons?` is none iff we've reached the end of the list. -/
  run (uncons? : Option (Task (Option (α × ListM m α)))) (pool : List (Task (Except _ β))) :
      ListM m (Except _ β) :=
    if uncons?.isNone || pool.length >= numThreads then
      -- We don't need to grow the pool.
      match pool with
      | [] => ListM.nil
      | hd::tl => cons do pure (← IO.wait hd, run uncons? tl)
    else
      -- We'd like to grow the pool if possible.
      let uncons := uncons?.get!
      squash do
        if ← IO.hasFinished uncons then
          match uncons.get with
          -- We've exhausted the list, so just try again with `uncons? = none`.
          | none => return run none pool
          -- Create a new task for unconsing the tail,
          -- and a new task for the next function application.
          | some (a, L') => do
              return run (← unconsAsTask L') (pool ++ [← MonadTask.asTask (f a)])
        else
          -- The unconsing task is still running.
          match pool with
          | [] => do
              -- If the pool is empty, we have no choice but to wait for unconsing.
              let u ← IO.wait uncons
              return run (some (Task.pure u)) pool
          | hd::tl => do
              if outOfOrder then
                -- We use `IO.waitAny` to wait for either unconsing, or any task in the list.
               let w : List (Task (Option (α × ListM m α) ⊕ (Nat × Except _ β))) :=
                 (uncons.map Sum.inl) :: pool.enum.map (fun (i, t) => t.map fun e => Sum.inr (i, e))
                match ← IO.waitAny w with
                | Sum.inl a => return run (some (Task.pure a)) pool
                | Sum.inr (i, e) =>
                    let r := run uncons? (pool.eraseIdx i)
                    return cons do pure (e, r)
              else
                -- Otherwise, we use `IO.waitAny` to wait for either unconsing,
                -- or the first task in the list.
                let w : List (Task (Option (α × ListM m α) ⊕ (Except _ β))) :=
                  [uncons.map Sum.inl, hd.map Sum.inr]
                match ← IO.waitAny w with
                | Sum.inl a => return run (some (Task.pure a)) pool
                | Sum.inr e =>
                    let r := run uncons? tl
                    return cons do pure (e, r)

/--
Map a function over a lazy list,
using a high priority task to read elements from the lazy list,
and normal priority tasks to compute the function in parallel.

Works at most `numThreads` steps ahead of the consumer.

When `outOfOrder = false` (the default behaviour),
the elements are produced in the same order as the original list.
When `outOfOrder = true`, elements will be produced in the order their computations complete.
-/
def parallelMap [Monad m] [MonadTask m] [MonadLiftT BaseIO m] (L : ListM m α)
    (f : α → β) (numThreads : Nat := 32) (outOfOrder : Bool := false) : ListM m β :=
  L.parallelMapM (fun a => pure (f a)) numThreads outOfOrder |>.filterMap fun r => match r with
  | .ok r => some r
  | .error (_ : IO.Error) => none
