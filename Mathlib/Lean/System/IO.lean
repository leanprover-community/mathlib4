/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.List.Indexes

/-!
# Functions for manipulating a list of tasks

* `IO.waitAny'` is a wrapper for `IO.waitAny` that also returns the remaining tasks.
* `List.waitAll : List (Task α) → Task (List α)` gathers a list of tasks into a task returning
  the list of all results.
-/

set_option autoImplicit true

-- duplicated from `lean4/src/Init/System/IO.lean`
local macro "nonempty_list" : tactic =>
  `(tactic| exact Nat.zero_lt_succ _)

/--
Given a non-empty list of tasks, wait for the first to complete.
Return the value and the list of remaining tasks.
-/
def IO.waitAny' (tasks : List (Task α)) (h : 0 < tasks.length := by nonempty_list) :
    BaseIO (α × List (Task α)) := do
  let (i, a) ← IO.waitAny
    (tasks.mapIdx fun i t => t.map (prio := .max) fun a => (i, a))
    ((tasks.length_mapIdx _).symm ▸ h)
  return (a, tasks.eraseIdx i)

/--
Given a list of tasks, create the task returning the list of results,
by waiting for each.
-/
def List.waitAll (tasks : List (Task α)) : Task (List α) :=
  match tasks with
  | [] => .pure []
  | task::tasks => task.bind (prio := .max) fun a =>
      tasks.waitAll.map (prio := .max) fun as => a::as

namespace MLList

/--
Variant of `MLList.fix?` that allows returning values of a different type.
-/
partial def fix?' [Monad m] (f : α → m (Option (α × β))) (init : α) : MLList m β :=
  squash fun _ => do
    match ← f init with
    | none => pure .nil
    | some (a, b) => pure (.cons b (fix?' f a))

/--
Give a list of tasks, return the monadic lazy list which
returns the values as they become available.
-/
def ofTaskList (tasks : List (Task α)) : MLList BaseIO α :=
  fix?' (init := tasks) fun t => do
    if h : 0 < t.length then
      let (a, t') ← IO.waitAny' t h
      pure (some (t', a))
    else
      pure none

end MLList

namespace Lean.Core.CoreM

/--
Given a monadic value in `CoreM`, create a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : CoreM α) : CoreM (Task (CoreM α)) := do
  let task ← (t.toIO (← read) (← get)).asTask
  return task.map fun
  | .ok (a, s) => do set s; pure a
  | .error e => throwError m!"{e}"

/--
Give a list of monadic values in `CoreM`, run them all as tasks,
and return the monadic lazy list which returns the values in the order they complete.
-/
def runGreedily (tasks : List (CoreM α)) : MLList CoreM α :=
  .squash fun _ => return MLList.ofTaskList (← tasks.mapM asTask) |>.liftM.mapM id

end Lean.Core.CoreM

namespace Lean.Meta.MetaM

/--
Given a monadic value in `MetaM`, create a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : MetaM α) : MetaM (Task (MetaM α)) := do
  let task ← (t.run (← read) (← get)).asTask
  return task.map fun c : CoreM (α × Meta.State) => do let (a, s) ← c; set s; pure a

/--
Give a list of monadic values in `MetaM`, run them all as tasks,
and return the monadic lazy list which returns the values in the order they complete.
-/
def runGreedily (tasks : List (MetaM α)) : MLList MetaM α :=
  .squash fun _ => return MLList.ofTaskList (← tasks.mapM asTask) |>.liftM.mapM id

end Lean.Meta.MetaM

namespace Lean.Elab.Term.TermElabM

/--
Given a monadic value in `TermElabM`, create a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : TermElabM α) : TermElabM (Task (TermElabM α)) := do
  let task ← (t.run (← read) (← get)).asTask
  return task.map fun c : MetaM (α × Term.State) => do let (a, s) ← c; set s; pure a

/--
Give a list of monadic values in `TermElabM`, run them all as tasks,
and return the monadic lazy list which returns the values in the order they complete.
-/
def runGreedily (tasks : List (TermElabM α)) : MLList TermElabM α :=
  .squash fun _ => return MLList.ofTaskList (← tasks.mapM asTask) |>.liftM.mapM id

end Lean.Elab.Term.TermElabM

namespace Lean.Elab.Tactic.TacticM

/--
Given a monadic value in `TacticM`, create a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : TacticM α) : TacticM (Task (TacticM α)) := do
  let task ← (t (← read) |>.run (← get)).asTask
  return task.map fun c : TermElabM (α × Tactic.State) => do let (a, s) ← c; set s; pure a

/--
Give a list of monadic values in `TermElabM`, run them all as tasks,
and return the monadic lazy list which returns the values in the order they complete.
-/
def runGreedily (tasks : List (TacticM α)) : MLList TacticM α :=
  .squash fun _ => return MLList.ofTaskList (← tasks.mapM asTask) |>.liftM.mapM id

end Lean.Elab.Tactic.TacticM
