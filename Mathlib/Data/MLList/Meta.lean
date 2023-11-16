/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.MLList.IO
import Mathlib.Data.List.Defs

/-!
# Parallelization in Lean's tactic monads.

`MetaM.runGreedily` will run a list of `MetaM α` in parallel,
producing an `MLList MetaM α` that returns the results (and the relevant `MetaM` state)
in the order that they finish.

Note that there is no way to cancel the generated tasks:
even if you dispose of the `MLList` before consuming the results,
the tasks will still consume resources.

(Similarly also for `CoreM`, `TermElabM`, and `TacticM`.)
-/

set_option autoImplicit true

namespace IO

/--
Given a list of values in `IO α`, executes them all in parallel as tasks, and
returns the monadic lazy list which returns the values in the order they complete.
-/
def runGreedily (tasks : List (IO α)) : MLList IO α :=
  .squash fun _ => do
    let t := (tasks.map IO.asTask).traverse id
    return MLList.ofTaskList (← t) |>.liftM |>.mapM fun
    | .ok a => pure a
    | .error e => throw (IO.userError s!"{e}")

end IO

namespace Lean.Core.CoreM

/--
Given a monadic value in `CoreM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : CoreM α) : CoreM (Task (CoreM α)) := do
  let task ← (t.toIO (← read) (← get)).asTask
  return task.map fun
  | .ok (a, s) => do set s; pure a
  | .error e => throwError m!"{e}"

/--
Given a list of monadic values in `CoreM`, runs them all as tasks,
and returns the monadic lazy list which returns the values in the order they complete.
-/
def runGreedily (tasks : List (CoreM α)) : MLList CoreM α :=
  .squash fun _ => return MLList.ofTaskList (← tasks.mapM asTask) |>.liftM.mapM id

end Lean.Core.CoreM

namespace Lean.Meta.MetaM

/--
Given a monadic value in `MetaM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : MetaM α) : MetaM (Task (MetaM α)) := do
  let task ← (t.run (← read) (← get)).asTask
  return task.map fun c : CoreM (α × Meta.State) => do let (a, s) ← c; set s; pure a

/--
Given a list of monadic values in `MetaM`, runs them all as tasks,
and return the monadic lazy list which returns the values in the order they complete.
-/
def runGreedily (tasks : List (MetaM α)) : MLList MetaM α :=
  .squash fun _ => return MLList.ofTaskList (← tasks.mapM asTask) |>.liftM.mapM id

end Lean.Meta.MetaM

namespace Lean.Elab.Term.TermElabM

/--
Given a monadic value in `TermElabM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : TermElabM α) : TermElabM (Task (TermElabM α)) := do
  let task ← (t.run (← read) (← get)).asTask
  return task.map fun c : MetaM (α × Term.State) => do let (a, s) ← c; set s; pure a

/--
Given a list of monadic values in `TermElabM`, runs them all as tasks,
and returns the monadic lazy list which returns the values in the order they complete.
-/
def runGreedily (tasks : List (TermElabM α)) : MLList TermElabM α :=
  .squash fun _ => return MLList.ofTaskList (← tasks.mapM asTask) |>.liftM.mapM id

end Lean.Elab.Term.TermElabM

namespace Lean.Elab.Tactic.TacticM

/--
Given a monadic value in `TacticM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : TacticM α) : TacticM (Task (TacticM α)) := do
  let task ← (t (← read) |>.run (← get)).asTask
  return task.map fun c : TermElabM (α × Tactic.State) => do let (a, s) ← c; set s; pure a

/--
Given a list of monadic values in `TermElabM`, runs them all as tasks,
and returns the monadic lazy list which returns the values in the order they complete.
-/
def runGreedily (tasks : List (TacticM α)) : MLList TacticM α :=
  .squash fun _ => return MLList.ofTaskList (← tasks.mapM asTask) |>.liftM.mapM id

end Lean.Elab.Tactic.TacticM
