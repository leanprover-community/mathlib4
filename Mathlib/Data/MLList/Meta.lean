/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.MLList.IO
import Mathlib.Data.List.Defs

/-!
# Parallelization in Lean's tactic monads.

`MetaM.runGreedily` will run a list of `MetaM α` in parallel, returning
* a cancellation hook and
* an `MLList MetaM α` that returns the results (and the relevant `MetaM` state)
  in the order that they finish.

After calling the cancellation hook the behaviour of the monadic lazy list should not be relied on.
It may continue returning values, or fail.
Recommended usage is to take a prefix of the list
(e.g. with `MLList.takeUpToFirst` followed by `MLList.force`, or `MLList.takeAsList`)
and then call the cancellation hook to request cancellation of later unwanted tasks.

(Similarly also for `CoreM`, `TermElabM`, and `TacticM`.)

## Implementation notes:
Calling `IO.cancel` on `t.map f` does not cancel `t`,
so we have to be careful throughout this file
to construct cancellation hooks connected to the underlying task,
rather than the various maps of it that we construct to pass state.
-/

set_option autoImplicit true

namespace IO

/--
Given a list of values in `IO α`, executes them all in parallel as tasks, and returns
* a cancellation hook and
* a monadic lazy list which returns the values in the order they complete.

Note that the cancellation hook merely requests cooperative cancellation:
the tasks must call `IO.checkCanceled` themselves.

After calling the cancellation hook the behaviour of the monadic lazy list should not be relied on.
It may continue returning values, or fail.
Recommended usage is to take a prefix of the list
(e.g. with `MLList.takeUpToFirst` followed by `MLList.force`, or `MLList.takeAsList`)
and then call the cancellation hook to request cancellation of later unwanted tasks.
-/
def runGreedily (tasks : List (IO α)) : IO (BaseIO Unit × MLList IO α) := do
  let t ← show BaseIO _ from (tasks.map IO.asTask).traverse id
  return (t.forM cancel, MLList.ofTaskList t |>.liftM |>.mapM fun
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{e}"))

/--
Variant of `IO.runGreedily` without a cancellation hook.
-/
def runGreedily' (tasks : List (IO α)) : MLList IO α :=
  .squash fun _ => (·.2) <$> runGreedily tasks

end IO

namespace Lean.Core.CoreM

/--
Given a monadic value in `CoreM`, creates a task that runs it in the current state,
returning
* a cancellation hook and
* a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : CoreM α) : CoreM (BaseIO Unit × Task (CoreM α)) := do
  let task ← (t.toIO (← read) (← get)).asTask
  return (IO.cancel task, task.map fun
  | .ok (a, s) => do set s; pure a
  | .error e => throwError m!"Task failed:\n{e}")

/--
Given a monadic value in `CoreM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask' (t : CoreM α) : CoreM (Task (CoreM α)) := (·.2) <$> asTask t

/--
Given a list of monadic values in `CoreM`, runs them all as tasks,
and returns
* a cancellation hook and
* the monadic lazy list which returns the values in the order they complete.

See the doc-string for `IO.runGreedily` for details about the cancellation hook behaviour.
-/
def runGreedily (jobs : List (CoreM α)) : CoreM (BaseIO Unit × MLList CoreM α) := do
  let (cancels, tasks) := (← jobs.mapM asTask).unzip
  return (cancels.forM id, .squash fun _ => return MLList.ofTaskList tasks |>.liftM.mapM id)

/--
Variant of `CoreM.runGreedily` without a cancellation hook.
-/
def runGreedily' (jobs : List (CoreM α)) : MLList CoreM α :=
  .squash fun _ => (·.2) <$> runGreedily jobs

end Lean.Core.CoreM

namespace Lean.Meta.MetaM

/--
Given a monadic value in `MetaM`, creates a task that runs it in the current state,
returning
* a cancellation hook and
* a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : MetaM α) : MetaM (BaseIO Unit × Task (MetaM α)) := do
  let (cancel, task) ← (t.run (← read) (← get)).asTask
  return (cancel, task.map fun c : CoreM (α × Meta.State) => do let (a, s) ← c; set s; pure a)

/--
Given a monadic value in `MetaM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask' (t : MetaM α) : MetaM (Task (MetaM α)) := (·.2) <$> asTask t

/--
Given a list of monadic values in `MetaM`, runs them all as tasks,
and returns
* a cancellation hook and
* the monadic lazy list which returns the values in the order they complete.

See the doc-string for `IO.runGreedily` for details about the cancellation hook behaviour.
-/
def runGreedily (jobs : List (MetaM α)) : MetaM (BaseIO Unit × MLList MetaM α) := do
  let (cancels, tasks) := (← jobs.mapM asTask).unzip
  return (cancels.forM id, .squash fun _ => return MLList.ofTaskList tasks |>.liftM.mapM id)

/--
Variant of `MetaM.runGreedily` without a cancellation hook.
-/
def runGreedily' (jobs : List (MetaM α)) : MLList MetaM α :=
  .squash fun _ => (·.2) <$> runGreedily jobs


end Lean.Meta.MetaM

namespace Lean.Elab.Term.TermElabM

/--
Given a monadic value in `TermElabM`, creates a task that runs it in the current state,
returning
* a cancellation hook and
* a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : TermElabM α) : TermElabM (BaseIO Unit × Task (TermElabM α)) := do
  let (cancel, task) ← (t.run (← read) (← get)).asTask
  return (cancel, task.map fun c : MetaM (α × Term.State) => do let (a, s) ← c; set s; pure a)

/--
Given a monadic value in `TermElabM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask' (t : TermElabM α) : TermElabM (Task (TermElabM α)) := (·.2) <$> asTask t

/--
Given a list of monadic values in `TermElabM`, runs them all as tasks,
and returns
* a cancellation hook and
* the monadic lazy list which returns the values in the order they complete.

See the doc-string for `IO.runGreedily` for details about the cancellation hook behaviour.
-/
def runGreedily (jobs : List (TermElabM α)) : TermElabM (BaseIO Unit × MLList TermElabM α) := do
  let (cancels, tasks) := (← jobs.mapM asTask).unzip
  return (cancels.forM id, .squash fun _ => return MLList.ofTaskList tasks |>.liftM.mapM id)

/--
Variant of `TermElabM.runGreedily` without a cancellation hook.
-/
def runGreedily' (jobs : List (TermElabM α)) : MLList TermElabM α :=
  .squash fun _ => (·.2) <$> runGreedily jobs

end Lean.Elab.Term.TermElabM

namespace Lean.Elab.Tactic.TacticM

/--
Given a monadic value in `TacticM`, creates a task that runs it in the current state,
returning
* a cancellation hook and
* a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : TacticM α) : TacticM (BaseIO Unit × Task (TacticM α)) := do
  let (cancel, task) ← (t (← read) |>.run (← get)).asTask
  return (cancel, task.map fun c : TermElabM (α × Tactic.State) => do let (a, s) ← c; set s; pure a)

/--
Given a monadic value in `TacticM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask' (t : TacticM α) : TacticM (Task (TacticM α)) := (·.2) <$> asTask t

/--
Given a list of monadic values in `TacticM`, runs them all as tasks,
and returns
* a cancellation hook and
* the monadic lazy list which returns the values in the order they complete.

See the doc-string for `IO.runGreedily` for details about the cancellation hook behaviour.
-/
def runGreedily (jobs : List (TacticM α)) : TacticM (BaseIO Unit × MLList TacticM α) := do
  let (cancels, tasks) := (← jobs.mapM asTask).unzip
  return (cancels.forM id, .squash fun _ => return MLList.ofTaskList tasks |>.liftM.mapM id)

/--
Variant of `TacticM.runGreedily` without a cancellation hook.
-/
def runGreedily' (jobs : List (TacticM α)) : MLList TacticM α :=
  .squash fun _ => (·.2) <$> runGreedily jobs

end Lean.Elab.Tactic.TacticM
