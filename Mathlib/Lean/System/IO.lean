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
def IO.waitAny' (tasks : List (Task α)) (h : List.length tasks > 0 := by nonempty_list) :
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
