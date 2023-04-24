/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.List.Indexes

/-!
# Wrapper for `IO.waitAny` that also returns the remaining tasks.
-/

local macro "nonempty_list" : tactic =>
  `(tactic| exact Nat.zero_lt_succ _)

/--
Given a non-empty list of tasks, wait for the first to complete.
Return the value and the list of remaining tasks.
-/
def IO.waitAny' (tasks : List (Task α)) (h : List.length tasks > 0 := by nonempty_list) :
    BaseIO (α × List (Task α)) := do
  let (i, a) ← IO.waitAny
    (tasks.mapIdx fun i t => t.map fun a => (i, a))
    ((tasks.length_mapIdx _).symm ▸ h)
  return (a, tasks.eraseIdx i)
