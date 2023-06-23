/-
Copyright (c) 2023 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Lean

/-!
# Defines `sleep_heartbeats` tactic.

This is useful for testing / debugging long running commands or elaboration in a somewhat precise
manner.
-/
open Lean Elab

/-- A low level command to sleep for at least a given number of heartbeats by running in a loop
  until the desired number of heartbeats is hit. -/
def sleepAtLeastHeartbeats (n : Nat) : IO Unit := do
  let i ← IO.getNumHeartbeats
  while (← IO.getNumHeartbeats) < i + n do
    continue

/-- do nothing for at least n heartbeats -/
elab "sleep_heartbeats " n:num : tactic => do
  match Syntax.isNatLit? n with
  | none    => throwIllFormedSyntax
  /- as this is a user facing command we multiply the user input by 1000 to match the maxHeartbeats
     option -/
  | some m => sleepAtLeastHeartbeats (m * 1000)

example : 1 = 1 := by
  sleep_heartbeats 1000
  rfl
