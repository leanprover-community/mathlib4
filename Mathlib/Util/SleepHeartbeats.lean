/-
Copyright (c) 2023 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Mathlib.Init
import Lean.Elab.Tactic.Basic

/-!
# Defines `sleep_heartbeats` tactic.

This is useful for testing / debugging long running commands or elaboration in a somewhat precise
manner.
-/
open Lean Elab

/-- A low level command to sleep for at least a given number of heartbeats by running in a loop
until the desired number of heartbeats is hit.
Warning: this function relies on interpreter / compiler
behaviour that is not guaranteed to function in the way that is relied upon here.
As such this function is not to be considered reliable, especially after future updates to Lean.
This should be used with caution and basically only for demo / testing purposes
and not in compiled code without further testing. -/
def sleepAtLeastHeartbeats (n : Nat) : IO Unit := do
  let i ← IO.getNumHeartbeats
  while (← IO.getNumHeartbeats) < i + n do
    continue

/-- do nothing for at least n heartbeats -/
elab "sleep_heartbeats " n:num : tactic => do
  match Syntax.isNatLit? n with
  | none    => throwIllFormedSyntax
  /-
  We multiply by `1000` to convert the user-facing heartbeat count to the
  internal heartbeat counter used by `IO.getNumHeartbeats`.
  -/
  | some m => sleepAtLeastHeartbeats (m * 1000)

example : 1 = 1 := by
  sleep_heartbeats 1000
  rfl
