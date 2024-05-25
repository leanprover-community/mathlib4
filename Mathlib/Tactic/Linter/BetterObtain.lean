/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-! ## Attempt to remove stream-of-conciousness syntax from `obtain`

Create a clone `myobtain` which requires a proof directly.

On second thought, just write a linter against it... -/

open Lean Elab

namespace Mathlib.Linter.Style

/-- Whether a syntax element is an `obtain` tactic call without a provided proof. -/
def is_obtain_without_proof : Syntax → Bool
  -- Cases with a proof.
  | `(tactic|obtain $_pat := $_proof) => false
  | `(tactic|obtain $_pat : $_type := $_proof) => false
  | `(tactic|obtain : $_type := $_proof) => false
  | `(tactic|obtain := $_proof) => false
  -- Case without a proof.
  | `(tactic|obtain : $_type) => true
  | `(tactic|obtain $_pat : $_type) => true
  -- The above should be all possible `obtain` pattern: to double-check, let's flag any others.
  | `(tactic|obtain _) => true
  | _ => false

/-- The `badObtain` linter emits a warning upon uses of "stream-of-conciousness" obtain,
i.e. with the proof postponed. -/
register_option linter.badObtain : Bool := {
  defValue := true
  descr := "enable the `badObtain` linter"
}

/-- Gets the value of the `linter.badObtain` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.badObtain o

/-- The `badObtain` linter: this lints ...
why bad?
what else?
-/
def badObtainLinter : Linter where run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    if let some ((head, _n)::_chain) := stx.findStack? (fun _ ↦ true) is_obtain_without_proof then
      Linter.logLint linter.badObtain head m!"Bad obtain syntax; please remove"

initialize addLinter badObtainLinter
