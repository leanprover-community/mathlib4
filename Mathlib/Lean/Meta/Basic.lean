/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Thomas Murrills
-/
import Lean.Meta.Basic

/-!
# Additions to `Lean.Meta.Basic`

Likely these already exist somewhere. Pointers welcome.
-/

/--
Restore the metavariable context after execution.
-/
def Lean.Meta.preservingMCtx (x : MetaM α) : MetaM α := do
  let mctx ← getMCtx
  try x finally setMCtx mctx

/-- Create an array of fresh level mvars. -/
def Lean.Meta.mkFreshLevelMVarsArray (n : Nat) : MetaM (Array Level) :=
  n.foldM (init := Array.mkEmpty (α := Level) n) fun _ acc => return acc.push (← mkFreshLevelMVar)
