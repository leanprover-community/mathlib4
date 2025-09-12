/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Elab.SyntheticMVars
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header

/-!
# Additions to `Lean.Elab.Tactic.Meta`
-/

namespace Lean.Elab
open Term

/-- Apply the given tactic code to `mvarId` in `MetaM`.

This is a variant of `Lean.Elab.runTactic` that forgets the final `Term.State`.
-/
def runTactic' (mvarId : MVarId) (tacticCode : Syntax) (ctx : Context := {}) (s : State := {}) :
    MetaM (List MVarId) := do
  instantiateMVarDeclMVars mvarId
  let go : TermElabM (List MVarId) :=
    withSynthesize do Tactic.run mvarId (Tactic.evalTactic tacticCode *> Tactic.pruneSolvedGoals)
  go.run' ctx s

end Lean.Elab
