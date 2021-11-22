/-
Copyright (c) 2018 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
import Lean.Elab.SyntheticMVars
open Lean Elab Tactic

unsafe def evalRunTacUnsafe (term : Syntax) : TacticM Unit := do
  let term ← `(show TacticM Unit from discard do $term)
  let n := `_runTac
  let type := mkApp (mkConst ``TacticM) (mkConst ``Unit)
  let e ← Term.elabTermEnsuringType term type
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← Meta.instantiateMVars e
  let decl := Declaration.defnDecl {
    name        := n
    levelParams := []
    type        := type
    value       := e
    hints       := ReducibilityHints.opaque
    safety      := DefinitionSafety.safe
  }
  Term.ensureNoUnassignedMVars decl
  let env ← getEnv
  let tac ← try
    addAndCompile decl
    evalConst (TacticM Unit) n
  finally
    setEnv env
  tac

@[implementedBy evalRunTacUnsafe]
constant evalRunTac : Syntax → TacticM Unit

elab "runTac" e:doSeq : tactic => evalRunTac e
