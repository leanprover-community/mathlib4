/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Lean.Elab.Command

set_option linter.unusedVariables false

elab "#adaptation_note " str:str : command => pure ()

elab "#adaptation_note " str:str ppLine e:term : term =>
  Lean.Elab.Term.elabTerm e none

elab "#adaptation_note " str:str : tactic => pure ()

#adaptation_note "This is a test"

example : 1 = 1 :=
  #adaptation_note "This is a test"
  rfl

example : 1 = 1 := by
  #adaptation_note "This is a test"
  rfl




  -- withoutModifyingEnv <| Command.runTermElabM fun _ => do
  -- let (heading, e) ← try
  --   -- Adapted from `#check` implementation
  --   let theoremName : Name ← resolveGlobalConstNoOverloadWithInfo stx
  --   addCompletionInfo <| .id stx theoremName (danglingDot := false) {} none
  --   let decl ← getConstInfo theoremName
  --   let c : Expr := .const theoremName (decl.levelParams.map mkLevelParam)
  --   pure (m!"{ppConst c} : {decl.type}", decl.value!)
  -- catch _ =>
  --   let e ← Term.elabTerm stx none
  --   Term.synthesizeSyntheticMVarsNoPostponing
  --   let e ← Term.levelMVarToParam (← instantiateMVars e)
  --   pure (m!"{e} : {← Meta.inferType e}", e)
  -- unless e.isSyntheticSorry do
  --   let entries ← explode e
  --   let fitchTable : MessageData ← entriesToMessageData entries
  --   logInfo <|← addMessageContext m!"{heading}\n\n{fitchTable}\n"
