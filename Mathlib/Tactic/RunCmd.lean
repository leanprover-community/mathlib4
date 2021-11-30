/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean

/-!
Define a `run_cmd a; b` command which executes code in `CoreM Unit`.
This is almost the same as `#eval show CoreM Unit from do a; b`,
except that it doesn't print an empty diagnostic.
-/

namespace Lean.Parser.Command
open Meta Elab.Command Elab

unsafe def elabRunCmdUnsafe : CommandElab := fun e => do
  let n := `_runCmd
  runTermElabM (some n) fun _ => do
    let e ← Term.elabTerm e none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← withLocalDeclD `env (mkConst ``Lean.Environment) fun env =>
      withLocalDeclD `opts (mkConst ``Lean.Options) fun opts => do
        let e ← mkAppM ``Lean.runMetaEval #[env, opts, e]
        mkLambdaFVars #[env, opts] e
    let env ← getEnv
    let opts ← getOptions
    let act ← try
      let type ← inferType e
      let decl := Declaration.defnDecl {
        name        := n
        levelParams := []
        type        := type
        value       := e
        hints       := ReducibilityHints.opaque
        safety      := DefinitionSafety.unsafe }
      Term.ensureNoUnassignedMVars decl
      addAndCompile decl
      evalConst (Environment → Options → IO (String × Except IO.Error Environment)) n
    finally setEnv env
    match (← act env opts).2 with
    | Except.error e => throwError e.toString
    | Except.ok env  => setEnv env

@[implementedBy elabRunCmdUnsafe] constant elabRunCmd : CommandElab

elab (name := runCmd) "run_cmd " elems:doSeq : command => do
  elabRunCmd <|<- `((do $elems : CoreM Unit))
