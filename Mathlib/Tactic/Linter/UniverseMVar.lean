/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

meta import all Lean.Elab.BuiltinCommand
meta import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep
import Lean.Message

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- Lint on `variable (foo : Bar)`, and emits a warning if `Bar` has
universe metavariables in its type. -/
public register_option linter.universeMVarInVariable : Bool :=
  { defValue := true
    descr := "enable the universeMVarInVariable linter" }

namespace universeMVarInVariableLinter

open Meta Term Parser.Term

/-- Open scopes and remove the binders that are binder updates. -/
private def pruneUpdate (binder : TSyntax ``Parser.Term.bracketedBinder) :
    CommandElabM (Array (TSyntax ``Parser.Term.bracketedBinder)) := do
  let some (binderIds, binderInfo) := typelessBinder? binder | return #[binder]
  let varDecls := (← getScope).varDecls
  let mut binderIds := binderIds
  -- Go through declarations in reverse to respect shadowing
  for varDecl in varDecls.reverse do
    let ids ← match varDecl with
      | `(bracketedBinderF|($ids* $[: $_]? $(_)?)) => pure ids
      | `(bracketedBinderF|{$ids* $[: $_]?}) => pure ids
      | `(bracketedBinderF|⦃$ids* $[: $_]?⦄) => pure ids
      | `(bracketedBinderF|[$id : $_]) => pure #[⟨id⟩]
      | _ => continue
    binderIds := binderIds.filter fun id' => ¬ containsId ids id'
  binderIds.mapM fun binderId =>
    match binderInfo with
      | .default => `(bracketedBinderF| ($binderId))
      | .implicit => `(bracketedBinderF| {$binderId})
      | .strictImplicit => `(bracketedBinderF| {{$binderId}})
      | .instImplicit => throwUnsupportedSyntax

open Meta Term in
/-- Lint on `variable (foo : Bar)`, and emits a warning if `Bar` has
universe metavariables in its type. -/
def universeMVarInVariable : Linter where run := withSetOptionIn fun stx => do
  match stx with
  | `(variable $[$x:bracketedBinder]*)
  | `(variable $[$x:bracketedBinder]* in $t) =>
    let y ← x.flatMapM pruneUpdate
    runTermElabM <| fun f ↦ elabBindersEx y fun b => do
      for (stx, e) in b do
      let v ← instantiateMVars <| ← inferType e
      if v.hasLevelMVar then
        logLint linter.universeMVarInVariable stx
          m!"type of variable contains universe metavariable! {v}"
  | _ => return

initialize addLinter universeMVarInVariable

end universeMVarInVariableLinter

end Mathlib.Linter
