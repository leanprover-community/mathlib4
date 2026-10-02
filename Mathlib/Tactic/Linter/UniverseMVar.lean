/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

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

/- (Probably) because of lean4#14574, trying to `import all` the next two definitions from
`Lean.Elab.BuiltinCommand` causes
interpreter crash. We copy their code instead.
Original license header for `typelessBinder?` and `containsId`:
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura -/

private def typelessBinder? : Syntax → Option (Array (TSyntax [`ident, `Lean.Parser.Term.hole]) × BinderInfo)
  | `(bracketedBinderF|($ids*))     => some (ids, .default)
  | `(bracketedBinderF|{$ids*})     => some (ids, .implicit)
  | `(bracketedBinderF|⦃$ids*⦄)     => some (ids, .strictImplicit)
  | `(bracketedBinderF|[$id:ident]) => some (#[id], .instImplicit)
  | _                               => none

/--  If `id` is an identifier, return true if `ids` contains `id`. -/
private def containsId (ids : Array (TSyntax [`ident, ``Parser.Term.hole])) (id : TSyntax [`ident, ``Parser.Term.hole]) : Bool :=
  id.raw.isIdent && ids.any fun id' => id'.raw.getId == id.raw.getId

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
      | .instImplicit => `(bracketedBinderF| [$(⟨binderId⟩)])

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
