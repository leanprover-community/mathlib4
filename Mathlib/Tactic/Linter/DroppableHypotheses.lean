/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import Lean.Elab.Declaration
public meta import Lean.Linter.Basic
public meta import Lean.Util.CollectAxioms
public import Mathlib.Init

/-!
# Droppable hypothesis linter

Lean's unused-variable linter detects parameters unused by the existing proof. A parameter can
be used yet redundant: `infer_instance` can derive `Nonempty α` from `[Inhabited α]`.
This linter finds such cases by deleting one parameter and re-elaborating the unchanged statement
and proof. Enable it with `set_option linter.droppableHypotheses true` after importing this module.

Only named theorems and lemmas are checked, including section variables and grouped binders.
Binders inside the return type are not tried.
Findings are independent; individually removable parameters may not all be removable together.
Trials restore command state, disable auto-implicit parameters and recursive linting, reject
`sorry` dependencies, and check that reinserting one parameter recovers the original statement.
Explicitly dependent section binders are conservatively skipped.
Arbitrary IO performed by elaborators or tactics is not undone.

This linter is expensive and requires explicit enabling, even with `linter.all true`.
Heartbeats do not bound every Lean operation, so large surveys need an external process timeout.
-/

public meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- Replay theorem declarations with each parameter individually removed. Expensive and opt-in. -/
register_option linter.droppableHypotheses : Bool := {
  defValue := false
  descr := "try re-elaborating theorem declarations after dropping each parameter"
}

/-- The heartbeat limit for each individual replay, in Lean's usual heartbeat units. -/
register_option linter.droppableHypotheses.maxHeartbeats : Nat := {
  defValue := 200000
  descr := "heartbeat limit for each droppable-hypothesis trial"
}

/-- Append structured progress and findings to this JSONL file, if nonempty. -/
register_option linter.droppableHypotheses.outputFile : String := {
  defValue := ""
  descr := "JSONL audit file for the droppable-hypothesis linter"
}

namespace DroppableHypotheses

/-- One source edit to try, together with the scope in which to replay it. -/
private structure Trial where
  ref : Syntax
  binder : Syntax
  command : Syntax
  scope : Scope
  isSection : Bool := false

/-- The individual names of a binder; an anonymous instance counts as one parameter. -/
private def binderNames (binder : Syntax) : Array Syntax :=
  if binder.isIdent || binder.isOfKind ``Parser.Term.hole ||
      binder.isOfKind ``Parser.Term.instBinder then #[binder]
  else if binder.isOfKind ``Parser.Term.explicitBinder ||
      binder.isOfKind ``Parser.Term.implicitBinder ||
      binder.isOfKind ``Parser.Term.strictImplicitBinder then binder[1].getArgs
  else #[]

/-- Delete one name from a grouped binder, or its entire binder if it has only one name. -/
private def eraseName (binders : Array Syntax) (i j : Nat) : Array Syntax :=
  let binder := binders[i]!
  if (binderNames binder).size == 1 then binders.eraseIdxIfInBounds i
  else binders.set! i <| binder.setArg 1 (mkNullNode <| binder[1].getArgs.eraseIdxIfInBounds j)

/-- Enumerate declaration parameters and section variables, without dropping a whole group. -/
private def trials (stx : Syntax) (scope : Scope) : Array Trial := Id.run do
  let mut result := #[]
  let sig := stx[1][2]
  let binders := sig[0].getArgs
  for binder in binders, i in *...binders.size do
    for ref in binderNames binder, j in *...(binderNames binder).size do
      let sig := sig.setArg 0 <| mkNullNode <| eraseName binders i j
      result := result.push { ref, binder, command := stx.setArg 1 (stx[1].setArg 2 sig), scope }
  let mut uidIdx := 0
  for binder in scope.varDecls, i in *...scope.varDecls.size do
    for ref in binderNames binder, j in *...(binderNames binder).size do
      let uid := scope.varUIds[uidIdx + j]!
      let varDecls := eraseName (scope.varDecls.map (·.raw)) i j
      -- Re-elaborating the whole section telescope with an explicitly referenced variable
      -- missing is invalid, even when the dependent binder is unused by this theorem.
      -- It can also trigger https://github.com/leanprover/lean4/issues/16125.
      let name? := if ref.isIdent then some ref.getId
        else if binder.raw.isOfKind ``Parser.Term.instBinder && binder.raw[1][0].isIdent then
          some binder.raw[1][0].getId
        else none
      if name?.any (fun name => varDecls.any fun remaining =>
          (remaining.getArgs.drop 2).any fun arg =>
            (arg.find? fun stx => stx.isIdent && stx.getId == name).isSome) then continue
      let scope := { scope with
        varDecls := varDecls.map (⟨·⟩)
        varUIds := scope.varUIds.eraseIdxIfInBounds (uidIdx + j)
        includedVars := scope.includedVars.filter (· != uid)
        omittedVars := scope.omittedVars.filter (· != uid) }
      result := result.push {
        ref := ref
        binder := binder
        command := stx
        scope := scope
        isSection := true }
    uidIdx := uidIdx + (binderNames binder).size
  return result

/-- Check that reinserting one original parameter recovers the original statement.
In particular, deleting a variable must not silently resolve its name to a global constant. -/
private def specializesToOriginal (original replay : Expr) : MetaM Bool :=
  Meta.forallTelescope original fun xs conclusion => do
    if replay.getNumHeadForalls + 1 != xs.size then return false
    let decls ← xs.mapM Meta.getFVarLocalDecl
    for dropped in *...xs.size do
      let mut type := replay
      let mut compatible := true
      for x in xs, i in *...xs.size do
        if i == dropped then continue
        let .forallE name domain body bi := type | compatible := false; break
        let decl := decls[i]!
        -- Anonymous instance names can change when an earlier binder is removed.
        unless (decl.binderInfo.isInstImplicit && decl.userName.hasMacroScopes &&
            bi.isInstImplicit && name.hasMacroScopes) ||
            name.eraseMacroScopes == decl.userName.eraseMacroScopes do
          compatible := false
        unless compatible do break
        unless ← Meta.isDefEq domain (← Meta.inferType x) do
          compatible := false
          break
        type := body.instantiate1 x
      if compatible && (← Meta.isDefEq type conclusion) then return true
    return false

/-- Persist an audit record immediately, including during commands that later time out. -/
private def audit (record : Json) : CommandElabM Unit := do
  let path := linter.droppableHypotheses.outputFile.get (← getOptions)
  unless path.isEmpty do
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn record.compress
    handle.flush

/-- An isolated replay's status and, when auditing, its replacement type. -/
private structure TrialResult where
  status : String
  newType : String := ""

/-- Re-elaborate in an isolated command state. No declaration or diagnostic escapes a trial. -/
private def succeeds (before : State) (declName : Name) (original : Expr) (trial : Trial) :
    CommandElabM TrialResult := do
  let saved ← get
  try
    -- Finish the trial proof before inspecting errors or discarding its snapshot tasks.
    let opts := trial.scope.opts
      |>.setBool `autoImplicit false
      |>.setBool `warningAsError false
      |>.setBool `Elab.async false
      |>.setBool `linter.droppableHypotheses false
      |>.set `maxHeartbeats (linter.droppableHypotheses.maxHeartbeats.get trial.scope.opts)
    set { before with
      messages := {}
      infoState := { enabled := false }
      snapshotTasks := #[]
      scopes := { trial.scope with opts } :: before.scopes.tail }
    withReader ({ · with snap? := none }) do
      elabDeclaration trial.command
      if (← get).messages.hasErrors then
        let heartbeat := (← get).messages.toArray.any fun m =>
          m.data.hasTag (· == `runtime.maxHeartbeats)
        return ⟨if heartbeat then "heartbeat_limit" else "elaboration_error", ""⟩
      let some info := (← getEnv).find? declName | return ⟨"missing_declaration", ""⟩
      if (← collectAxioms declName).contains ``sorryAx then return ⟨"sorry", ""⟩
      unless ← liftTermElabM <| specializesToOriginal original info.type do
        return ⟨"statement_changed", ""⟩
      let newType ← if (linter.droppableHypotheses.outputFile.get (← getOptions)).isEmpty then
        pure ""
        else liftTermElabM do return toString (← Meta.ppExpr info.type)
      return ⟨"success", newType⟩
  catch ex =>
    if ex.isInterrupt then throw ex
    return ⟨if ex.isMaxHeartbeat then "heartbeat_limit"
      else if ex.isMaxRecDepth then "recursion_limit" else "exception", ""⟩
  finally
    set saved

/-- Capture the state before adding a theorem, then run isolated deletion trials. -/
@[command_elab Lean.Parser.Command.declaration]
def elabWithDroppableHypotheses : CommandElab := fun stx => do
  unless linter.droppableHypotheses.get (← getOptions) do
    throwUnsupportedSyntax
  unless stx[1].isOfKind ``Parser.Command.theorem do
    throwUnsupportedSyntax
  let before ← get
  let scope ← getScope
  -- Preserve normal elaboration, including asynchronous handling of private declarations.
  -- `collectAxioms` below waits for the original proof's checked environment.
  elabDeclaration stx
  if (← get).messages.hasErrors then return
  -- Protected declarations are not resolvable by their short names, even in their namespace.
  let id := stx[1][1][0]
  let currNamespace ← getCurrNamespace
  let fullName := if (`_root_).isPrefixOf id.getId then
    id.getId.replacePrefix `_root_ .anonymous
    else currNamespace ++ id.getId
  let declName ← resolveGlobalConstNoOverload (mkIdentFrom id (`_root_ ++ fullName))
  if (← collectAxioms declName).contains ``sorryAx then return
  let some info := (← getEnv).find? declName | return
  let candidates := trials stx scope
  let started ← IO.monoMsNow
  let location := [
    ("declaration", toJson declName.toString),
    ("declarationStart", toJson <| (stx.getPos?.map (·.byteIdx)).getD 0),
    ("declarationEnd", toJson <| (stx.getTailPos?.map (·.byteIdx)).getD 0)]
  audit <| Json.mkObj <| [("event", toJson "declaration_start"),
    ("trials", toJson candidates.size)] ++ location
  let auditing := !(linter.droppableHypotheses.outputFile.get (← getOptions)).isEmpty
  let mut originalType : Option String := none
  let mut findings := 0
  let mut outcomes : Std.HashMap String Nat := {}
  for (trial, index) in candidates.zipIdx do
    if auditing then
      audit <| Json.mkObj [("event", toJson "trial_start"),
        ("declaration", toJson declName.toString), ("index", toJson index),
        ("binder", toJson <| trial.binder.reprint.getD ""),
        ("section", toJson trial.isSection)]
    let result ← succeeds before declName info.type trial
    if auditing then
      audit <| Json.mkObj [("event", toJson "trial_done"), ("index", toJson index),
        ("status", toJson result.status)]
    outcomes := outcomes.insert result.status (outcomes.getD result.status 0 + 1)
    if result.status == "success" then
      findings := findings + 1
      if auditing then
        if originalType.isNone then
          originalType := some (← liftTermElabM do return toString (← Meta.ppExpr info.type))
        let finding := Json.mkObj <| [
          ("binder", toJson <| trial.ref.reprint.getD ""),
          ("binderSyntax", toJson <| trial.binder.reprint.getD ""),
          ("binderStart", toJson <| (trial.binder.getPos?.map (·.byteIdx)).getD 0),
          ("binderEnd", toJson <| (trial.binder.getTailPos?.map (·.byteIdx)).getD 0),
          ("newType", toJson result.newType),
          ("section", toJson trial.isSection),
          ("byteOffset", toJson <| (trial.ref.getPos?.map (·.byteIdx)).getD 0)] ++ location
        audit <| Json.mkObj [("event", toJson "finding"), ("finding", finding),
          ("originalType", toJson <| originalType.getD "")]
      let kind := if trial.isSection then "Section parameter" else "Parameter"
      logLint linter.droppableHypotheses trial.ref m!"\
        {kind} `{trial.ref}` can be dropped: \
        the declaration and its existing proof re-elaborate without it."
  audit <| Json.mkObj <| [
    ("event", toJson "declaration_done"),
    ("trials", toJson candidates.size),
    ("outcomes", Json.mkObj <| outcomes.toList.map fun (k, v) => (k, toJson v)),
    ("findings", toJson findings),
    ("milliseconds", toJson <| (← IO.monoMsNow) - started)] ++ location
end DroppableHypotheses
end Mathlib.Linter
