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

Import this module and enable `set_option linter.droppableHypotheses true` to try deleting
each parameter of a `theorem` (including a `lemma` expanded to a theorem). Each trial replays
the unchanged proof from the command state *before* the original declaration. Section variables
are tested too. Grouped binders are tested one name at a time. Findings are independent: they
do not imply that all reported parameters can be removed simultaneously.

The linter uses a declaration elaborator hook to obtain the pre-declaration state. It preserves
the original theorem's elaboration options, uses synchronous elaboration for deletion trials,
and restores command state after every trial.
Trials disable auto-implicit parameters and recursive linting, reject errors and `sorry` (also
through auxiliary declarations), and check that the new type specializes to the old type by
reinserting one parameter. This last check prevents accepting a changed statement through name
capture or a change of instance. A failed or timed-out trial produces no warning.

Limitations: only named theorems are handled, not `example`, `def`, mutual declarations, or
parameters written inside the result type. Trials that remove additional automatically included
section parameters are conservatively rejected. A proof that needs editing is not detected.
Ambiguous binder alignment (e.g. repeated anonymous instances of a data-carrying class) is
conservatively rejected too.
Section parameters explicitly referenced by another remaining section binder are skipped:
deleting them would leave an invalid section telescope.

Command state is isolated, but arbitrary IO performed by elaborators or tactics is not undone.
This module is deliberately not imported by the default linter bundle.

The heartbeat limit is not a wall-clock timeout: some Lean operations do not check heartbeats.
In the full-library survey, `CategoryTheory/Sites/Descent/IsPrestack.lean` still timed out while
replaying `pullHom_pullHom` without its section category instance. Run large surveys in separate
processes with an external timeout. The dependent-section guard also avoids the universe-unifier
stack overflow reported in https://github.com/leanprover/lean4/issues/16125.
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

/-- Record individual trial phases in the audit file when diagnosing a failed replay. -/
register_option linter.droppableHypotheses.traceTrials : Bool := {
  defValue := false
  descr := "record individual droppable-hypothesis trial phases"
}

namespace DroppableHypotheses

initialize registerTraceClass `linter.droppableHypotheses

/-- One source edit to try, together with the scope in which to replay it. -/
private structure Trial where
  ref : Syntax
  binder : Syntax
  command : Syntax
  scope : Scope
  isSection : Bool := false
  dependentSectionBinder : Bool := false

/-- The individual names of a binder; an anonymous instance counts as one parameter. -/
private def binderNames (binder : Syntax) : Array Syntax :=
  if binder.isIdent || binder.isOfKind ``Parser.Term.hole then #[binder]
  else if binder.isOfKind ``Parser.Term.instBinder then #[binder]
  else if binder.isOfKind ``Parser.Term.explicitBinder ||
      binder.isOfKind ``Parser.Term.implicitBinder ||
      binder.isOfKind ``Parser.Term.strictImplicitBinder then binder[1].getArgs
  else #[]

/-- Delete one name from a grouped binder, or the entire binder if it has only one name. -/
private def dropName (binder : Syntax) (i : Nat) : Option Syntax :=
  if (binderNames binder).size == 1 then none
  else some <| binder.setArg 1 (mkNullNode <| binder[1].getArgs.eraseIdxIfInBounds i)

/-- Replace a binder, or remove it if its replacement is `none`. -/
private def editBinders (binders : Array Syntax) (i : Nat) (replacement : Option Syntax) :
    Array Syntax :=
  match replacement with
  | some binder => binders.set! i binder
  | none => binders.eraseIdxIfInBounds i

/-- Enumerate declaration parameters and section variables, without dropping a whole group. -/
private def trials (stx : Syntax) (scope : Scope) : Array Trial := Id.run do
  let mut result := #[]
  let sig := stx[1][2]
  let binders := sig[0].getArgs
  for binder in binders, i in *...binders.size do
    for ref in binderNames binder, j in *...(binderNames binder).size do
      let sig := sig.setArg 0 <| mkNullNode <| editBinders binders i (dropName binder j)
      result := result.push { ref, binder, command := stx.setArg 1 (stx[1].setArg 2 sig), scope }
  let mut uidIdx := 0
  for binder in scope.varDecls, i in *...scope.varDecls.size do
    for ref in binderNames binder, j in *...(binderNames binder).size do
      let uid := scope.varUIds[uidIdx + j]!
      let varDecls := editBinders (scope.varDecls.map (·.raw)) i (dropName binder j)
      -- Re-elaborating the whole section telescope with an explicitly referenced variable
      -- missing is invalid, even when the dependent binder is unused by this theorem.
      let name? := if ref.isIdent then some ref.getId
        else if binder.raw.isOfKind ``Parser.Term.instBinder && binder.raw[1][0].isIdent then
          some binder.raw[1][0].getId
        else none
      let dependentSectionBinder := name?.any fun name => varDecls.any fun remaining =>
        (remaining.getArgs.drop 2).any fun arg =>
          (arg.find? fun stx => stx.isIdent && stx.getId == name).isSome
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
        isSection := true
        dependentSectionBinder := dependentSectionBinder }
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
        if decl.binderInfo.isInstImplicit && decl.userName.hasMacroScopes &&
            bi.isInstImplicit && name.hasMacroScopes then
          -- Anonymous instance names can change when an earlier binder is removed. Align by
          -- type only when unambiguous, or when proof irrelevance makes the choice immaterial.
          unless ← Meta.isProp decl.type do
            for other in decls do
              if other.fvarId != decl.fvarId && (← Meta.isDefEq decl.type other.type) then
                compatible := false
        else
          if name != decl.userName || decls.any (fun other =>
              other.fvarId != decl.fvarId && other.userName == decl.userName) then
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

private def traceTrialPhase (phase : String) : CommandElabM Unit := do
  if linter.droppableHypotheses.traceTrials.get (← getOptions) then
    audit <| Json.mkObj [("event", toJson "trial_phase"), ("phase", toJson phase)]

/-- The outcome of an isolated replay; only successful trials carry a replacement type. -/
private structure TrialResult where
  status : String
  newType : String := ""

/-- Re-elaborate in an isolated command state. No declaration or diagnostic escapes a trial. -/
private def succeeds (before : State) (declName : Name) (original : Expr) (trial : Trial) :
    CommandElabM TrialResult := do
  if trial.dependentSectionBinder then return ⟨"dependent_section_binder", ""⟩
  let saved ← get
  try
    let opts := trial.scope.opts
      |>.setBool `autoImplicit false
      |>.setBool `Elab.async false
      |>.setBool `linter.all false
      |>.setBool `linter.droppableHypotheses false
      |>.set `maxHeartbeats (linter.droppableHypotheses.maxHeartbeats.get trial.scope.opts)
    set { before with
      messages := {}
      infoState := { enabled := false }
      snapshotTasks := #[]
      scopes := { trial.scope with opts } :: before.scopes.tail }
    withReader ({ · with snap? := none }) do
      traceTrialPhase "elaborate"
      elabDeclaration trial.command
      traceTrialPhase "check_errors"
      if (← get).messages.hasErrors then
        let heartbeat := (← get).messages.toArray.any fun m =>
          m.data.hasTag (· == `runtime.maxHeartbeats)
        return ⟨if heartbeat then "heartbeat_limit" else "elaboration_error", ""⟩
      let some info := (← getEnv).find? declName | return ⟨"missing_declaration", ""⟩
      traceTrialPhase "axioms"
      if (← collectAxioms declName).contains ``sorryAx then return ⟨"sorry", ""⟩
      traceTrialPhase "compare_types"
      unless ← liftTermElabM <| specializesToOriginal original info.type do
        return ⟨"statement_changed", ""⟩
      traceTrialPhase "pretty_type"
      let newType ← liftTermElabM do return toString (← Meta.ppExpr info.type)
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
  unless getLinterValue linter.droppableHypotheses (← getLinterOptions) do
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
  let mut findings : Array Json := #[]
  let mut outcomes : Std.HashMap String Nat := {}
  for (trial, index) in candidates.zipIdx do
    if linter.droppableHypotheses.traceTrials.get (← getOptions) then
      audit <| Json.mkObj [("event", toJson "trial_start"),
        ("declaration", toJson declName.toString), ("index", toJson index),
        ("binder", toJson <| trial.binder.reprint.getD ""),
        ("section", toJson trial.isSection)]
    let result ← succeeds before declName info.type trial
    if linter.droppableHypotheses.traceTrials.get (← getOptions) then
      audit <| Json.mkObj [("event", toJson "trial_done"), ("index", toJson index),
        ("status", toJson result.status)]
    outcomes := outcomes.insert result.status (outcomes.getD result.status 0 + 1)
    if result.status == "success" then
      let finding := Json.mkObj <| [
        ("binder", toJson <| trial.ref.reprint.getD ""),
        ("binderSyntax", toJson <| trial.binder.reprint.getD ""),
        ("binderStart", toJson <| (trial.binder.getPos?.map (·.byteIdx)).getD 0),
        ("binderEnd", toJson <| (trial.binder.getTailPos?.map (·.byteIdx)).getD 0),
        ("newType", toJson result.newType),
        ("section", toJson trial.isSection),
        ("byteOffset", toJson <| (trial.ref.getPos?.map (·.byteIdx)).getD 0)] ++ location
      findings := findings.push finding
      let originalType ← liftTermElabM do return toString (← Meta.ppExpr info.type)
      audit <| Json.mkObj [("event", toJson "finding"), ("finding", finding),
        ("originalType", toJson originalType)]
      let kind := if trial.isSection then "Section parameter" else "Parameter"
      logLint linter.droppableHypotheses trial.ref m!"\
        {kind} `{trial.ref}` can be dropped: \
        the declaration and its existing proof re-elaborate without it."
  audit <| Json.mkObj <| [
    ("event", toJson "declaration_done"),
    ("trials", toJson candidates.size),
    ("outcomes", Json.mkObj <| outcomes.toList.map fun (k, v) => (k, toJson v)),
    ("findings", toJson findings.size),
    ("milliseconds", toJson <| (← IO.monoMsNow) - started)] ++ location
  trace[linter.droppableHypotheses] "{Json.compress <| Json.mkObj [
    ("declaration", toJson declName.toString),
    ("trials", toJson candidates.size),
    ("findings", toJson findings)]}"

end DroppableHypotheses
end Mathlib.Linter
