/-
Copyright (c) 2026 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public import Mathlib.Tactic.ApplyRuleSets.Core
public import Mathlib.Tactic.FunProp.Decl
import Qq

/-!
# The `apply_rulesets` tactic

This file defines tactic elaboration for a configurable backward-search tactic using named rulesets.
Rulesets contain theorem rules and procedural rules (`ruleproc`s) in one ordered database.
-/

public meta section

namespace Mathlib
namespace Tactic.ApplyRuleSets

open Lean Meta Elab Tactic Term
open Lean.Parser.Tactic

open Parser.Tactic in
syntax applyRuleSetErase := "-" term:max
syntax applyRuleSetArg := applyRuleSetErase <|> term
syntax applyRuleSetArgs := "[" applyRuleSetArg,* "]"

/-- Config elaborator for `apply_rulesets`. -/
declare_config_elab elabApplyRuleSetsConfig Config

syntax (name := applyRuleSetsTac) "apply_rulesets" optConfig (discharger)?
  (ppSpace applyRuleSetArgs)? : tactic
syntax (name := applyRuleSetsQuestionTac) "apply_rulesets?" optConfig (discharger)?
  (ppSpace applyRuleSetArgs)? : tactic

open Parser.Tactic in
private def parseApplyRuleSetArgs (args : TSyntax ``applyRuleSetArgs) :
    Array (TSyntax ``applyRuleSetArg) :=
  match args with
  | `(applyRuleSetArgs| [$xs,*]) => xs.getElems
  | _ => #[]

open Mathlib.Meta.FunProp in
private def tacticDischarger (d? : Option (TSyntax ``Parser.Tactic.discharger)) :
    TacticM (ArgOrigin → Expr → MetaM (Option Expr)) := do
  match d? with
  | none => return fun _ _ => pure none
  | some d =>
    match d with
    | `(discharger| (discharger := $tac)) =>
      let disch := Mathlib.Meta.FunProp.tacticToDischarge (← `(tactic| ($tac)))
      return fun _ e => disch e
    | _ => return fun _ _ => pure none

open Lean Meta in
private partial def leadingIndent (source : String) (pos : String.Pos.Raw) : String :=
  let rec go (i : String.Pos.Raw) : String.Pos.Raw :=
    if i.atEnd source then
      i
    else
      let c := i.get source
      if c == ' ' || c == '\t' then
        go (i.next source)
      else
        i
  String.Pos.Raw.extract source pos (go pos)

open Lean.Meta.Tactic.TryThis in
def addHaveSuggestions (ref : Syntax) (goals : Array Expr) : TacticM Unit := do
  let some refRange := ref.getRange? | return
  let fileMap ← getFileMap
  let lineStart := fileMap.lineStart (fileMap.toPosition refRange.start).line
  let source := fileMap.source
  let insertionRange : Syntax.Range := ⟨lineStart, lineStart⟩

  let indent := leadingIndent source lineStart
  let mut collected : ExprSet := {}
  let mut suggestions : Array Suggestion := #[]
  for goal in goals do
    if !collected.contains goal then
      collected := collected.insert goal
      let code := s!"have : {← ppExpr goal} := sorry"
      let suggestion : Suggestion := {
        suggestion := .string s!"{indent}{code}\n"
        toCodeActionTitle? := some fun _ => code
      }
      suggestions := suggestions.push suggestion
  addSuggestions ref suggestions (origSpan? := some (Syntax.ofRange insertionRange))
    (header := "Code action:")

private def explicitRuleId (order : Nat) : Name :=
  `apply_rulesets.explicit ++ Name.num Name.anonymous order

private def explicitOrigin (order : Nat) (ref : Syntax) (expr : Expr) : Origin :=
  match expr with
  | .fvar fvarId => .fvar fvarId
  | _ =>
    match expr.constName? with
    | some declName => .decl declName
    | none => .stx (explicitRuleId order) ref

private def mkExplicitExprRule (origin : Origin) (order : Nat) (ref : Term) (e : Expr) :
    TacticM Rule := do
  let (e, pattern, levelParams) ←
    if e.isLambda then
      pure (e, ← inferType e, #[])
    else
      let e ← abstractMVars e
      pure (e.expr, ← inferType e.expr, e.paramNames)
  let rule : Rule := { origin, type := .expr e, pattern, levelParams, order }
  if rule.hasExprMVar then
    throwErrorAt ref "explicit rule contains expression metavariables"
  return rule

private def evalApplyRuleSetsCore (cfgStx : TSyntax ``Parser.Tactic.optConfig)
    (d? : Option (TSyntax ``Parser.Tactic.discharger))
    (argsStx? : Option (TSyntax ``applyRuleSetArgs)) (forceCollectFailedSubgoals : Bool) :
    TacticM Unit := do
  let cfg ← elabApplyRuleSetsConfig cfgStx
  let cfg :=
    if forceCollectFailedSubgoals then
      { cfg with collectFailedSubgoals := true }
    else
      cfg
  let disch ← tacticDischarger d?
  let args := argsStx?.map parseApplyRuleSetArgs |>.getD #[]
  let mut rulesets := #[]
  let mut explicitTerms : Array Term := #[]
  let mut erased : Std.HashSet Name := {}
  for arg in args do
    match arg with
    | `(applyRuleSetArg| - $t:term) =>
      match t.raw with
      | .ident .. => erased := erased.insert (← realizeGlobalConstNoOverload t.raw)
      | _ => throwErrorAt t "apply_rulesets only supports removals by name"
    | `(applyRuleSetArg| $t:term) =>
      match t.raw with
      | .ident _ _ val _ =>
        if ← isRuleSetName val then
          rulesets := rulesets.push val
        else
          explicitTerms := explicitTerms.push t
      | _ => explicitTerms := explicitTerms.push t
    | _ => throwUnsupportedSyntax
  withMainContext do
    let goal ← getMainGoal
    let goalType ← goal.getType
    let mut explicitRules := #[]
    for h : i in [:explicitTerms.size] do
      let e ← Term.elabTerm explicitTerms[i].raw none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let origin := explicitOrigin i explicitTerms[i].raw e
      if let some rule ← explicitRuleProcRule? origin e then
        explicitRules := explicitRules.push { rule with order := i }
      else
        explicitRules := explicitRules.push (← mkExplicitExprRule origin i explicitTerms[i] e)
    Term.synthesizeSyntheticMVarsNoPostponing
    let ctx : Context :=
      { config := cfg,
        rulesets := rulesets,
        explicitRules := explicitRules,
        erased := erased,
        disch := disch
        lctxInitIndices := (← getLCtx).numIndices }
    let s : State := { goalCaches := #[{ minLctxIndex := (← getLCtx).numIndices }] }
    let (proof?, s) ← (applyRuleSets { ruleName := Name.anonymous } goalType).run ctx |>.run s
    match proof? with
    | some proof => goal.assign proof; replaceMainGoal []
    | none =>
      unless cfg.collectFailedSubgoals do
        throwError "apply_rulesets failed"
      addHaveSuggestions (← getRef) s.failedSubgoals

@[tactic applyRuleSetsTac]
def evalApplyRuleSets : Tactic := fun stx => do
  let `(tactic| apply_rulesets $cfgStx:optConfig $[$d?]? $[$argsStx?:applyRuleSetArgs]?) := stx
    | throwUnsupportedSyntax
  evalApplyRuleSetsCore cfgStx d? argsStx? (forceCollectFailedSubgoals := false)

@[tactic applyRuleSetsQuestionTac]
def evalApplyRuleSetsQuestion : Tactic := fun stx => do
  let `(tactic| apply_rulesets? $cfgStx:optConfig $[$d?]? $[$argsStx?:applyRuleSetArgs]?) := stx
    | throwUnsupportedSyntax
  evalApplyRuleSetsCore cfgStx d? argsStx? (forceCollectFailedSubgoals := true)


end Tactic.ApplyRuleSets
end Mathlib
