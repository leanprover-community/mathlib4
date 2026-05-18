/-
Copyright (c) 2026 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public meta import Mathlib.Lean.Meta.RefinedDiscrTree.Lookup
public import Lean.Elab.Tactic.ElabTerm
public import Lean.Meta.Tactic.ExposeNames
public import Mathlib.Tactic.ApplyRuleSets.Attr

public meta section

namespace Mathlib
namespace Tactic.ApplyRuleSets

open Lean Meta Elab Tactic

/-- Increase and check step count. -/
def checkStep : ApplyRuleSetsM Unit := do
  let n := (← get).numSteps
  let maxSteps := (← read).config.maxSteps
  if n ≥ maxSteps then
    throwError "apply_rulesets failed, maximum number of steps ({maxSteps}) exceeded"
  modify fun s => { s with numSteps := s.numSteps + 1 }

/-- Increase the logical search depth without introducing a new metavariable depth. -/
def withIncreasedSearchDepth {α} (x : ApplyRuleSetsM α) : ApplyRuleSetsM α := do
  let depth := (← get).depth
  modify fun s => { s with depth := depth + 1 }
  try
    let a ← x
    modify fun s => { s with depth := depth }
    return a
  catch e =>
    modify fun s => { s with depth := depth }
    throw e

/-- Roll back metavariable assignments if `x` returns `none` or throws. -/
def observingWithRollback? {α} (x : ApplyRuleSetsM (Option α)) : ApplyRuleSetsM (Option α) := do
  let mctx ← getMCtx
  try
    match ← x with
    | some a => return some a
    | none => setMCtx mctx; return none
  catch e =>
    trace[Meta.Tactic.apply_rulesets] "candidate failed: {e.toMessageData}"
    setMCtx mctx
    return none

/-- Run the tactic embedded in an `autoParam` goal. -/
def runAutoParam? (goalType : Expr) : MetaM (Option Expr) := do
  let some (.const tacticDecl _) := goalType.getAutoParamTactic?
    | return none
  let goalType := goalType.appFn!.appArg!
  let .ok tacticSyntax := evalSyntaxConstant (← getEnv) (← getOptions) tacticDecl
    | return none
  let tacticSeq : TSyntax `Lean.Parser.Tactic.tacticSeq := ⟨tacticSyntax⟩
  let tacticCode ← `(tactic| try ($tacticSeq:tacticSeq))
  let mvar ← mkFreshExprSyntheticOpaqueMVar goalType `apply_rulesets.autoParam
  let runTac? : TermElabM (Option Expr) := do
    try
      Term.withoutModifyingElabMetaStateWithInfo do
        Term.withSynthesize (postpone := .no) do
          discard <| Tactic.run mvar.mvarId! <|
            Tactic.evalTactic tacticCode *> Tactic.pruneSolvedGoals
        let result ← instantiateMVars mvar
        if result.hasExprMVar then
          return none
        else
          return some result
    catch _ =>
      return none
  let (result?, _) ← runTac?.run {} {}
  return result?

/-- Query selected rulesets for candidates matching `goalType`. -/
def takeRuleSetTree (rsName : Name) : ApplyRuleSetsM (RefinedDiscrTree Rule) := do
  let tree? ← modifyGet fun s =>
    (s.ruleSetTrees.get? rsName,
      { s with ruleSetTrees := s.ruleSetTrees.alter rsName fun _ => none })
  return tree?.getD (← getRuleSet rsName).tree

def queryRuleSets (goalType : Expr) (rulesets : Array Name) : ApplyRuleSetsM (Array Rule) := do
  let mut out := #[]
  for rsName in rulesets do
    let tree ← takeRuleSetTree rsName
    let (result, tree) ← withConfig (fun cfg => { cfg with iota := false, zeta := false }) <|
      tree.getMatch goalType true true
    modify fun s =>
      { s with ruleSetTrees := s.ruleSetTrees.alter rsName fun _ => some tree }
    out := out ++ result.toArray
  return out

/-- Sort candidates by priority, explicitness, and insertion order. -/
def sortRules (rules : Array Rule) : Array Rule :=
  rules.qsort fun a b =>
    if a.priority != b.priority then
      a.priority > b.priority
    else
      a.order < b.order

def Rule.instantiate (rule : Rule) : MetaM (RuleType × Expr) := do
  let levelParams := rule.allLevelParams
  let us ← levelParams.mapM fun _ => mkFreshLevelMVar
  let pattern := rule.pattern.instantiateLevelParamsArray levelParams us
  let type := match rule.type with
    | .expr proof => .expr (proof.instantiateLevelParamsArray levelParams us)
    | .proc proc => .proc (proc.instantiateLevelParamsArray levelParams us)
  return (type, pattern)

def matchRuleConclusion (_rule : Rule) (conclusion goal : Expr) : ApplyRuleSetsM Bool := do
  let conclusion ← instantiateMVars conclusion
  let goal ← instantiateMVars goal
  withTransparency (← read).config.transparency <| isDefEq conclusion goal

mutual

/-- Try to solve a proposition goal by a local hypothesis. -/
partial def assumption? (origin : ArgOrigin) (goalType : Expr) : ApplyRuleSetsM (Option Expr) := do
  unless ← isProp goalType do
    return none
  for localDecl in ← getLCtx do
    unless localDecl.isAuxDecl do
      if ← isProp localDecl.type then
        if ← isDefEq localDecl.type goalType then
          return some (mkFVar localDecl.fvarId)
        if localDecl.type.isForall then
          let rule : Rule := {
            origin := .fvar localDecl.fvarId
            pattern := localDecl.type
            type := .expr (.fvar localDecl.fvarId)
          }
          if let some r ← tryRule? origin goalType rule then
            return r
  return none

partial def applyRuleSets (origin : ArgOrigin) (goalType : Expr) :
    ApplyRuleSetsM (Option Expr) := do
  let goalType ← instantiateMVars goalType
  withTraceNode `Meta.Tactic.apply_rulesets
    (fun _ => return s!"{← ppExpr goalType}") do
  checkStep
  let depth := (← get).depth
  let maxDepth := (← read).config.maxDepth
  if depth > maxDepth then
    trace[Meta.Tactic.apply_rulesets] "maximum recursion depth ({maxDepth}) exceeded"
    return none
  let cfg := (← read).config
  if cfg.autoParam then
    if let some proof ← observingWithRollback? <| runAutoParam? goalType then
      trace[Meta.Tactic.apply_rulesets] "solved by autoParam tactic"
      return some proof
  if cfg.assumption then
    if let some proof ← observingWithRollback? <| assumption? origin goalType then
      trace[Meta.Tactic.apply_rulesets] "solved by local assumption"
      return some proof
  if cfg.intro then
    let some proof ← observingWithRollback? <| forallTelescopeReducing goalType fun xs body => do
      if xs.isEmpty then
        return none
      trace[Meta.Tactic.apply_rulesets] "introducing {xs.size} binder(s)"
      let some proof ← withIncreasedSearchDepth <| applyRuleSets origin body | return none
      return some (← mkLambdaFVars xs proof)
      | pure ()
    return some proof
  let rules := sortRules (← queryRuleSets goalType (← read).rulesets)
  trace[Meta.Tactic.apply_rulesets]
    "candidate rules: {rules.map fun rule => rule.name}"
  for rule in (← read).explicitRules do
    if let some proof ← observingWithRollback? <| tryRule? origin goalType rule then
      return some proof
  for rule in rules do
    unless (← read).erased.contains rule.name do
      if let some proof ← observingWithRollback? <| tryRule? origin goalType rule then
        return some proof
  trace[Meta.Tactic.apply_rulesets] "no rule matched"
  return none

/-- Synthesize arguments created by theorem or ruleproc application. -/
partial def synthesizeArgs (ruleName : Name) (args : Array Expr)
    (allowPostponed := false) : ApplyRuleSetsM Bool := do
  let mut success := true
  let mut postponed := #[]
  for h : i in [:args.size] do
    let arg := args[i]
    if (← instantiateMVars arg).isMVar then
      let type ← inferType arg
      if (← isClass? type).isSome then
        if let .some inst ← trySynthInstance type then
          if (← isDefEq arg inst) then
            continue
          else
            trace[Meta.Tactic.apply_rulesets]
              "{ruleName}, failed to assign instance{indentExpr type}\
              \nsynthesized value{indentExpr inst}\nis not definitionally equal to{indentExpr arg}"
        else
          trace[Meta.Tactic.apply_rulesets]
            "{ruleName}, failed to synthesize instance{indentExpr type}"
      if (← isProp type) then
        let argName := (← getMCtx).getDecl arg.mvarId! |>.userName
        let origin := { ruleName, argIndex := some i, argName := some argName }
        if let some proof ← withIncreasedSearchDepth <| applyRuleSets origin type then
          if (← isDefEq arg proof) then
            continue
          else
            trace[Meta.Tactic.apply_rulesets]
              "{ruleName}, failed to assign proof{indentExpr type}"
        let ctx ← read
        if let some proof ← ctx.disch origin type then
          if (← isDefEq arg proof) then
            continue
          else
            trace[Meta.Tactic.apply_rulesets]
              "{ruleName}, failed to assign discharger proof{indentExpr type}"
        trace[Meta.Tactic.apply_rulesets]
          "{ruleName}, failed to discharge hypothesis{indentExpr type}"
        addFailedSubgoal arg
        success := false
        continue
      else
        postponed := postponed.push arg
  for arg in postponed do
    if (← instantiateMVars arg).isMVar then
      if allowPostponed then
        continue
      trace[Meta.Tactic.apply_rulesets]
        "{ruleName}, failed to infer `({← ppExpr arg} : {← ppExpr (← inferType arg)})`"
      success := false
      continue
  return success

partial def tryRule? (origin : ArgOrigin) (goalType : Expr) (rule : Rule) :
    ApplyRuleSetsM (Option Expr) := do
  let action := match rule.origin with
    | .decl .. =>
      match rule.type with
      | .proc _ => "applying ruleproc"
      | .expr _ => "applying theorem"
    | .fvar .. | .stx .. | .other .. => match rule.type with
      | .proc _ => "applying explicit ruleproc"
      | .expr _ => "applying explicit rule"
  withTraceNode `Meta.Tactic.apply_rulesets
    (fun _ => return s!"{action}: {rule.name}") do
  if (← read).erased.contains rule.name then
    trace[Meta.Tactic.apply_rulesets] "rule is erased"
    return none
  let (ruleType, pattern) ← rule.instantiate
  let (args, _, conclusion) ← forallMetaTelescope pattern
  let ok ← matchRuleConclusion rule conclusion goalType
  unless ok do
    trace[Meta.Tactic.apply_rulesets]
      "failed to unify rule pattern{indentExpr conclusion}\nwith{indentExpr goalType}"
    return none
  match ruleType with
  | .expr expr =>
    unless ← synthesizeArgs rule.name args do
      return none
    return some (← instantiateMVars (mkAppN expr args))
  | .proc procExpr =>
    unless ← synthesizeArgs rule.name args (allowPostponed := true) do
      trace[Meta.Tactic.apply_rulesets]
        "failed to synthesize ruleproc arguments for {rule.name}"
      return none
    let args ← args.mapM instantiateMVars
    let proc ← evalRuleProc procExpr
    let some proof ← proc args origin goalType
      | trace[Meta.Tactic.apply_rulesets] "ruleproc {rule.name} returned none"; return none
    let proofType ← inferType proof
    let ok ← withTransparency (← read).config.transparency <| isDefEq proofType goalType
    unless ok do
      trace[Meta.Tactic.apply_rulesets]
        "ruleproc {rule.name} returned proof of wrong type{indentExpr proofType}\
        \nfor{indentExpr goalType}"
      return none
    return some proof

end

/-- Backward-search using the active rule sets. Alias for `applyRuleSets`. -/
abbrev appluRuleSets := applyRuleSets

end Tactic.ApplyRuleSets
end Mathlib
