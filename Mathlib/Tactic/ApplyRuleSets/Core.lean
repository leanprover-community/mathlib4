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

def ProfileEntry.addNanos (entry : ProfileEntry) (nanos : Nat) : ProfileEntry :=
  { entry with nanos := entry.nanos + nanos }

def ProfileEntry.incCount (entry : ProfileEntry) : ProfileEntry :=
  { entry with count := entry.count + 1 }

def profileChargeCurrent (now : Nat) : ApplyRuleSetsM Unit := do
  let profile := (← get).profile
  unless profile.enabled do
    return ()
  let some op := profile.stack.head? | return ()
  let elapsed := now - profile.lastNanos
  let entry := (profile.times.get? op).getD {}
  modify fun s =>
    { s with profile :=
      { s.profile with
        lastNanos := now
        times := s.profile.times.insert op (entry.addNanos elapsed) } }

def profileEnter (op : Name) : ApplyRuleSetsM Unit := do
  unless (← get).profile.enabled do
    return ()
  let now ← IO.monoNanosNow
  profileChargeCurrent now
  let entry := ((← get).profile.times.get? op).getD {}
  modify fun s =>
    { s with profile :=
      { s.profile with
        lastNanos := now
        stack := op :: s.profile.stack
        times := s.profile.times.insert op entry.incCount } }

def profileExit : ApplyRuleSetsM Unit := do
  unless (← get).profile.enabled do
    return ()
  let now ← IO.monoNanosNow
  profileChargeCurrent now
  modify fun s =>
    { s with profile :=
      { s.profile with
        lastNanos := now
        stack := s.profile.stack.tail } }

def withProfile {α} (op : Name) (x : ApplyRuleSetsM α) : ApplyRuleSetsM α := do
  unless (← get).profile.enabled do
    return ← x
  profileEnter op
  try
    let a ← x
    profileExit
    return a
  catch e =>
    profileExit
    throw e

/-- Run `x` without charging its elapsed time to the currently active profile timer.

Nested `withProfile` calls inside `x` are still recorded. This is used at public recursive-search
entry points so callers such as ruleprocs are not charged for delegated `apply_rulesets` search. -/
def withoutChargingCurrentTimer {α} (x : ApplyRuleSetsM α) : ApplyRuleSetsM α := do
  let profile := (← get).profile
  unless profile.enabled && !profile.stack.isEmpty do
    return ← x
  let now ← IO.monoNanosNow
  profileChargeCurrent now
  let oldStack := profile.stack
  modify fun s => { s with profile := { s.profile with stack := [], lastNanos := now } }
  try
    let a ← x
    let finish ← IO.monoNanosNow
    modify fun s => { s with profile := { s.profile with stack := oldStack, lastNanos := finish } }
    return a
  catch e =>
    let finish ← IO.monoNanosNow
    modify fun s => { s with profile := { s.profile with stack := oldStack, lastNanos := finish } }
    throw e

def initProfileState : MetaM ProfileState := do
  let now ← IO.monoNanosNow
  return { enabled := true, startNanos := now, lastNanos := now }

def formatProfileNanos (nanos : Nat) : String :=
  let ms := nanos / 1_000_000
  let frac := (nanos % 1_000_000) / 1_000
  s!"{ms}.{frac / 100}{(frac / 10) % 10}{frac % 10}ms"

def formatProfilePct (nanos total : Nat) : String :=
  if total == 0 then
    "0.0%"
  else
    let tenths := (nanos * 1000) / total
    s!"{tenths / 10}.{tenths % 10}%"

def finishProfileReport (profile : ProfileState) : MetaM MessageData := do
  let finish ← IO.monoNanosNow
  let total := finish - profile.startNanos
  let entries := profile.times.toArray.qsort fun a b => a.2.nanos > b.2.nanos
  let mut categorized := 0
  let mut lines : Array MessageData :=
    #[m!"apply_rulesets profile: total {formatProfileNanos total}"]
  for (op, entry) in entries do
    categorized := categorized + entry.nanos
    lines := lines.push <| m!"  {op}: {formatProfileNanos entry.nanos} \
      ({formatProfilePct entry.nanos total}), {entry.count} call(s)"
  let uncategorized := total - categorized
  if uncategorized > 0 then
    lines := lines.push <| m!"  uncategorized: {formatProfileNanos uncategorized} \
      ({formatProfilePct uncategorized total})"
  return MessageData.joinSep lines.toList "\n"

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

def withIncreasedCacheDepth {α} (x : ApplyRuleSetsM α) : ApplyRuleSetsM α := do
  let oldSize := (← get).goalCaches.size
  let minLctxIndex := (← getLCtx).numIndices
  modify fun s =>
    { s with goalCaches := s.goalCaches.push { minLctxIndex } }
  try
    let a ← x
    modify fun s => { s with goalCaches := s.goalCaches.extract 0 oldSize }
    return a
  catch e =>
    modify fun s => { s with goalCaches := s.goalCaches.extract 0 oldSize }
    throw e

def currentGoalCache? : ApplyRuleSetsM (Option GoalCache) := do
  let caches := (← get).goalCaches
  return caches.back?

def modifyGoalCacheAt (i : Nat) (f : GoalCache → GoalCache) : ApplyRuleSetsM Unit := do
  modify fun s =>
    if h : i < s.goalCaches.size then
      { s with goalCaches := s.goalCaches.set i (f s.goalCaches[i]) }
    else
      s

def modifyCurrentGoalCache (f : GoalCache → GoalCache) : ApplyRuleSetsM Unit := do
  let caches := (← get).goalCaches
  unless caches.isEmpty do
    modifyGoalCacheAt (caches.size - 1) f

def cacheCurrentFailure (goal : Goal) : ApplyRuleSetsM Unit := do
  modifyCurrentGoalCache fun cache =>
    { cache with failures := cache.failures.insert goal }

def containsCurrentFailure (goal : Goal) : ApplyRuleSetsM Bool := do
  return (← currentGoalCache?).any (·.failures.contains goal)

def findCachedSuccess? (goal : Goal) : ApplyRuleSetsM (Option Expr) := do
  for cache in (← get).goalCaches.reverse do
    if let some proof := cache.successes.get? goal then
      return some proof
  return none

def maxLocalIndex? (es : Array Expr) : MetaM (Option Nat) := do
  let lctx ← getLCtx
  let mut max? := none
  for e in es do
    for fvarId in (Lean.collectFVars {} e).fvarIds do
      if let some decl := lctx.find? fvarId then
        max? := some <| max (max?.getD 0) decl.index
  return max?

def successCacheIndex (goal : Goal) (proof : Expr) : ApplyRuleSetsM Nat := do
  let maxIdx? ← maxLocalIndex? #[goal.expr, proof]
  let caches := (← get).goalCaches
  if caches.isEmpty then
    return 0
  let some maxIdx := maxIdx? | return 0
  for h : i in [:caches.size] do
    if maxIdx < caches[i].minLctxIndex then
      return i
  return caches.size - 1

def cacheSuccess (goal : Goal) (proof : Expr) : ApplyRuleSetsM Unit := do
  let proof ← withProfile `instantiateMVars <| instantiateMVars proof
  unless proof.hasExprMVar do
    let i ← successCacheIndex goal proof
    modifyGoalCacheAt i fun cache =>
      { cache with successes := cache.successes.insert goal proof }

def mkGoal (e : Expr) : MetaM Goal := do
  let r ← abstractMVars (← instantiateMVars e)
  let expr ← lambdaTelescope r.expr fun xs body => mkForallFVars xs body
  return { expr, numOutputs := r.numMVars }

def Goal.open {α} (goal : Goal) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let (outputs, _, body) ← forallMetaTelescopeReducing goal.expr (some goal.numOutputs)
  k outputs body

/-- Run the tactic embedded in an `autoParam` goal. -/
def runAutoParam? (goalType : Expr) : ApplyRuleSetsM (Option Expr) :=
  withProfile `autoParam do
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
    (s.refinedRuleSetTrees.get? rsName,
      { s with refinedRuleSetTrees := s.refinedRuleSetTrees.alter rsName fun _ => none })
  return tree?.getD (← getRuleSet rsName).refinedTree

def queryRuleSetRefined (goalType : Expr) (rsName : Name) : ApplyRuleSetsM (Array Rule) := do
  let tree ← takeRuleSetTree rsName
  let (result, tree) ← withProfile `refinedDiscrTree.getMatch <|
    withConfig (fun cfg => { cfg with iota := false, zeta := false }) <|
      tree.getMatch goalType true true
  modify fun s =>
    { s with refinedRuleSetTrees := s.refinedRuleSetTrees.alter rsName fun _ => some tree }
  return result.toArray

def queryRuleSetPlain (goalType : Expr) (rsName : Name) : ApplyRuleSetsM (Array Rule) := do
  withProfile `discrTree.getMatch do
    return ← (← getRuleSet rsName).discrTree.getMatch goalType

def queryRuleSets (goalType : Expr) (rulesets : Array Name) : ApplyRuleSetsM (Array Rule) := do
  let mut out := #[]
  for rsName in rulesets do
    let result ←
      if (← read).config.useRefinedDiscrTree then
        queryRuleSetRefined goalType rsName
      else
        queryRuleSetPlain goalType rsName
    out := out ++ result
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
  let conclusion ← withProfile `instantiateMVars <| instantiateMVars conclusion
  let goal ← withProfile `instantiateMVars <| instantiateMVars goal
  withProfile `isDefEq <|
    withTransparency (← read).config.transparency <| isDefEq conclusion goal

mutual

/-- Try to solve a proposition goal by a local hypothesis. -/
partial def assumption? (origin : ArgOrigin) (goalType : Expr) : ApplyRuleSetsM (Option Expr) := do
  unless ← withProfile `isProp <| isProp goalType do
    return none
  withProfile `assumption do
  for localDecl in ← getLCtx do
    unless localDecl.isAuxDecl do
      if ← withProfile `isProp <| isProp localDecl.type then
        if ← withProfile `isDefEq <| isDefEq localDecl.type goalType then
          return some (mkFVar localDecl.fvarId)
        if localDecl.type.isForall then
          let rule : Rule := {
            origin := .fvar localDecl.fvarId
            pattern := localDecl.type
            type := .expr (.fvar localDecl.fvarId)
          }
          let goal ← withProfile `goal.mk <| mkGoal goalType
          if let some r ← withoutChargingCurrentTimer <| tryRule? origin goal rule then
            return r
  return none

partial def applyRuleSets (origin : ArgOrigin) (goalType : Expr) :
    ApplyRuleSetsM (Option Expr) :=
  withoutChargingCurrentTimer <| applyRuleSetsCoreSearch origin goalType

partial def applyRuleSetsCoreSearch (origin : ArgOrigin) (goalType : Expr) :
    ApplyRuleSetsM (Option Expr) := do
  let goal ← withProfile `goal.mk <| mkGoal goalType
  if let some r ← applyRuleSetsGoal origin goal then
    if ← withProfile `isDefEq <|
        withTransparency (← read).config.transparency <| isDefEq goalType (← inferType r) then
      return r
    else
      return none
  else
    return none

partial def applyRuleSetsGoal (origin : ArgOrigin) (goal : Goal) :
    ApplyRuleSetsM (Option Expr) := do
  let goalType ← withProfile `goal.open <| goal.open fun _ goalType => pure goalType
  withTraceNode `Meta.Tactic.apply_rulesets
    (fun _ => return s!"{← ppExpr goalType}") do
  if ← withProfile `cache.lookup <| containsCurrentFailure goal then
    trace[Meta.Tactic.apply_rulesets] "failed goal cache hit"
    return none
  if let some proof ← withProfile `cache.lookup <| findCachedSuccess? goal then
    trace[Meta.Tactic.apply_rulesets] "successful goal cache hit"
    return some proof
  match ← applyRuleSetsGoalCore origin goal goalType with
  | some proof =>
    withProfile `cache.insertSuccess <| cacheSuccess goal proof
    return some proof
  | none =>
    withProfile `cache.insertFailure <| cacheCurrentFailure goal
    return none

partial def applyRuleSetsGoalCore (origin : ArgOrigin) (goal : Goal) (goalType : Expr) :
    ApplyRuleSetsM (Option Expr) := do
  checkStep
  let depth := (← get).depth
  let maxDepth := (← read).config.maxDepth
  if depth > maxDepth then
    trace[Meta.Tactic.apply_rulesets] "maximum recursion depth ({maxDepth}) exceeded"
    return none
  let cfg := (← read).config
  if cfg.autoParam then
    if let some proof ← runAutoParam? goalType then
      trace[Meta.Tactic.apply_rulesets] "solved by autoParam tactic"
      return some proof
  if cfg.assumption then
    if let some proof ← assumption? origin goalType then
      trace[Meta.Tactic.apply_rulesets] "solved by local assumption"
      return some proof
  if cfg.intro then
    let some proof ← withProfile `forallMetaTelescope <|
      forallTelescopeReducing goalType fun xs body => do
      if xs.isEmpty then
        return none
      trace[Meta.Tactic.apply_rulesets] "introducing {xs.size} binder(s)"
      let some proof ← withIncreasedSearchDepth <| withIncreasedCacheDepth <|
        applyRuleSetsCoreSearch origin body | return none
      return some (← withProfile `mkLambdaFVars <| mkLambdaFVars xs proof)
      | pure ()
    return some proof
  let rules ← withProfile `rules.querySort do
    return sortRules (← queryRuleSets goalType (← read).rulesets)
  trace[Meta.Tactic.apply_rulesets]
    "candidate rules: {rules.map fun rule => rule.name}"
  for rule in (← read).explicitRules do
    if let some proof ← tryRule? origin goal rule then
      return some proof
  for rule in rules do
    unless (← read).erased.contains rule.name do
      if let some proof ← tryRule? origin goal rule then
        return some proof
  trace[Meta.Tactic.apply_rulesets] "no rule matched"
  return none

partial def synthesizeInstanceArg? (ruleName : Name) (arg type : Expr) : ApplyRuleSetsM Bool := do
  unless (← isClass? type).isSome do
    return false
  if let .some inst ← withProfile `synthInstance <| trySynthInstance type then
    if ← withProfile `isDefEq <| isDefEq arg inst then
      return true
    trace[Meta.Tactic.apply_rulesets]
      "{ruleName}, failed to assign instance{indentExpr type}\
      \nsynthesized value{indentExpr inst}\nis not definitionally equal to{indentExpr arg}"
  else
    trace[Meta.Tactic.apply_rulesets]
      "{ruleName}, failed to synthesize instance{indentExpr type}"
  return false

partial def synthesizeProofArg? (ruleName : Name) (argIndex : Nat) (arg type : Expr) :
    ApplyRuleSetsM Bool := do
  unless ← isProp type do
    return false
  let argName := (← getMCtx).getDecl arg.mvarId! |>.userName
  let origin := { ruleName, argIndex := some argIndex, argName := some argName }
  if let some proof ← withIncreasedSearchDepth <| applyRuleSetsCoreSearch origin type then
    if ← withProfile `isDefEq <| isDefEq arg proof then
      return true
    trace[Meta.Tactic.apply_rulesets]
      "{ruleName}, failed to assign proof{indentExpr type}"
  let ctx ← read
  if let some proof ← withProfile `discharger <| ctx.disch origin type then
    if ← withProfile `isDefEq <| isDefEq arg proof then
      return true
    trace[Meta.Tactic.apply_rulesets]
      "{ruleName}, failed to assign discharger proof{indentExpr type}"
  trace[Meta.Tactic.apply_rulesets]
    "{ruleName}, failed to discharge hypothesis{indentExpr type}"
  addFailedSubgoal arg
  return true

partial def checkPostponedArgs (ruleName : Name) (args : Array Expr) (allowPostponed : Bool) :
    ApplyRuleSetsM Bool := do
  let mut success := true
  for arg in args do
    if (← withProfile `instantiateMVars <| instantiateMVars arg).isMVar then
      if allowPostponed then
        continue
      trace[Meta.Tactic.apply_rulesets]
        "{ruleName}, failed to infer `({← ppExpr arg} : {← ppExpr (← inferType arg)})`"
      success := false
  return success

/-- Synthesize arguments created by theorem or ruleproc application. -/
partial def synthesizeArgs (ruleName : Name) (args : Array Expr)
    (allowPostponed := false) : ApplyRuleSetsM Bool := do
  let mut success := true
  let mut postponed := #[]
  for h : i in [:args.size] do
    let arg := args[i]
    if (← withProfile `instantiateMVars <| instantiateMVars arg).isMVar then
      let type ← withProfile `inferType <| inferType arg
      if ← synthesizeInstanceArg? ruleName arg type then
        continue
      if ← withProfile `isProp <| isProp type then
        unless ← synthesizeProofArg? ruleName i arg type do
          postponed := postponed.push arg
        if (← withProfile `instantiateMVars <| instantiateMVars arg).isMVar then
          success := false
        continue
      postponed := postponed.push arg
  return success && (← checkPostponedArgs ruleName postponed allowPostponed)

partial def tryRule? (origin : ArgOrigin) (goal : Goal) (rule : Rule) :
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
  if rule.hasExprMVar then
    trace[Meta.Tactic.apply_rulesets] "rule contains expression metavariables"
    return none
  let goalType ← withProfile `goal.open <| goal.open fun _ goalType => pure goalType
  let (ruleType, pattern) ← withProfile `rule.instantiate <| rule.instantiate
  let (args, _, conclusion) ← withProfile `forallMetaTelescope <| forallMetaTelescope pattern
  let ok ← matchRuleConclusion rule conclusion goalType
  unless ok do
    trace[Meta.Tactic.apply_rulesets]
      "failed to unify rule pattern{indentExpr conclusion}\nwith{indentExpr goalType}"
    return none
  match ruleType with
  | .expr expr =>
    unless ← synthesizeArgs rule.name args do
      return none
    let proof ← withProfile `instantiateMVars <| instantiateMVars (mkAppN expr args)
    return some proof
  | .proc procExpr =>
    unless ← synthesizeArgs rule.name args (allowPostponed := true) do
      trace[Meta.Tactic.apply_rulesets]
        "failed to synthesize ruleproc arguments for {rule.name}"
      return none
    let args ← withProfile `instantiateMVars <| args.mapM instantiateMVars
    let proc ← withProfile `ruleproc.eval <| evalRuleProc procExpr
    let some proof ← withProfile `ruleproc.run <| proc args origin goalType
      | trace[Meta.Tactic.apply_rulesets] "ruleproc {rule.name} returned none"; return none
    let proofType ← withProfile `inferType <| inferType proof
    let ok ← withProfile `isDefEq <|
      withTransparency (← read).config.transparency <| isDefEq proofType goalType
    unless ok do
      trace[Meta.Tactic.apply_rulesets]
        "ruleproc {rule.name} returned proof of wrong type{indentExpr proofType}\
        \nfor{indentExpr goalType}"
      return none
    return some proof

end

end Tactic.ApplyRuleSets
end Mathlib
