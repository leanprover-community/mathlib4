/-
Copyright (c) 2026 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public meta import Mathlib.Lean.Meta.RefinedDiscrTree.Initialize
public meta import Mathlib.Lean.Meta.RefinedDiscrTree.Lookup
public import Lean.Elab.Tactic.Config
public import Lean.Elab.Tactic.ElabTerm
public import Lean.Meta.Tactic.SolveByElim
public import Mathlib.Tactic.FunProp.Decl

/-!
# The `apply_rulesets` tactic

This file defines a first version of a configurable backward-search tactic using named rulesets.
Rulesets contain theorem rules and procedural rules (`ruleproc`s) in one ordered database.
-/

public meta section

namespace Mathlib
namespace Tactic.ApplyRuleSets

open Lean Meta Elab Tactic Term
open Lean.Parser.Tactic
open Lean.Meta.RefinedDiscrTree

initialize registerTraceClass `Meta.Tactic.apply_rulesets
initialize registerTraceClass `Meta.Tactic.apply_rulesets.attr

/-- Configuration for `apply_rulesets`. -/
structure Config extends ApplyConfig where
  /-- Maximum recursive depth. -/
  maxDepth : Nat := 50
  /-- Maximum number of candidate attempts. -/
  maxSteps : Nat := 10000
  /-- Transparency used by unification. -/
  transparency : TransparencyMode := .default
  /-- Use local hypotheses to solve proposition goals. -/
  assumption : Bool := true
  /-- Introduce leading binders and continue recursively. -/
  intro : Bool := true
  /-- Run the tactic embedded in `autoParam` goals. -/
  autoParam : Bool := true

instance : Inhabited Config := ⟨{}⟩

/-- Information about a goal passed to a rule or discharger. -/
structure ArgOrigin where
  /-- The theorem or term rule that generated the goal, or `anonymous` for the root goal. -/
  ruleName : Name
  /-- Argument index in the theorem telescope, or `none` for the root goal. -/
  argIndex : Option Nat := none
  /-- Argument binder name in the theorem telescope, or `none` for the root goal. -/
  argName : Option Name := none
deriving Inhabited, BEq

/-- Explicit tactic-call theorem or term. -/
structure ExplicitRule where
  order : Nat
  expr : Expr
deriving Inhabited

def ExplicitRule.name (r : ExplicitRule) : Name :=
  r.expr.constName?.getD (`apply_rulesets.explicit ++ Name.num Name.anonymous r.order)

/-- Search context. -/
structure Context where
  config : Config := {}
  rulesets : Array Name := #[]
  explicitRules : Array ExplicitRule := #[]
  /-- Side-condition discharger for proposition arguments. -/
  disch : ArgOrigin → Expr → MetaM (Option Expr) := fun _ _ => pure none

/-- Search state. -/
structure State where
  numSteps : Nat := 0
  messages : List String := []

/-- Monad used by `apply_rulesets`. -/
abbrev ApplyRuleSetsM := ReaderT Context <| StateT State MetaM

/-- A procedural rule. The array contains the synthesized arguments from the ruleproc pattern. -/
abbrev RuleProc := Array Expr → ArgOrigin → Expr → ApplyRuleSetsM (Option Expr)

/-- Common metadata for theorem rules and ruleprocs. -/
structure RuleHeader where
  name : Name
  priority : Nat := eval_prio default
  order : Nat := 0
  explicit : Bool := false
deriving Inhabited, BEq

/-- A theorem rule stored in a ruleset. -/
structure TheoremRule where
  header : RuleHeader
deriving Inhabited, BEq

/-- A procedural rule stored in a ruleset. -/
structure ProcRule where
  header : RuleHeader
  pattern : Expr
deriving Inhabited, BEq

/-- A rule entry. -/
inductive RuleEntry where
  | theorem (rule : TheoremRule)
  | proc (rule : ProcRule)
deriving Inhabited, BEq

def RuleEntry.header : RuleEntry → RuleHeader
  | .theorem r => r.header
  | .proc r => r.header

/-- Ruleset data kept in the environment. -/
structure RuleSet where
  entries : Array RuleEntry := #[]
  tree : RefinedDiscrTree RuleEntry := {}
deriving Inhabited

/-- All registered rulesets. -/
structure RuleSets where
  ruleSets : Std.HashMap Name RuleSet := {}
  nextOrder : Nat := 0
deriving Inhabited

/-- Entry added to the global ruleset extension. -/
structure RuleSetExtEntry where
  ruleSetName : Name
  entry : RuleEntry
  keys : List (Key × LazyEntry)
deriving Inhabited

initialize ruleSetsExt : SimpleScopedEnvExtension RuleSetExtEntry RuleSets ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun s e =>
      let header := e.entry.header
      let header := { header with order := s.nextOrder, explicit := false }
      let entry := match e.entry with
        | .theorem r => .theorem { r with header := header }
        | .proc r => .proc { r with header := header }
      let rs := s.ruleSets.getD e.ruleSetName {}
      let tree := e.keys.foldl (fun t (key, lazyEntry) =>
        RefinedDiscrTree.insert t key (lazyEntry, entry)) rs.tree
      let rs := { entries := rs.entries.push entry, tree := tree }
      { ruleSets := s.ruleSets.insert e.ruleSetName rs, nextOrder := s.nextOrder + 1 }
  }

/-- Return true if `name` is a registered ruleset. -/
def isRuleSetName (name : Name) : CoreM Bool := do
  return (ruleSetsExt.getState (← getEnv)).ruleSets.contains name

/-- Get a registered ruleset. -/
def getRuleSet (name : Name) : CoreM RuleSet := do
  return (ruleSetsExt.getState (← getEnv)).ruleSets.getD name {}

/-- Compute indexing keys for a theorem conclusion or ruleproc pattern. -/
def keysForPattern (pattern : Expr) : MetaM (List (Key × LazyEntry)) := do
  RefinedDiscrTree.initializeLazyEntryWithEta pattern

/-- Add a theorem to a ruleset. -/
def addTheoremRule (ruleSetName declName : Name) (kind : AttributeKind)
    (prio : Nat := eval_prio default) : MetaM Unit := do
  let info ← getConstInfo declName
  let (_, _, conclusion) ← forallMetaTelescope info.type
  let keys ← keysForPattern conclusion
  let entry : RuleEntry := .theorem { header := { name := declName, priority := prio } }
  ruleSetsExt.add { ruleSetName, entry, keys } kind
  trace[Meta.Tactic.apply_rulesets.attr] "added theorem rule {declName} to {ruleSetName}"

/-- Persistent information about a declared ruleproc pattern. -/
structure RuleProcDecl where
  declName : Name
  pattern : Expr
  keys : List (Key × LazyEntry)
deriving Inhabited

initialize ruleProcDeclExt : SimpleScopedEnvExtension RuleProcDecl (Std.HashMap Name RuleProcDecl) ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun s e => s.insert e.declName e
  }

/-- Register the pattern for a ruleproc declaration. -/
def registerRuleProcPattern (declName : Name) (pattern : Expr) : MetaM Unit := do
  let (_, _, conclusion) ← forallMetaTelescope pattern
  let keys ← keysForPattern conclusion
  modifyEnv fun env => ruleProcDeclExt.addEntry env { declName, pattern, keys }

/-- Return registered pattern information for a ruleproc declaration. -/
def getRuleProcDecl? (declName : Name) : CoreM (Option RuleProcDecl) := do
  return (ruleProcDeclExt.getState (← getEnv)).get? declName

/-- Register a ruleproc in a ruleset. -/
def addProcRule (ruleSetName declName : Name) (kind : AttributeKind)
    (prio : Nat := eval_prio default) : MetaM Unit := do
  let some decl ← getRuleProcDecl? declName
    | throwError "invalid ruleproc attribute: `{.ofConstName declName}` has no registered pattern"
  let info ← getConstInfo declName
  unless (← isDefEq info.type (mkConst ``RuleProc)) do
    throwError "invalid ruleproc: `{.ofConstName declName}` has type{indentExpr info.type}\
      \nexpected `RuleProc`"
  let header := { name := declName, priority := prio }
  let entry : RuleEntry := .proc { header, pattern := decl.pattern }
  ruleSetsExt.add { ruleSetName, entry, keys := decl.keys } kind
  trace[Meta.Tactic.apply_rulesets.attr] "added ruleproc {declName} to {ruleSetName}"

/-- Evaluate a ruleproc declaration. -/
unsafe def getRuleProcFromDeclImpl (declName : Name) : MetaM RuleProc := do
  let env ← getEnv
  let opts ← getOptions
  match env.evalConst RuleProc opts declName with
  | .ok proc => return proc
  | .error err => throwError err

@[implemented_by getRuleProcFromDeclImpl]
opaque getRuleProcFromDecl (declName : Name) : MetaM RuleProc

/-- Declaration command used internally by `ruleproc_decl`. -/
elab "ruleproc_pattern% " pat:term " => " proc:ident : command => do
  Command.liftTermElabM do
    let procName ← realizeGlobalConstNoOverload proc
    let pattern ← Term.elabType pat
    Term.synthesizeSyntheticMVars
    let pattern ← Term.levelMVarToParam (← instantiateMVars pattern)
    registerRuleProcPattern procName pattern

private def binderNames (binders : Array Syntax) : Array Name := Id.run do
  let mut names := #[]
  let mut instIdx := 0
  for binder in binders do
    match binder.getKind with
    | `Lean.Parser.Term.explicitBinder | `Lean.Parser.Term.implicitBinder =>
      for arg in binder[1].getArgs do
        if arg.isIdent then
          let name := arg.getId
          unless name == `_ do
            names := names.push name
    | `Lean.Parser.Term.instBinder =>
      let explicitNames := binder[1].getArgs.filter Syntax.isIdent |>.map Syntax.getId
      if explicitNames.isEmpty then
        names := names.push (.mkSimple s!"_inst{instIdx}")
        instIdx := instIdx + 1
      else
        for name in explicitNames do
          names := names.push name
    | _ => pure ()
  return names

private def mkRuleProcBody (xs : Ident) (names : Array Name) (body : Term) : MacroM Term := do
  let mut result := body
  for i in [0:names.size] do
    let i := names.size - 1 - i
    let id := mkIdent names[i]!
    let idx := quote i
    result ← `(let $id:ident : Lean.Expr := $xs[$idx]!; $result)
  return result

/-- Syntax for a ruleproc declaration. -/
syntax (docComment)? "ruleproc_decl " ident (ppSpace bracketedBinder)* " : " term " := "
  term : command

macro_rules
  | `($[$doc?:docComment]? ruleproc_decl $n:ident $bs* : $pat:term := $body:term) => do
    let xs := mkIdent `xs
    let body ← mkRuleProcBody xs (binderNames bs) body
    `($[$doc?:docComment]? meta def $n : Mathlib.Tactic.ApplyRuleSets.RuleProc :=
        fun $xs:ident => $body
      ruleproc_pattern% (∀ $bs*, $pat) => $n)

/-- Syntax for a ruleproc declaration immediately attached to rulesets. -/
syntax (docComment)? attrKind "ruleproc " "[" ident,* "]" ident
  (ppSpace bracketedBinder)* " : " term " := " term : command

macro_rules
  | `($[$doc?:docComment]? $kind:attrKind ruleproc [$attrs,*] $n:ident $bs* :
      $pat:term := $body:term) => do
    let attrs := attrs.getElems
    let mut cmds : Array Syntax :=
      #[← `($[$doc?:docComment]? ruleproc_decl $n $bs* : $pat := $body)]
    for attr in attrs do
      let attrName := attr.getId
      let attrParser := mkIdentFrom attr (`Parser.Attr ++ attrName)
      let attrStx : TSyntax `attr := ⟨mkNode attrParser.getId #[mkAtom attrName.toString]⟩
      cmds := cmds.push (← `(attribute [$kind $attrStx:attr] $n))
    return mkNullNode cmds

/-- Register the theorem and proc attributes for a ruleset. -/
def registerRuleSetAttr (ruleSetName : Name) (descr : String) : IO Unit := do
  registerBuiltinAttribute {
    name := ruleSetName
    descr := descr
    applicationTime := AttributeApplicationTime.afterCompilation
    add := fun decl stx kind => discard <| MetaM.run do
      let prio ← getAttrParamOptPrio stx[1]
      if (← getRuleProcDecl? decl).isSome then
        addProcRule ruleSetName decl kind prio
      else
        addTheoremRule ruleSetName decl kind prio
    erase := fun _ => throwError "can't remove ruleset attributes"
  }

/-- Register a new ruleset and its associated attributes. -/
macro (name := registerRulesetCmd) doc:(docComment)? "register_ruleset " id:ident : command => do
  let str := id.getId.toString
  let idParser := mkIdentFrom id (`Parser.Attr ++ id.getId)
  let descr := quote ((doc.map (·.getDocString) |>.getD s!"ruleset {id.getId}").removeLeadingSpaces)
  `($[$doc:docComment]? public meta initialize registerRuleSetAttr $(quote id.getId) $descr
    $[$doc:docComment]? syntax (name := $idParser:ident) $(quote str):str (prio)? : attr)

/-- Increase and check step count. -/
def checkStep : ApplyRuleSetsM Unit := do
  let n := (← get).numSteps
  let maxSteps := (← read).config.maxSteps
  if n ≥ maxSteps then
    throwError "apply_rulesets failed, maximum number of steps ({maxSteps}) exceeded"
  modify fun s => { s with numSteps := s.numSteps + 1 }

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

/-- Try to solve a proposition goal by a local hypothesis. -/
def assumption? (goalType : Expr) : MetaM (Option Expr) := do
  unless ← isProp goalType do
    return none
  for localDecl in ← getLCtx do
    unless localDecl.isAuxDecl do
      if ← isProp localDecl.type then
        if ← isDefEq localDecl.type goalType then
          return some (mkFVar localDecl.fvarId)
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
def queryRuleSets (goalType : Expr) (rulesets : Array Name) : MetaM (Array RuleEntry) := do
  let mut out := #[]
  for rsName in rulesets do
    let rs ← getRuleSet rsName
    let (result, _) ← withConfig (fun cfg => { cfg with iota := false, zeta := false }) <|
      rs.tree.getMatch goalType true true
    out := out ++ result.toArray
  return out

/-- Sort candidates by priority, explicitness, and insertion order. -/
def sortEntries (entries : Array RuleEntry) : Array RuleEntry :=
  entries.qsort fun a b =>
    let ah := a.header
    let bh := b.header
    if ah.priority != bh.priority then
      ah.priority > bh.priority
    else if ah.explicit != bh.explicit then
      ah.explicit && !bh.explicit
    else
      ah.order < bh.order

mutual

partial def prove? (origin : ArgOrigin) (goalType : Expr) (entries : Array RuleEntry)
    (erased : Std.HashSet Name) (depth : Nat) : ApplyRuleSetsM (Option Expr) := do
  checkStep
  let maxDepth := (← read).config.maxDepth
  if depth > maxDepth then
    return none
  let cfg := (← read).config
  if cfg.autoParam then
    if let some proof ← observingWithRollback? <| runAutoParam? goalType then
      return some proof
  if cfg.assumption then
    if let some proof ← observingWithRollback? <| assumption? goalType then
      return some proof
  if cfg.intro then
    let some proof ← observingWithRollback? <| forallTelescopeReducing goalType fun xs body => do
      if xs.isEmpty then
        return none
      let some proof ← prove? origin body entries erased (depth + 1) | return none
      return some (← mkLambdaFVars xs proof)
      | pure ()
    return some proof
  let entries := sortEntries (← queryRuleSets goalType (← read).rulesets)
  for rule in (← read).explicitRules do
    if let some proof ←
        observingWithRollback? <| tryExplicit? origin goalType entries erased depth rule then
      return some proof
  for entry in entries do
    unless erased.contains entry.header.name do
      if let some proof ←
          observingWithRollback? <| tryEntry? origin goalType entries erased depth entry then
        return some proof
  return none

/-- Synthesize arguments created by theorem application. -/
partial def synthesizeArgs (ruleName : Name) (args : Array Expr) (entries : Array RuleEntry)
    (erased : Std.HashSet Name) (depth : Nat) : ApplyRuleSetsM Bool := do
  let mut postponed := #[]
  for h : i in [:args.size] do
    let arg := args[i]
    if (← instantiateMVars arg).isMVar then
      let type ← inferType arg
      if (← isClass? type).isSome then
        if let .some inst ← trySynthInstance type then
          if (← isDefEq arg inst) then
            continue
      if (← isProp type) then
        let argName := (← getMCtx).getDecl arg.mvarId! |>.userName
        let origin := { ruleName, argIndex := some i, argName := some argName }
        if let some proof ← prove? origin type entries erased (depth + 1) then
          if (← isDefEq arg proof) then
            continue
        let ctx ← read
        if let some proof ← ctx.disch origin type then
          if (← isDefEq arg proof) then
            continue
        return false
      else
        postponed := postponed.push arg
  for arg in postponed do
    if (← instantiateMVars arg).isMVar then
      return false
  return true

/-- Try an explicit theorem or term provided in the tactic call. -/
partial def tryExplicit? (_origin : ArgOrigin) (goalType : Expr) (entries : Array RuleEntry)
    (erased : Std.HashSet Name) (depth : Nat) (r : ExplicitRule) :
    ApplyRuleSetsM (Option Expr) := do
  let name := r.name
  if erased.contains name then
    return none
  let type ← inferType r.expr
  let (args, _, conclusion) ← forallMetaTelescope type
  let ok ← withTransparency (← read).config.transparency <| isDefEq conclusion goalType
  unless ok do return none
  unless ← synthesizeArgs name args entries erased depth do return none
  return some (← instantiateMVars (mkAppN r.expr args))

/-- Try a theorem rule. -/
partial def tryTheorem? (_origin : ArgOrigin) (goalType : Expr) (entries : Array RuleEntry)
    (erased : Std.HashSet Name) (depth : Nat) (rule : TheoremRule) :
    ApplyRuleSetsM (Option Expr) := do
  let val ← mkConstWithFreshMVarLevels rule.header.name
  let type ← inferType val
  let (args, _, conclusion) ← forallMetaTelescope type
  let ok ← withTransparency (← read).config.transparency <| isDefEq conclusion goalType
  unless ok do
    return none
  unless ← synthesizeArgs rule.header.name args entries erased depth do
    return none
  return some (← instantiateMVars (mkAppN val args))

/-- Try a ruleproc. -/
partial def tryProc? (origin : ArgOrigin) (goalType : Expr) (entries : Array RuleEntry)
    (erased : Std.HashSet Name) (depth : Nat) (rule : ProcRule) :
    ApplyRuleSetsM (Option Expr) := do
  let (args, _, conclusion) ← forallMetaTelescope rule.pattern
  let ok ← withTransparency (← read).config.transparency <| isDefEq conclusion goalType
  unless ok do
    trace[Meta.Tactic.apply_rulesets] "ruleproc {rule.header.name} did not match {goalType}"
    return none
  unless ← synthesizeArgs rule.header.name args entries erased depth do
    trace[Meta.Tactic.apply_rulesets]
      "failed to synthesize ruleproc arguments for {rule.header.name}"
    return none
  let args ← args.mapM instantiateMVars
  let proc ← getRuleProcFromDecl rule.header.name
  let some proof ← proc args origin goalType
    | trace[Meta.Tactic.apply_rulesets] "ruleproc {rule.header.name} returned none"; return none
  let proofType ← inferType proof
  let ok ← withTransparency (← read).config.transparency <| isDefEq proofType goalType
  unless ok do
    trace[Meta.Tactic.apply_rulesets]
      "ruleproc {rule.header.name} returned proof of wrong type {proofType} for {goalType}"
    return none
  return some proof

/-- Try any rule entry. -/
partial def tryEntry? (origin : ArgOrigin) (goalType : Expr) (entries : Array RuleEntry)
    (erased : Std.HashSet Name) (depth : Nat) : RuleEntry → ApplyRuleSetsM (Option Expr)
  | .theorem rule => tryTheorem? origin goalType entries erased depth rule
  | .proc rule => tryProc? origin goalType entries erased depth rule

end

open Parser.Tactic in
syntax applyRuleSetErase := "-" term:max
syntax applyRuleSetArg := applyRuleSetErase <|> term
syntax applyRuleSetArgs := "[" applyRuleSetArg,* "]"

/-- Config elaborator for `apply_rulesets`. -/
declare_config_elab elabApplyRuleSetsConfig Config

syntax (name := applyRuleSetsTac) "apply_rulesets" optConfig (discharger)? ppSpace
  applyRuleSetArgs : tactic

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

@[tactic applyRuleSetsTac]
def evalApplyRuleSets : Tactic := fun stx => do
  let `(tactic| apply_rulesets $cfgStx:optConfig $[$d?]? $argsStx:applyRuleSetArgs) := stx
    | throwUnsupportedSyntax
  let cfg ← elabApplyRuleSetsConfig cfgStx
  let disch ← tacticDischarger d?
  let args := parseApplyRuleSetArgs argsStx
  let mut rulesets := #[]
  let mut explicitTerms : Array Term := #[]
  let mut erased : Std.HashSet Name := {}
  let mut positives := 0
  for arg in args do
    match arg with
    | `(applyRuleSetArg| - $t:term) =>
      match t.raw with
      | .ident _ _ val _ => erased := erased.insert val
      | _ => throwErrorAt t "apply_rulesets only supports removals by name"
    | `(applyRuleSetArg| $t:term) =>
      positives := positives + 1
      match t.raw with
      | .ident _ _ val _ =>
        if ← isRuleSetName val then
          rulesets := rulesets.push val
        else
          explicitTerms := explicitTerms.push t
      | _ => explicitTerms := explicitTerms.push t
    | _ => throwUnsupportedSyntax
  if positives == 0 then
    throwError "apply_rulesets requires at least one positive ruleset, theorem, or term"
  withMainContext do
    let goal ← getMainGoal
    let goalType ← goal.getType
    let mut explicitRules := #[]
    for h : i in [:explicitTerms.size] do
      let e ← Term.elabTerm explicitTerms[i].raw none
      explicitRules := explicitRules.push ({ order := i, expr := e } : ExplicitRule)
    Term.synthesizeSyntheticMVarsNoPostponing
    let allEntries := #[]
    let ctx : Context :=
      { config := cfg, rulesets := rulesets, explicitRules := explicitRules, disch := disch }
    let s : State := {}
    let (proof?, _) ←
      (prove? { ruleName := Name.anonymous } goalType allEntries erased 0).run ctx |>.run s
    match proof? with
    | some proof => goal.assign proof; replaceMainGoal []
    | none => throwError "apply_rulesets failed"

end Tactic.ApplyRuleSets
end Mathlib
