/-
Copyright (c) 2026 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public meta import Mathlib.Lean.Meta.RefinedDiscrTree.Encode
public import Lean.Elab.Tactic.ElabTerm
public import Mathlib.Tactic.ApplyRuleSets.Types
public import Mathlib.Tactic.FunProp.Decl

public meta section

namespace Mathlib
namespace Tactic.ApplyRuleSets

open Lean Meta Elab Term
open Lean.Meta.RefinedDiscrTree

/-- A procedural rule. The array contains the synthesized arguments from the ruleproc pattern. -/
abbrev RuleProc := Array Expr → ArgOrigin → Expr → ApplyRuleSetsM (Option Expr)

/-- Compute indexing keys for a theorem conclusion or ruleproc pattern. -/
def keysForPattern (pattern : Expr) : MetaM (List (Key × LazyEntry)) := do
  RefinedDiscrTree.initializeLazyEntryWithEta pattern

/-- Compute a plain discrimination-tree path for a theorem conclusion or ruleproc pattern. -/
def discrPathForPattern (pattern : Expr) : MetaM (Array DiscrTree.Key) := do
  DiscrTree.mkPath pattern

/-- Persistent information about a declared ruleproc pattern. -/
structure RuleProcDecl where
  declName : Name
  pattern : Expr
  levelParams : Array Name := #[]
  refinedKeys : List (Key × LazyEntry)
  discrPath : Array DiscrTree.Key
  /-- The declaration applied to default procedural parameters, if it has type `RuleProc`.
  This is used when registering a ruleproc in a ruleset with an attribute. Parameterized
  ruleprocs without defaults have no default proc and must be supplied explicitly, e.g.
  `apply_rulesets [myProc 7]`. -/
  defaultProc? : Option Expr := none
deriving Inhabited

initialize ruleProcDeclExt : SimpleScopedEnvExtension RuleProcDecl (Std.HashMap Name RuleProcDecl) ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun s e => s.insert e.declName e
  }

/-- Register the pattern for a ruleproc declaration. -/
def registerRuleProcPattern (declName : Name) (pattern : Expr) (levelParams : Array Name := #[])
    (defaultProc? : Option Expr := none) : MetaM Unit := do
  if pattern.hasExprMVar then
    throwError "invalid ruleproc pattern for `{.ofConstName declName}` contains expression \
      metavariables"
  let levelParams := levelParams ++ (exprLevelParams pattern).filter (!levelParams.contains ·)
  let (_, _, conclusion) ← forallMetaTelescope pattern
  let refinedKeys ← keysForPattern conclusion
  let discrPath ← discrPathForPattern conclusion
  modifyEnv fun env => ruleProcDeclExt.addEntry env {
    declName, pattern, levelParams, refinedKeys, discrPath, defaultProc? }

/-- Return registered pattern information for a ruleproc declaration. -/
def getRuleProcDecl? (declName : Name) : CoreM (Option RuleProcDecl) := do
  return (ruleProcDeclExt.getState (← getEnv)).get? declName

/-- Evaluate a ruleproc declaration. -/
unsafe def getRuleProcFromDeclImpl (declName : Name) : MetaM RuleProc := do
  let env ← getEnv
  let opts ← getOptions
  match env.evalConst RuleProc opts declName with
  | .ok proc => return proc
  | .error err => throwError err

@[implemented_by getRuleProcFromDeclImpl]
opaque getRuleProcFromDecl (declName : Name) : MetaM RuleProc

/-- Evaluate a ruleproc expression. -/
unsafe def evalRuleProcImpl (proc : Expr) : MetaM RuleProc := do
  Meta.evalExpr RuleProc (mkConst ``RuleProc) proc (safety := .unsafe)

@[implemented_by evalRuleProcImpl]
opaque evalRuleProc (proc : Expr) : MetaM RuleProc

def instantiateRuleProcPattern (decl : RuleProcDecl) (proc : Expr) : MetaM (Expr × Array Name) := do
  let some declName := proc.getAppFn.constName?
    | throwError "ruleproc term is not headed by a declaration{indentExpr proc}"
  unless declName == decl.declName do
    throwError "ruleproc declaration mismatch: expected `{.ofConstName decl.declName}`, \
      got `{declName}`"
  let pattern := decl.pattern
  let levelParams :=
    decl.levelParams ++ (exprLevelParams pattern).filter (!decl.levelParams.contains ·)
  return (pattern, levelParams)

def explicitRuleProcRule? (origin : Origin) (proc : Expr) : MetaM (Option Rule) := do
  let some declName := proc.getAppFn.constName?
    | return none
  unless (← getRuleProcDecl? declName).isSome do
    return none
  unless ← isDefEq (← inferType proc) (mkConst ``RuleProc) do
    return none
  let some decl ← getRuleProcDecl? declName
    | throwError "explicit ruleproc `{.ofConstName declName}` has no registered pattern"
  let (pattern, levelParams) ← instantiateRuleProcPattern decl proc
  let rule : Rule := { origin, type := .proc proc, pattern, levelParams }
  if rule.hasExprMVar then
    throwError "explicit ruleproc `{.ofConstName declName}` contains expression metavariables"
  return some rule

/-- Declaration command used internally to register a ruleproc pattern. -/
elab "ruleproc_pattern% " pat:term " => " proc:ident : command => do
  Command.liftTermElabM do
    let procName ← realizeGlobalConstNoOverload proc
    let pattern ← Term.withAutoBoundImplicit <| Term.elabType pat
    Term.synthesizeSyntheticMVars
    let pattern ← abstractMVars (← instantiateMVars pattern)
    let levelParams := pattern.paramNames
    let pattern ← lambdaTelescope pattern.expr fun xs pattern => mkForallFVars xs pattern
    registerRuleProcPattern procName pattern levelParams

private def mkRuleProcBody (xs : Ident) (names : Array (Nat × Name)) (body : Term) :
    MacroM Term := do
  let mut result := body
  for i in [0:names.size] do
    let i := names.size - 1 - i
    let (argIdx, name) := names[i]!
    let id := mkIdentFrom body name
    let idx := quote argIdx
    result ← `(let $id:ident : Lean.Expr := $xs[$idx]!; $result)
  return result

private def mkRuleProcTacticBody (goal : Ident)
    (seq : TSyntax ``Lean.Parser.Tactic.tacticSeq) : MacroM Term := do
  `(do
    withOptions (·.setBool `linter.unusedTactic false) <|
      Mathlib.Meta.FunProp.tacticToDischarge (← `(tactic| ($seq:tacticSeq))) $goal)

private def removeUnusedForallBinders (e : Expr) (keepPrefix : Nat := 0) : MetaM Expr := do
  forallTelescope e fun xs body => do
    let mut result := body
    for _h : i in [:xs.size] do
      let i := xs.size - 1 - i
      let x := xs[i]!
      if i < keepPrefix || result.containsFVar x.fvarId! then
        let decl ← x.fvarId!.getDecl
        result := Expr.forallE decl.userName decl.type (result.abstract #[x]) decl.binderInfo
    return result

private def closeRuleProcPattern (pat : Term) :
    TermElabM (Expr × Array Name × Array (Nat × Name)) := do
  let pattern ← Term.withAutoBoundImplicit <| Term.elabType pat
  Term.synthesizeSyntheticMVars
  let pattern ← abstractMVars (← instantiateMVars pattern)
  let levelParams := pattern.paramNames
  let pattern ← lambdaTelescope pattern.expr fun xs pattern => mkForallFVars xs pattern
  let pattern ← removeUnusedForallBinders pattern
  let names ← forallTelescope pattern fun xs _ => do
    let mut names := #[]
    for h : i in [:xs.size] do
      let name ← xs[i].fvarId!.getUserName
      unless name.isAnonymous do
        names := names.push (i, name)
    return names
  return (pattern, levelParams, names)

private def attrInstancesOfAttributes (attrs : TSyntax ``Lean.Parser.Term.attributes) :
    Array (TSyntax ``Lean.Parser.Term.attrInstance) :=
  attrs.raw[1].getArgs.filterMap fun stx =>
    if stx.isOfKind ``Lean.Parser.Term.attrInstance then
      some ⟨stx⟩
    else
      none

/-- Declares a procedural rule for `apply_rulesets`.

A `ruleproc` has a pattern, written like a theorem conclusion, and produces a value of type
`RuleProc`. During search, `apply_rulesets` first matches the pattern against the current goal. If
the pattern matches, the ruleproc is run with the matched pattern arguments, origin information, and
the current goal expression.

The simplest form is a meta-code ruleproc:

```lean
ruleproc solveNeedFirst : NeedFirst := fun origin goal => do
  return some (Lean.mkConst ``NeedFirst.intro)
```

Named binders in the pattern are exposed in the body as `Lean.Expr` values through the argument
array. For example, in

```lean
ruleproc reflByProc {A : Type} (a : A) : a = a := fun _ _ => do
  return some (← Lean.Meta.mkAppM ``Eq.refl #[a])
```

the name `a` in the body is a `Lean.Expr` corresponding to the matched pattern argument.

Binders before a comma are procedural parameters, not part of the matching pattern:

```lean
ruleproc procWithParam (n : Nat), {A : Prop} : A := fun _ _ => do
  logInfo m!"parameter: {n}"
  return none
```

Such a ruleproc must be supplied explicitly with its parameter, for example
`apply_rulesets [procWithParam 7]`, unless all procedural parameters have defaults and the
declaration elaborates to `RuleProc` without extra arguments.

Ruleprocs can also be written in tactic mode:

```lean
ruleproc run_tactic (a b : Int) : a < b := by
  omega
```

In tactic mode, the binders are used only for pattern matching. They are not introduced as local
terms in the tactic script; if the tactic needs to inspect matched expressions, use the meta-code
form instead.

Adding an attribute such as `@[my_rules]` registers the ruleproc in that ruleset. Attribute
registration is only allowed when the declaration has a default executable `RuleProc`; parameterized
ruleprocs without defaults should be passed explicitly in the tactic call. -/
syntax (name := ruleprocCmd) (docComment)? (Lean.Parser.Term.attributes)? "ruleproc " ident
  (ppSpace bracketedBinder)* ("," (ppSpace bracketedBinder)*)? " : " term " := " term : command

@[command_elab ruleprocCmd]
def elabRuleProc : Command.CommandElab := fun stx => do
  let cmdStx := stx
  let `(command| $[$doc?:docComment]? $[$attrs?:attributes]? ruleproc $n:ident $preBs*
      $[, $postBs*]? : $pat:term := $body:term) := cmdStx
    | throwUnsupportedSyntax
  let scope ← Command.getScope
  let varDecls : TSyntaxArray ``Lean.Parser.Term.bracketedBinder :=
    scope.varDecls.map (fun stx => ⟨stx⟩)
  let (procBs, patternBs) :=
    match postBs with
    | none => (#[], varDecls ++ preBs)
    | some postBs => (preBs, varDecls ++ postBs)
  let pat ← `(∀ $patternBs*, $pat)
  let (pattern, levelParams, names) ← Command.liftTermElabM <|
    closeRuleProcPattern pat
  let xs := mkIdent `__ruleprocArgs
  let cmd ← match body with
    | `(term| by $seq:tacticSeq) =>
      let origin := mkIdent `__ruleprocOrigin
      let goal := mkIdent `__ruleprocGoal
      let body ← liftMacroM <| mkRuleProcTacticBody goal seq
      `($[$doc?:docComment]? meta def $n $procBs* :
        Mathlib.Tactic.ApplyRuleSets.RuleProc :=
          fun $xs:ident $origin:ident $goal:ident => $body)
    | _ =>
      let body ← liftMacroM <| mkRuleProcBody xs names body
      `($[$doc?:docComment]? meta def $n $procBs* :
        Mathlib.Tactic.ApplyRuleSets.RuleProc := fun $xs:ident => $body)
  Command.elabCommand cmd
  Command.liftTermElabM do
    let procName ← realizeGlobalConstNoOverload n
    let default? ← try
      let proc ← Term.elabTerm (mkIdentFrom n procName) (some (mkConst ``RuleProc))
      Term.synthesizeSyntheticMVars
      let proc ← instantiateMVars proc
      if proc.hasExprMVar then
        throwError "ruleproc has unsolved default parameter"
      pure <| some proc
    catch _ =>
      pure none
    registerRuleProcPattern procName pattern levelParams (defaultProc? := default?)
  if let some attrs := attrs? then
    let attrInsts := attrInstancesOfAttributes attrs
    Command.elabCommand <| ← `(command| attribute [$attrInsts,*] $n)

end Tactic.ApplyRuleSets
end Mathlib
