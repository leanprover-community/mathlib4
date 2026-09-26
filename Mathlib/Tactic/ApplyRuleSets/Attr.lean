/-
Copyright (c) 2026 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public import Mathlib.Tactic.ApplyRuleSets.RuleProc

public meta section

namespace Mathlib
namespace Tactic.ApplyRuleSets

open Lean Meta Elab
open Lean.Meta.RefinedDiscrTree

initialize ruleSetsExt : SimpleScopedEnvExtension RuleSetExtEntry RuleSets ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun s e =>
      let rule := { e.rule with order := s.nextOrder }
      let rs := s.ruleSets.getD e.ruleSetName {}
      let refinedTree := e.refinedKeys.foldl (fun t (key, lazyEntry) =>
        RefinedDiscrTree.insert t key (lazyEntry, rule)) rs.refinedTree
      let discrTree := rs.discrTree.insertKeyValue e.discrPath rule
      let rs := { entries := rs.entries.push rule, refinedTree, discrTree }
      { ruleSets := s.ruleSets.insert e.ruleSetName rs, nextOrder := s.nextOrder + 1 }
  }

/-- Return true if `name` is a registered ruleset. -/
def isRuleSetName (name : Name) : CoreM Bool := do
  return (ruleSetsExt.getState (← getEnv)).ruleSets.contains name

/-- Get a registered ruleset. -/
def getRuleSet (name : Name) : CoreM RuleSet := do
  return (ruleSetsExt.getState (← getEnv)).ruleSets.getD name {}

/-- Add a theorem to a ruleset. -/
def addTheoremRule (ruleSetName declName : Name) (kind : AttributeKind)
    (prio : Nat := eval_prio default) : MetaM Unit := do
  let info ← getConstInfo declName
  let pattern := info.type
  let (_, _, conclusion) ← forallMetaTelescope pattern
  let refinedKeys ← keysForPattern conclusion
  let discrPath ← discrPathForPattern conclusion
  let value := mkConst declName (info.levelParams.map Level.param)
  let rule : Rule := {
    origin := .decl declName
    type := .expr value
    pattern := pattern
    levelParams := info.levelParams.toArray
    priority := prio
  }
  if rule.hasExprMVar then
    throwError "invalid theorem rule `{.ofConstName declName}` contains expression metavariables"
  ruleSetsExt.add { ruleSetName, rule, refinedKeys, discrPath } kind
  trace[Meta.Tactic.apply_rulesets.attr] "added theorem rule {declName} to {ruleSetName}"

/-- Register a ruleproc in a ruleset. -/
def addProcRule (ruleSetName declName : Name) (kind : AttributeKind)
    (prio : Nat := eval_prio default) : MetaM Unit := do
  let some decl ← getRuleProcDecl? declName
    | throwError "invalid ruleproc attribute: `{.ofConstName declName}` has no registered pattern"
  let some proc := decl.defaultProc?
    | throwError "invalid ruleproc attribute: `{.ofConstName declName}` does not elaborate as a \
      `RuleProc`; provide defaults for all ruleproc parameters before the comma"
  let rule : Rule := {
    origin := .decl declName
    type := .proc proc
    pattern := decl.pattern
    levelParams := decl.levelParams
    priority := prio
  }
  if rule.hasExprMVar then
    throwError "invalid ruleproc rule `{.ofConstName declName}` contains expression metavariables"
  ruleSetsExt.add {
    ruleSetName := ruleSetName
    rule := rule
    refinedKeys := decl.refinedKeys
    discrPath := decl.discrPath } kind
  trace[Meta.Tactic.apply_rulesets.attr] "added ruleproc {declName} to {ruleSetName}"

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

end Tactic.ApplyRuleSets
end Mathlib
