/-
Copyright (c) 2026 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public meta import Mathlib.Lean.Meta.RefinedDiscrTree.Initialize
public import Lean.Meta.DiscrTree
public import Lean.Elab.Tactic.Config
public import Lean.Meta.Tactic.SolveByElim

public meta section

namespace Mathlib
namespace Tactic.ApplyRuleSets

open Lean Meta
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
  transparency : TransparencyMode := .reducible
  /-- Use local hypotheses to solve proposition goals. -/
  assumption : Bool := true
  /-- Introduce leading binders and continue recursively. -/
  intro : Bool := true
  /-- Run the tactic embedded in `autoParam` goals. -/
  autoParam : Bool := true
  /-- Failed subgoals are collected during the search and code action adding
  `have : <subgoal> := sorry` is offered at the end. -/
  collectFailedSubgoals : Bool := false
  /-- Print an exclusive timing profile for selected `apply_rulesets` operations. -/
  profile : Bool := false
  /-- Use `RefinedDiscrTree` for ruleset lookup. If false, use Lean's plain `DiscrTree` instead.
  This is intended for profiling and comparison; candidate sets may differ. -/
  useRefinedDiscrTree : Bool := true

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

/-- Where a rule came from. -/
inductive Origin where
  /-- A global declaration in the environment. -/
  | decl (declName : Name)
  /-- A local hypothesis. -/
  | fvar (fvarId : FVarId)
  /-- A proof term or proc provided directly to a tactic call. -/
  | stx (id : Name) (ref : Syntax)
  /-- Some other origin. -/
  | other (name : Name)
deriving Inhabited, Repr

def Origin.name : Origin → Name
  | .decl declName .. => declName
  | .fvar fvarId => fvarId.name
  | .stx id _ => id
  | .other name => name

/-- The implementation kind of a rule. -/
inductive RuleType where
  /-- Apply this expression to synthesized arguments. -/
  | expr (proof : Expr)
  /-- Run this procedural rule. -/
  | proc (proc : Expr)
deriving Inhabited

/-- A theorem, explicit term, or procedural rule candidate.

`pattern` is the (possibly dependent) type whose telescope conclusion is unified with the goal.
For theorem rules this is the theorem type; for ruleprocs it is the declared ruleproc pattern. -/
structure Rule where
  origin : Origin
  type : RuleType
  pattern : Expr
  levelParams : Array Name := #[]
  priority : Nat := eval_prio default
  order : Nat := 0
deriving Inhabited

instance : BEq Rule where
  -- `DiscrTree` uses `BEq` only to deduplicate values. Rules are ordered explicitly, so keep every
  -- registered entry even if two rule payloads are structurally identical.
  beq _ _ := false

/-- A canonicalized goal used by `apply_rulesets` internally.

The expression `expr` contains no expression metavariables from the original goal. If the original
goal was `P a b ?c ?d`, then `expr` is `∀ c d, P a b c d`, and `numOutputs = 2` records how many
leading binders should be reopened as fresh output metavariables for each attempt. -/
structure Goal where
  expr : Expr
  numOutputs : Nat
deriving Inhabited, BEq, Hashable

/-- Per-local-context-depth cache for `apply_rulesets` goals. -/
structure GoalCache where
  /-- All local declarations with index strictly below this are in scope for this cache level. -/
  minLctxIndex : Nat
  successes : Std.HashMap Goal Expr := {}
  failures : Std.HashSet Goal := {}
deriving Inhabited

/-- Accumulated timing data for one profiling category. -/
structure ProfileEntry where
  nanos : Nat := 0
  count : Nat := 0
deriving Inhabited

/-- Exclusive profiling state for `apply_rulesets`.

The currently active operation is the head of `stack`. Whenever a new operation starts or ends, the
elapsed time since `lastNanos` is charged to the previous stack head, so operation counters do not
overlap. -/
structure ProfileState where
  enabled : Bool := false
  startNanos : Nat := 0
  lastNanos : Nat := 0
  stack : List Name := []
  times : Std.HashMap Name ProfileEntry := {}
deriving Inhabited

def Rule.name (rule : Rule) : Name :=
  rule.origin.name

def Rule.hasExprMVar (rule : Rule) : Bool :=
  rule.pattern.hasExprMVar ||
    match rule.type with
    | .expr proof => proof.hasExprMVar
    | .proc proc => proc.hasExprMVar

def exprLevelParams (e : Expr) : Array Name :=
  (Lean.collectLevelParams {} e).params

def Rule.allLevelParams (rule : Rule) : Array Name :=
  let params := rule.levelParams ++ exprLevelParams rule.pattern
  match rule.type with
  | .expr proof => params ++ (exprLevelParams proof).filter (!params.contains ·)
  | .proc proc => params ++ (exprLevelParams proc).filter (!params.contains ·)

/-- Search state. -/
structure State where
  numSteps : Nat := 0
  depth : Nat := 0
  failedSubgoals : Array Expr := #[]
  /-- Per-run ruleset trees. `RefinedDiscrTree` resolves lazy entries during lookup, so each
  `getMatch` result must be stored back here for subsequent queries in the same tactic run. -/
  refinedRuleSetTrees : Std.HashMap Name (RefinedDiscrTree Rule) := {}
  /-- Stack of goal caches, one for each local-context depth used by introduced binders. -/
  goalCaches : Array GoalCache := #[]
  profile : ProfileState := {}

/-- Search context. -/
structure Context where
  config : Config := {}
  rulesets : Array Name := #[]
  explicitRules : Array Rule := #[]
  erased : Std.HashSet Name := {}
  /-- Side-condition discharger for proposition arguments. -/
  disch : ArgOrigin → Expr → MetaM (Option Expr) := fun _ _ => pure none
  lctxInitIndices : Nat

/-- Monad used by `apply_rulesets`. -/
abbrev ApplyRuleSetsM := ReaderT Context <| StateT State MetaM

/-- Ruleset data kept in the environment. -/
structure RuleSet where
  entries : Array Rule := #[]
  refinedTree : RefinedDiscrTree Rule := {}
  discrTree : DiscrTree Rule := {}
deriving Inhabited

/-- All registered rulesets. -/
structure RuleSets where
  ruleSets : Std.HashMap Name RuleSet := {}
  nextOrder : Nat := 0
deriving Inhabited

/-- Entry added to the global ruleset extension. -/
structure RuleSetExtEntry where
  ruleSetName : Name
  rule : Rule
  refinedKeys : List (Key × LazyEntry)
  discrPath : Array DiscrTree.Key
deriving Inhabited

def addFailedSubgoal (e : Expr) : ApplyRuleSetsM Unit := do
  unless (← read).config.collectFailedSubgoals do
    return ()

  unless e.isMVar do
    throwError m!"apply_ruleset bug! Trying to store unsolved goal that is not meta variable!"

  let numIndices := (← read).lctxInitIndices

  let type ← inferType e >>= instantiateMVars
  let xs : Array Expr :=
    -- collect all fvars that are in the goal and are not in the original context
    (← getLCtx).foldl (init := #[]) (fun xs decl =>
      if decl.index ≥ numIndices && type.containsFVar decl.fvarId then
        xs.push (.fvar decl.fvarId)
      else
        xs)

  let type ← mkForallFVars xs type

  modify (fun s =>
    { s with failedSubgoals := s.failedSubgoals.push type })

end Tactic.ApplyRuleSets
end Mathlib
