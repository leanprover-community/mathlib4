/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.Elab.Command
public import Lean.Linter.Basic
public import Lean.Meta.Instances
public meta import Lean.Meta.Tactic.TryThis
public import Mathlib.Tactic.DeclarationNames

/-!
# The instance diamond linter

The `instanceDiamond` linter checks that instance declarations do not introduce
non-defeq diamonds in the typeclass hierarchy.

For each instance whose return type is a class with diamond inheritance
(multiple paths to a common ancestor), the linter verifies that all paths
yield definitionally equal results at `reducible_and_instances` transparency.
-/

meta section

open Lean Meta Elab Command Linter

namespace Mathlib.Linter

/-- The `instanceDiamond` linter checks that instance declarations do not introduce
non-defeq diamonds in the typeclass hierarchy.

For each instance whose return type is a class with diamond inheritance,
verifies that all paths through the parent hierarchy to a common ancestor
are definitionally equal at `reducible_and_instances` transparency. -/
public register_option linter.instanceDiamond : Bool := {
  defValue := true
  descr := "enable the instance diamond linter"
}

namespace InstanceDiamond

/-- Compose a sequence of structure projections on an expression.

Given `e : S args...` and a list of projection function names `[p₁, p₂, ...]`,
returns `p₂ (p₁ e)` (with appropriate universe and type arguments). -/
private def applyProjectionPath (e : Expr) (path : List Name) : MetaM Expr := do
  let mut e := e
  for projName in path do
    let type ← whnf (← inferType e)
    let .const _ us := type.getAppFn
      | throwError "applyProjectionPath: expected structure type, got {type}"
    e := mkAppN (.const projName us) (type.getAppArgs.push e)
  return e

/-- Walk two expressions in parallel, finding the most specific subexpression where they diverge.
Returns `(lhsSub, rhsSub)` — the smallest pair of differing subexpressions. -/
private partial def findDivergence (lhs rhs : Expr) (fuel : Nat := 32) : MetaM (Expr × Expr) := do
  if fuel == 0 || lhs == rhs then return (lhs, rhs)
  -- If same head function, find first differing argument
  if lhs.getAppFn == rhs.getAppFn && lhs.getAppNumArgs == rhs.getAppNumArgs then
    let args1 := lhs.getAppArgs
    let args2 := rhs.getAppArgs
    for i in [:args1.size] do
      if args1[i]! != args2[i]! then
        return ← findDivergence args1[i]! args2[i]! (fuel - 1)
    return (lhs, rhs)
  -- If both are lambdas, descend into body (even if binder types differ,
  -- since the interesting divergence is usually in the body, not the type)
  match lhs, rhs with
  | .lam _ t1 b1 bi, .lam _ _ b2 _ =>
    withLocalDecl `x bi t1 fun x =>
      findDivergence (b1.instantiate1 x) (b2.instantiate1 x) (fuel - 1)
  | _, _ => return (lhs, rhs)

/-- A single diamond failure: the warning message and the lhs/rhs expressions that failed defeq. -/
private structure DiamondFailure where
  message : MessageData
  lhs : Expr
  rhs : Expr
  pathI : List Name
  pathJ : List Name

/-- Find all diamond failures for an instance expression of the given class.

For each pair of direct parents that share a common ancestor,
checks that the two projection paths yield definitionally equal results. -/
private def findDiamondFailures (instExpr : Expr) (structName : Name) :
    MetaM (Array DiamondFailure) := do
  let env ← getEnv
  let parents := (getStructureInfo env structName).parentInfo
  if parents.size < 2 then return #[]
  -- For each parent, compute its ancestor set (including itself)
  let mut parentAncestors : Array (StructureParentInfo × NameSet) := #[]
  for p in parents do
    let ancestors ← getAllParentStructures p.structName
    let ancestorSet := ancestors.foldl (init := NameSet.empty.insert p.structName)
      fun s n => s.insert n
    parentAncestors := parentAncestors.push (p, ancestorSet)
  -- Collect all common ancestors with the pair of parents that witness them
  let mut diamondPairs : Array (Name × StructureParentInfo × StructureParentInfo) := #[]
  for i in [:parentAncestors.size] do
    for j in [i + 1 : parentAncestors.size] do
      let (pi, piAncestors) := parentAncestors[i]!
      let (pj, pjAncestors) := parentAncestors[j]!
      -- Find common ancestors
      for ancestor in piAncestors.toList do
        if !pjAncestors.contains ancestor then continue
        diamondPairs := diamondPairs.push (ancestor, pi, pj)
  -- Check each diamond pair
  let mut rawFailures : Array (Name × List Name × List Name × Expr × Expr) := #[]
  for (ancestor, pi, pj) in diamondPairs do
    -- Get canonical paths from each parent to the ancestor
    let some pathI := if ancestor == pi.structName then some []
      else getPathToBaseStructure? env ancestor pi.structName
      | continue
    let some pathJ := if ancestor == pj.structName then some []
      else getPathToBaseStructure? env ancestor pj.structName
      | continue
    -- Full paths from the instance: [parent_proj] ++ [path_to_ancestor]
    let fullPathI := pi.projFn :: pathI
    let fullPathJ := pj.projFn :: pathJ
    -- Build and compare the expressions
    let lhs ← applyProjectionPath instExpr fullPathI
    let rhs ← applyProjectionPath instExpr fullPathJ
    let ok ← withNewMCtxDepth <| withReducibleAndInstances <| isDefEq lhs rhs
    unless ok do
      rawFailures := rawFailures.push (ancestor, fullPathI, fullPathJ, lhs, rhs)
  -- Root-cause filter: keep only the most primitive failing ancestors.
  -- If B fails and one of B's ancestors A also fails, then B's failure is
  -- a consequence of A's — suppress B.
  let failedNames := rawFailures.map (·.1)
  let mut failures : Array DiamondFailure := #[]
  for (ancestor, fullPathI, fullPathJ, lhs, rhs) in rawFailures do
    let ancestorsOfThis ← getAllParentStructures ancestor
    let dominated := failedNames.any fun other =>
      other != ancestor && ancestorsOfThis.any (· == other)
    unless dominated do
      -- Find which fields of the ancestor differ, and show their reduced values
      let fields := getStructureFields env ancestor
      let mut differingFieldMsgs : Array MessageData := #[]
      for field in fields do
        try
          let projName := ancestor ++ field
          let lhsField ← applyProjectionPath lhs [projName]
          let rhsField ← applyProjectionPath rhs [projName]
          let eq ← withNewMCtxDepth <| withReducibleAndInstances <| isDefEq lhsField rhsField
          unless eq do
            -- Find where the unreduced field expressions structurally diverge,
            -- then whnf the divergence point to show the actual differing values.
            let (divLhs, divRhs) ← findDivergence lhsField rhsField
            let divLhs ← withReducibleAndInstances <| whnf divLhs
            let divRhs ← withReducibleAndInstances <| whnf divRhs
            let lhsFmt ← ppExpr divLhs
            let rhsFmt ← ppExpr divRhs
            differingFieldMsgs := differingFieldMsgs.push
              m!"    {field}:\n      lhs: {lhsFmt}\n      rhs: {rhsFmt}"
        catch _ => pure ()
      let fieldMsg := if differingFieldMsgs.isEmpty then m!""
        else m!"\n  Differing fields:\n" ++ .joinSep differingFieldMsgs.toList "\n"
      failures := failures.push {
        message := m!"instance diamond at {ancestor}:\
           \n  the projection chains {fullPathI} and {fullPathJ}\
           \n  produce results which are not definitionally equal\
           \n  at `with_reducible_and_instances` transparency.\
           {fieldMsg}"
        lhs, rhs
        pathI := fullPathI
        pathJ := fullPathJ }
  return failures

/-- Check a single declaration for instance diamonds.
Returns the warning message and example statements demonstrating each failure. -/
private def checkInstanceDiamond (declName : Name) :
    MetaM (Option (MessageData × Array String)) := do
  unless ← isInstance declName do return none
  let info ← getConstInfo declName
  -- Skip instances with sorry in their body
  if info.value?.any (·.hasSorry) then return none
  forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName))
      fun args retTy => do
    -- Reduce the return type head to handle reducible aliases
    let retTy ← whnfR retTy
    let .const structName _ := retTy.getAppFn | return none
    let env ← getEnv
    unless isStructure env structName do return none
    unless isClass env structName do return none
    -- Check that the class actually has diamond inheritance (≥ 2 parents)
    let parents := (getStructureInfo env structName).parentInfo
    if parents.size < 2 then return none
    let instExpr := mkAppN (← mkConstWithLevelParams declName) args
    let failures ← findDiamondFailures instExpr structName
    if failures.isEmpty then return none
    -- Build example statements for each failure.
    -- Wrap instExpr in mdata with `pp.explicit` so the pretty-printer shows all
    -- implicit arguments for just the instance application (e.g. `@inst n α ...`),
    -- making the example reparsable without needing string assembly.
    let explicitInst := Expr.mdata (KVMap.empty.setBool `pp.explicit true) instExpr
    let mut messages : Array MessageData := #[]
    let mut examples : Array String := #[]
    for f in failures do
      let displayLhs ← applyProjectionPath explicitInst f.pathI
      let displayRhs ← applyProjectionPath explicitInst f.pathJ
      let eq ← mkEq displayLhs displayRhs
      let prop ← mkForallFVars args eq
      let propStr := toString (← ppExpr prop)
      let tactic := if args.isEmpty then "with_reducible_and_instances rfl"
        else "intros; with_reducible_and_instances rfl"
      let ex := s!"example : {propStr} := by {tactic}"
      messages := messages.push (f.message ++ m!"\n{ex}")
      examples := examples.push ex
    return some (.joinSep messages.toList "\n", examples)

@[inherit_doc linter.instanceDiamond]
def instanceDiamondLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.instanceDiamond (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- Only look at declaration commands
  unless stx.isOfKind ``Lean.Parser.Command.declaration do return
  -- Get the declaration names added by this command
  let declNames ← getNamesFrom (stx.getPos?.getD default)
  for id in declNames do
    let declName := id.getId
    if declName.hasMacroScopes then continue
    let result ← liftTermElabM <| Meta.MetaM.run' <| checkInstanceDiamond declName
    if let some (msg, examples) := result then
      logLint linter.instanceDiamond stx msg
      -- Emit "Try this:" suggestions to insert example statements after the declaration
      if !examples.isEmpty then
        let exampleStr := "\n\n" ++ "\n\n".intercalate examples.toList
        let endPos := stx.getTailPos?.getD default
        let insertSpan := Syntax.atom (SourceInfo.synthetic endPos endPos) ""
        liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion stx
          { suggestion := .string exampleStr
            toCodeActionTitle? := some fun _ => "Insert instance diamond examples" }
          (origSpan? := insertSpan)

initialize addLinter instanceDiamondLinter

end Mathlib.Linter.InstanceDiamond
