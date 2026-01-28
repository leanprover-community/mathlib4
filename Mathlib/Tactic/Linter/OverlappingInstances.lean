/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Init

/-
# A linter to declarations with local instances that have overlapping data

We want to avoid this because this lead to instance diamonds
-/

open Lean Meta Batteries Tactic Lint

public meta section

/-- Given an instance `e`, conpute return all data carrying classes that are
the type of `e` itself, or a child class. -/
private partial def getStructureDataProjections (e : Expr) (acc : Array Expr := #[]) :
    StateRefT NameSet MetaM (Array Expr) := do
  let eType ← whnf (← inferType e)
  if ← isProp eType then return acc
  let .const structName us := eType.getForallBody.getAppFn
    | throwError "{e} is not an instance of a structure"
  if (← get).contains structName then return acc
  modify (·.insert structName)
  let some info := getStructureInfo? (← getEnv) structName | return acc
  info.parentInfo.foldlM (init := acc.push eType) fun acc info ↦ do
    if ← isInstance info.projFn then
      let proj := Expr.app (mkAppN (.const info.projFn us) eType.getAppArgs) e
      getStructureDataProjections proj acc
    else
      return acc

/-- Run the overlapping instances linter on `declName`. -/
def findDuplicateDataInstances (declName : Name) : CoreM (Option MessageData) := MetaM.run' do
  Core.checkSystem "overlappingInstances"
  forallTelescope (← getConstInfo declName).type fun _ _ ↦ do
  let mut result := none
  let mut insts : Std.HashMap Expr Expr := {}
  for { fvar, .. } in ← getLocalInstances do
    unless (← fvar.fvarId!.getBinderInfo).isInstImplicit do continue
    let projClasses ← forallTelescope (← inferType fvar) fun xs _ ↦ do
      (← getStructureDataProjections (mkAppN fvar xs) |>.run' {}).mapM (mkForallFVars xs)

    for cls in projClasses do
      if let some fvar' := insts[cls]? then
        let type ← inferType fvar; let type' ← inferType fvar'
        if type == type' then
          result := m!"{result.getD m!""}There are multiple different instances of `{type}`\n\n"
          break
        else
          result := m!"{result.getD m!""}`{type}` and `{type'}` both imply `{cls}`\n\n"
      else
        insts := insts.insert cls fvar
  result.mapM addMessageContextFull

/-- A linter for declarations which have instance hypotheses that have overlapping data. -/
@[env_linter] def overlappingInstances : Lint.Linter where
  noErrorsFound := "No declarations have overlapping instance arguments"
  errorsFound := "Some declarations have overlapping instance arguments"
  test := fun declName => do
    if declName.isInternal then return none
    if congrKindsExt.contains (← getEnv) declName then return none
    findDuplicateDataInstances declName
