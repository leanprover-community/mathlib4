/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Thomas R. Murrills
-/
module

public meta import Mathlib.Lean.Elab.InfoTree
public meta import Lean.Elab.Command
public meta import Mathlib.Lean.ContextInfo

/-!
# A linter to declarations with local instances that have overlapping data

We want to avoid this because this lead to instance diamonds
-/

open Lean Meta Elab

public meta section

namespace Mathlib.Tactic.OverlappingInstances

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

/-- An overlap between two local instances. This is introduced for readability, as all fields are
`Expr`s. -/
structure Overlap where
  /-- A local instance free variable whose data-carrying projections overlap with `fvar₂`. -/
  fvar₁ : Expr × Bool
  /-- A local instance free variable whose data-carrying projections overlap with `fvar₁`. -/
  fvar₂ : Expr × Bool
  /-- A type class on which `fvar₁` and `fvar₂`'s data-carrying projections overlap. -/
  overlap : Expr

/-- Find data-carrying overlaps between the current local instances of the `MetaM` context. -/
def findOverlappingDataInstances : MetaM (Array Overlap) := do
  let mut overlaps : Array Overlap := #[]
  /- The `Bool` indicates whether the given class key is exactly the type of the associated `fvar`
  value. This is used for error reporting. -/
  let mut insts : Std.HashMap Expr (Expr × Bool) := {}
  for { fvar := fvar₁, .. } in ← getLocalInstances do
    unless (← fvar₁.fvarId!.getBinderInfo).isInstImplicit do continue
    let projClasses ← forallTelescope (← inferType fvar₁) fun xs _ ↦ do
      (← getStructureDataProjections (mkAppN fvar₁ xs) |>.run' {}).mapM (mkForallFVars xs)
    for h : clsIdx in 0...projClasses.size do
      let cls := projClasses[clsIdx]
      if let some (fvar₂, isTypeOfFVar₂) := insts[cls]? then
        overlaps := overlaps.push {
            fvar₁ := (fvar₁, clsIdx = 0)
            fvar₂ := (fvar₂, isTypeOfFVar₂)
            overlap := cls }
        if clsIdx = 0 && isTypeOfFVar₂ then
          break -- Don't consider further projections of this local instance
      else
        insts := insts.insert cls (fvar₁, clsIdx = 0)
  return overlaps

