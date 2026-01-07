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

/-- Lints against data-carrying overlaps between instances in the local contexts of declarations. -/
register_option linter.overlappingInstances : Bool := {
  defValue := false
  descr := "enable the overlapping instances linter. This only lints against data-carrying \
    overlaps and on declaration bodies."
}

/-- Surrounds an expression representing the type of an instance with square brackets, taking care
to group and nest appropriately. -/
private def _root_.Lean.MessageData.ofInstanceType (e : Expr) : MessageData :=
  m!"{e}".sbracket

open Linter in
/--
Lints against data-carrying overlaps between instances in the local contexts of declarations.

Note: currently does not respect `set_option`.
-/
def overlappingInstances : Linter where
  run cmd := do
    unless getLinterValue linter.overlappingInstances (← getLinterOptions) do
      return
    /- TODO: use `withSetOptionIn` when either it's fixed via the open lean PR or
    `unusedFintypeInType` lands with a workaround -/
    -- Note: we don't break on errors; we want to lint even on partial declarations
    for t in ← getInfoTrees do
      for (ctx, info) in t.getDeclBodyInfos do
        let (lctx, localInstances, remainingType?) ← do
          match info with
          | .ofTacticInfo i => do
            let g :: _ := i.goalsBefore | continue
            let some decl := i.mctxBefore.findDecl? g | continue
            pure (decl.lctx, some decl.localInstances, some decl.type)
          | .ofTermInfo i
          | .ofPartialTermInfo i => pure (i.lctx, none, i.expectedType?)
          | _ => continue -- Unreachable. TODO: refactor?
        let namingCtx : NamingContext := {
          currNamespace := ← getCurrNamespace
          openDecls     := ← getOpenDecls
        }
        let outerEnv ← getEnv
        ctx.runMetaMWithMessages lctx (localInstances := localInstances) <|
          withRef (← getRef) do
          letI forallTelescope? expectedType? (k : Array Expr → Option Expr → MetaM Unit) :=
            if let some type := expectedType? then
              forallTelescope type fun fvars ty => k fvars ty
            else
              k #[] expectedType?
          forallTelescope? remainingType? fun newFVars _ => do
            let overlaps ← findOverlappingDataInstances
            unless overlaps.isEmpty do
              let mut collectedByOverlap : Std.HashMap Expr (Std.HashSet (Expr × Bool)) := {}
              for { fvar₁, fvar₂, overlap } in overlaps do
                collectedByOverlap := collectedByOverlap.alter overlap fun set? =>
                  (set?.getD ∅).insert fvar₁ |>.insert fvar₂

              -- For now, no hovers, since the name clashes with the aux decl of the same name in
              -- the lctx. TODO: account for this.
              let mut msg := m!"The \
                {if let some decl := ctx.parentDecl? then
                  m!"declaration `{privateToUserName decl}`"
                else
                  "current declaration"} \
                has instance hypotheses which overlap on data-carrying components."

              for (overlap, fvars) in collectedByOverlap do
                let (direct, indirect) := fvars.toList.partitionMap fun (fvar, isDirect) =>
                  if isDirect then .inl fvar else .inr fvar
                let overlapType := m!"`{.ofInstanceType overlap}`"
                let indirectTypes := MessageData.andList <|← indirect.mapM fun fvar =>
                  return m!"`{.ofInstanceType <|← inferType fvar}`"
                msg := msg ++ "\n\n"
                msg := msg ++
                  if indirect.isEmpty then
                    -- Necessarily plural:
                    m!"There are {direct.length} instances of {overlapType}."
                  else
                    if direct.isEmpty then
                      m!"{overlapType} is provided by {indirectTypes}."
                    else if let [direct] := direct then
                      m!"There is an instance of {overlapType} in the local context, but it is \
                        also provided by {indirectTypes}."
                    else
                      m!"There are {direct.length} instances of {overlapType} in the local \
                        context, and it is also provided by {indirectTypes}."
              -- TODO: better logging location
              -- TODO: alert user to `variable`s, possibly suggest `omit` when relevant
              logWarning <|← addMessageContextFull msg

initialize addLinter overlappingInstances
