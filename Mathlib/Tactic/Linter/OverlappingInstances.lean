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

/-- Stores the local instance overlaps per class. The keys are the class, and the values are local
instances which have the class as a projection. The `Bool` value of each entry indicates whether
its type is exactly the key class. We use an `ExprMap Bool` here instead of e.g. an
`Array (Expr × Bool`) to ensure that each local instance is recorded only once. There may be
assumed to be at least two local instances per class. -/
abbrev Overlaps := ExprMap (ExprMap Bool)

/-- Inserts an overlap into `Overlaps`. -/
def Overlaps.insert (cls : Expr) (fvar₁ fvar₂ : Expr × Bool) (overlaps : Overlaps) : Overlaps :=
  overlaps.alter cls fun map? =>
    map?.getD ∅ |>.insert fvar₁.1 fvar₁.2 |>.insert fvar₂.1 fvar₂.2

/-- Find data-carrying overlaps between the current local instances of the `MetaM` context. -/
def findOverlappingDataInstances : MetaM Overlaps := do
  let mut overlaps : Overlaps := {}
  /- Records all instances encountered, and so is distinct from `overlaps`. The `Bool` indicates
  whether the given class key is exactly the type of the associated `fvar` value. -/
  let mut insts : Std.HashMap Expr (Expr × Bool) := {}
  for { fvar := fvar₁, .. } in ← getLocalInstances do
    unless (← fvar₁.fvarId!.getBinderInfo).isInstImplicit do continue
    let projClasses ← forallTelescope (← inferType fvar₁) fun xs _ ↦ do
      (← getStructureDataProjections (mkAppN fvar₁ xs) |>.run' {}).mapM (mkForallFVars xs)
    /- The fvars that are either projections of the current fvar or have projections equal to the
    current fvar. In both cases we want to ignore further matches against these fvars.

    For less verbose error reporting, we would ideally also ignore overlaps which share a parent;
    we may eventually want a different data structure for `projClasses` for this. -/
    let mut done : Array Expr := #[]
    for h : clsIdx in 0...projClasses.size do
      let cls := projClasses[clsIdx]
      if let some (fvar₂, isTypeOfFVar₂) := insts[cls]? then
        unless done.contains fvar₂ do
          overlaps := overlaps.insert cls (fvar₁, clsIdx = 0) (fvar₂, isTypeOfFVar₂)
          if clsIdx = 0 || isTypeOfFVar₂ then
            done := done.push fvar₂ -- Don't consider `fvar₂` any more
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

/--
Creates a description of the current declaration in messages: "declaration <declName>" if the `parentDecl?` is known, and "current declaration" otherwise. May be preceded by "the".

TODO: For now, this does not produce hovers on `<declName>`, since the name may clash with the aux
decl of the same name in the local context. In the future, we should account for this, and render
the name within a more appropriate message context. The type of this declaration is therefore
subject to change.
-/
def _root_.Lean.Elab.ContextInfo.toDeclDescr (ctx : ContextInfo) : MessageData :=
  if let some decl := ctx.parentDecl? then
    m!"declaration `{privateToUserName decl}`"
  else
    "current declaration"

/-- Creates a message describing the violations captured in `Overlaps`, assumed to be nonempty. -/
def Overlaps.toMsg (declDescr : MessageData) (overlaps : Overlaps) : MetaM MessageData := do
  let mut msg := m!"The {declDescr} \
    has instance hypotheses which overlap on data-carrying components."
  for (overlap, fvars) in overlaps do
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
        else if let [_] := direct then
          m!"There is an instance of {overlapType} in the local context, but it is \
            also provided by {indirectTypes}."
        else
          m!"There are {direct.length} instances of {overlapType} in the local \
            context, and it is also provided by {indirectTypes}."
  addMessageContextFull msg

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
          | _ => continue -- Ought to be unreachable. TODO: check or refactor?
        let outerRef ← getRef
        ctx.runMetaMWithMessages lctx (localInstances := localInstances) <|
          -- TODO: better logging location
          withRef outerRef do
          /- If there's a remaining expected type, then telescope into it in case it contains more
          instance hypotheses. For now, we don't use the new fvars or remaining type for anything,
          but these could be passed to `k`. -/
          let forallTelescopeRemainingType (k : MetaM Unit) :=
            if let some type := remainingType? then
              forallTelescope type fun _ _ => k
            else
              k
          forallTelescopeRemainingType do
            let overlaps ← findOverlappingDataInstances
            unless overlaps.isEmpty do
              -- TODO: alert user to `variable`s, possibly suggest `omit` when relevant
              logWarning <|← overlaps.toMsg ctx.toDeclDescr

initialize addLinter overlappingInstances
