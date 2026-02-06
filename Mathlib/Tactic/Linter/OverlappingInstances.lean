/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Thomas R. Murrills
-/
module

public meta import Lean.Elab.Command
public meta import Mathlib.Lean.ContextInfo
public meta import Mathlib.Lean.Elab.InfoTree
public meta import Mathlib.Lean.Message

/-!
# A linter to declarations with local instances that have overlapping data

We want to avoid this because this lead to instance diamonds
-/

open Lean Meta Elab Command

public meta section

namespace Mathlib.Tactic.OverlappingInstances

/--
Given an instance `e`, compute all data carrying classes that are
the type of `e` itself, or a child class, together with the indices of the parents of each
projection as they appear in this array.

This also records data-carrying non-structure inductive classes in a one-element array.
-/
private partial def getClassDataProjections (e : Expr) (acc : Array (List Nat × Expr) := #[])
    (parentIdx? : Option Nat := none) :
    StateRefT (NameMap Nat) MetaM (Array (List Nat × Expr)) := do
  let eType ← whnf (← inferType e)
  if ← isProp eType then return acc
  let .const structName us := eType.getForallBody.getAppFn
    | throwError "`{e}` is not an instance of a structure"
  -- Check if already recorded
  if let some structIdx := (← get).get? structName then
    if let some parentIdx := parentIdx? then
      -- `e` has already been recorded, but is being encountered as the child of a new parent at
      -- `parentIdx`. Add this parent index to `e`'s original parent indices.
      return acc.modify structIdx fun (parents, struct) => (parentIdx :: parents, struct)
    -- In ordinary usage, where only the first invocation of `getStructureDataProjections` has no
    -- parent, this case cannot be reached.
    return acc
  -- Record current class and recurse
  let currentIdx := acc.size
  let acc := acc.push (parentIdx?.toList, eType)
  if let some info := getStructureInfo? (← getEnv) structName then
    -- Record the index at which this structure occurs in `acc`, so we can add to its parents later
    -- if it is encountered as a projection of something else.
    modify (·.insert structName currentIdx)
    info.parentInfo.foldlM (init := acc) fun acc info ↦ do
      if ← isInstance info.projFn then
        let proj := Expr.app (mkAppN (.const info.projFn us) eType.getAppArgs) e
        getClassDataProjections proj acc currentIdx
      else
        return acc
  else
    -- This case should only be reached by non-structure inductive classes, and therefore only
    -- occur at the root. We still want to record these to warn on duplicate inductive classes.
    return acc

/-- Given an array of projection types paired with indices for their parents, returns `true` if `p`
is true for the types at any of the starting indices or their transitive parents. -/
private partial def hasParentP! (projections : Array (List Nat × Expr)) (p : Nat → Expr → Bool)
    (startingIdxs : List Nat) : Bool :=
  match startingIdxs with
  | []          => false
  | idx :: idxs =>
    let (parentIdxs, expr) := projections[idx]!
    p idx expr || hasParentP! projections p parentIdxs || hasParentP! projections p idxs

/-- Stores the local instance overlaps per class. The keys are the class, and the values are local
instances which have the class as a projection. The `Bool` value of each entry indicates whether
its type is exactly the key class. We use an `ExprMap Bool` here instead of e.g. an
`Array (Expr × Bool)` to ensure that each local instance is recorded only once. There may be
assumed to be at least two local instances per class. -/
abbrev Overlaps := ExprMap (ExprMap Bool)

/-- Inserts an overlap into `Overlaps`. -/
def Overlaps.insert (cls : Expr) (fvar₁ fvar₂ : Expr × Bool) (overlaps : Overlaps) : Overlaps :=
  overlaps.alter cls fun map? =>
    map?.getD ∅ |>.insert fvar₁.1 fvar₁.2 |>.insert fvar₂.1 fvar₂.2

/-- Returns `true` iff `fvar₁` and `fvar₂` overlap on the `cls` projection typeclass. -/
def Overlaps.containsOverlapOn (fvar₁ fvar₂ : Expr) (cls : Expr) (overlaps : Overlaps) : Bool :=
  match overlaps[cls]? with
  | none => false
  | some overlap => overlap.contains fvar₁ && overlap.contains fvar₂

/--
Find data-carrying overlaps between the current local instances of the `MetaM` context.

The resulting `Overlaps` can be assumed to have at least two fvars present for each recorded class.
Further, it will only record overlaps at "maximal" nodes in the projection DAG; for example, if
`fvar₁` and `fvar₂` overlap on `cls`, the resulting `Overlaps` will not redundantly record their
overlap on any projection `cls.proj`.
-/
def findOverlappingDataInstances : MetaM Overlaps := do
  /- Records only the overlaps that will eventually be reported. This remains empty iff no
  messages should be logged. -/
  let mut overlaps : Overlaps := {}
  /- Associates all (data-carrying) typeclasses encountered to the first fvar that has a projection
  into the typeclass. We check every projection against this hashmap to detect if it has been seen
  before, and add it to the hashmap if not.

  The keys are classes, and the values are fvars. The `Bool` indicates whether the class key is
  exactly the type of the associated fvar. We use this for error reporting. -/
  let mut encounteredClasses : Std.HashMap Expr (Expr × Bool) := {}
  for { fvar := fvar, .. } in ← getLocalInstances do
    unless (← fvar.fvarId!.getBinderInfo).isInstImplicit do continue
    let projClasses ← forallTelescope (← inferType fvar) fun xs _ ↦ do
      (← getClassDataProjections (mkAppN fvar xs) |>.run' {}).mapM fun (parentIdx?, expr) =>
        return (parentIdx?, ← mkForallFVars xs expr)
    for (parentIdxs, cls) in projClasses, idx in 0...* do
      if let some (fvar₀, clsIsTypeOfFVar₀) := encounteredClasses[cls]? then
        -- We have encountered a projection with this type already; we should now record an overlap,
        -- unless it is (or will) be redundant.
        -- Note that the actions in this branch are allowed to be "slow".
        let shouldIgnoreCurrent (parentIdx : Nat) (parentClass : Expr) :=
          -- If a parent further on in `projClasses` will overlap via `fvar₀`, ignore this child.
          -- Note that we can assume `false`, as only the first array element has `true`.
          (idx < parentIdx && encounteredClasses[parentClass]?.isEqSome (fvar₀, false))
          -- If `fvar` and `fvar₀` already overlap on a parent, ignore this redundant overlap.
            || overlaps.containsOverlapOn fvar fvar₀ parentClass
        -- See if any parent of the current projection, starting with the immediate `parentIdxs`,
        -- imply it is redundant.
        unless hasParentP! projClasses shouldIgnoreCurrent parentIdxs do
          overlaps := overlaps.insert cls (fvar, parentIdxs.isEmpty) (fvar₀, clsIsTypeOfFVar₀)
      else
        encounteredClasses := encounteredClasses.insert cls (fvar, parentIdxs.isEmpty)
  return overlaps

/-- Lints against data-carrying overlaps between instances in the local contexts of declarations. -/
register_option linter.overlappingInstances : Bool := {
  defValue := false
  descr := "enable the overlapping instances linter. This only lints against data-carrying \
    overlaps and on declaration bodies."
}

/--
Creates a description of the current declaration in messages: "declaration `<declName>`" if the `parentDecl?` is known, and "current declaration" otherwise. May be preceded by "the".

TODO: For now, this does not produce hovers on `<declName>`, since the name may clash with the aux
decl of the same name in the local context. In the future, we should account for this, and render
the name within a more appropriate message context. The type of this declaration is therefore
subject to change.
-/
private def _root_.Lean.Elab.ContextInfo.toDeclDescr (ctx : ContextInfo) : MetaM MessageData := do
  if let some decl := ctx.parentDecl? then
    let decl ← unresolveNameGlobal decl
    return m!"declaration `{decl}`"
  else
    return "current declaration"

/-- Creates a message describing the violations captured in `Overlaps`, assumed to be nonempty. -/
def Overlaps.toMsg (declDescr : MessageData) (overlaps : Overlaps) : MetaM MessageData := do
  let mut msg := m!"The {declDescr} \
    has instance hypotheses which provide conflicting versions of the same data. Specifically:"
  let mut msgs := #[]
  for (overlap, fvars) in overlaps do
    let (instsOfOverlap, parentsOfOverlap) :=
      fvars.toList.partitionMap fun (fvar, isFVarType) =>
        if isFVarType then .inl fvar else .inr fvar
    let overlapType := m!"`{.ofInstanceBinderType overlap}`"
    let parentTypesOfOverlap := MessageData.andList <|← parentsOfOverlap.mapM fun fvar =>
      return m!"`{.ofInstanceBinderType <|← inferType fvar}`"
    let parentTypesOfOverlap :=
      m!"{if let [_, _] := parentsOfOverlap then m!"both " else m!""}{parentTypesOfOverlap}"

    msgs := msgs.push <|
      if parentsOfOverlap.isEmpty then
        -- Necessarily plural:
        m!"There are {instsOfOverlap.length} instances of {overlapType}."
      else
        match instsOfOverlap with
        | []  => m!"{overlapType} is provided by {parentTypesOfOverlap}."
        | [_] => m!"There is an instance of {overlapType} in the local context, but it is \
            also provided by {parentTypesOfOverlap}."
        | _   => m!"There are {instsOfOverlap.length} instances of {overlapType} in the local \
            context, and it is also provided by {parentTypesOfOverlap}."
  -- Create a bulleted list if there are multiple messages, otherwise just a single line
  msg := if h : msgs.size = 1 then msg ++ "\n\n" ++ msgs[0] else
    msgs.foldl (init := msg ++ "\n") fun accMsg newMsg => m!"{accMsg}\n• {newMsg}"
  msg := msg ++ m!"\n\n\
    There should only be a single instance of these data-carrying typeclasses in the local context \
    at a time. Consider choosing different instance hypotheses for the {declDescr}."
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
        let some (lctx, localInstances?, remainingType?) := info.getLCtxBefore?
          | continue
        -- TODO: better logging location
        let outerRef ← getRef
        ctx.runMetaMWithMessages lctx (localInstances := localInstances?) <|
          withRef outerRef do
          /- If there's a remaining expected type, then telescope into it in case it contains more
          instance hypotheses. For now, we don't use the new fvars or return type for anything. -/
          remainingType?.elim id (forallTelescope · fun _ _ => ·) do
            let overlaps ← findOverlappingDataInstances
            unless overlaps.isEmpty do
              -- TODO: alert user to `variable`s, possibly suggest `omit` when relevant
              logWarning <|← overlaps.toMsg <|← ctx.toDeclDescr

initialize addLinter overlappingInstances

end Mathlib.Tactic.OverlappingInstances
