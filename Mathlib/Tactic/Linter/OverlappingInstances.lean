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

namespace Mathlib.Linter.OverlappingInstances

/--
Given an instance `e`, compute all data carrying classes that are
the type of `e` itself, or a child class, together with the indices of the parents of each
projection as they appear in this array.

This also records data-carrying non-structure inductive classes in a one-element array.
-/
private partial def getClassDataProjections (e : Expr) (acc : Array (List Nat × Expr) := #[])
    (parentIdx? : Option Nat := none) :
    StateRefT (NameMap Nat) MetaM (Array (List Nat × Expr)) := do
  let eType ← whnf <|← instantiateMVars <|← inferType e
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

/-- Given an array of projection types paired with the locations of their parents, returns `true`
if `p` is true for the types at any of the starting indices or their transitive parents. -/
private partial def hasAnyParentWhich (p : Expr → Bool)
    (projections : Array (List Nat × Expr)) (startingIdxs : List Nat) : Bool :=
  startingIdxs.any fun idx =>
    let (parentIdxs, cls) := projections[idx]!
    p cls || hasAnyParentWhich p projections parentIdxs

/-- Stores the local instance overlaps per class. The "keys" are the class, and the values are local
instances which have the class as a projection. The `Bool` in the value of each entry indicates
whether its type is exactly the key class.

The code constructing values of this class is responsible for ensuring that (1) every `Array` value
contains at least two elements (2) no element of the array appears twice.

We use an `Array` instead of a hashmap in order to record the overlaps in the order the classes
appear. -/
abbrev Overlaps := Array <| Expr × Array (Expr × Bool)

/-- Inserts `fvar₁` into the overlap for `cls` with `fvar₀`, assuming `fvar₀` is the representative
of the class. Since this is the only way we insert fvars and the representatives do not change, we
assume the representative `fvar₀` has already been inserted if the overlap exists, and do not
re-insert it. -/
def Overlaps.pushOverlap (fvar₀ : Expr × Bool) (cls : Expr) (fvar₁ : Expr × Bool)
    (overlaps : Overlaps) : Overlaps :=
  match overlaps.findIdx? (·.1 == cls) with
  | none => overlaps.push (cls, #[fvar₀, fvar₁])
  | some idx => overlaps.modify idx fun (cls, overlap) => (cls, overlap.push fvar₁)

/-- Returns `true` iff `fvar` is among the overlaps recorded for `cls`. -/
def Overlaps.containsAt (cls : Expr) (fvar : Expr) (overlaps : Overlaps) : Bool :=
  overlaps.any fun (cls', overlap) => cls == cls' && overlap.any (·.1 == fvar)

/--
Find data-carrying overlaps between the current local instances of the `MetaM` context.

The resulting `Overlaps` can be assumed to have at least two fvars present for each recorded class.
Further, it will only record overlaps at "maximal" nodes in the projection DAG; for example, if
`fvar₁` and `fvar₂` overlap on `cls`, the resulting `Overlaps` will not redundantly record their
overlap on any projection `cls.proj`.
-/
partial def findOverlappingDataInstances : MetaM Overlaps := do
  /- Records only the overlaps that will eventually be reported. This remains empty iff no
  messages should be logged. -/
  let mut overlaps : Overlaps := {}
  /- Associates all (data-carrying) typeclasses encountered to the first fvar that has a projection
  into the typeclass. We check every projection against this hashmap to detect if it has been seen
  before, and add it to the hashmap if not.

  The keys are classes, and the values are the representative fvars. The `Bool` indicates whether
  the class key is exactly the type of the associated fvar. We use this for error reporting. -/
  let mut encounteredClasses : Std.HashMap Expr (Expr × Bool) := {}
  for { fvar := fvar, .. } in ← getLocalInstances do
    unless (← fvar.fvarId!.getBinderInfo).isInstImplicit do continue
    let projClasses ← forallTelescope (← inferType fvar) fun xs _ ↦ do
      (← getClassDataProjections (mkAppN fvar xs) |>.run' {}).mapM fun (parentIdx?, expr) =>
        return (parentIdx?, ← mkForallFVars xs expr)
    for (parentIdxs, cls) in projClasses do
      if let some (fvar₀, clsIsTypeOfFVar₀) := encounteredClasses[cls]? then
        -- We have encountered a projection with this type already; we should now record an overlap,
        -- unless it is (or will be) redundant.
        -- Note that the actions in this branch are allowed to be "slow".

        /- Whether `fvar₀` yields the presciently-named class `parentClass` as a projection. This
        occurs iff either
        - `fvar₀` represents `parentClass` in `encounteredClasses`
        - or `fvar₀` is in an overlap on `parentClass`. -/
        let isProjectionOfFVar₀ (parentClass : Expr) :=
          encounteredClasses[parentClass]?.any (·.1 == fvar₀)
            || overlaps.containsAt parentClass fvar₀

        /- Tests if any (strict) parents of `cls` are yielded by `fvar₀` as a projection. If so,
        then `fvar` and `fvar₀` overlap (or will overlap) on some parent of the current `cls`.
        We should (only) record overlaps on the maximal parent class(es); the current overlap is
        therefore redundant, and we skip it. -/
        unless hasAnyParentWhich isProjectionOfFVar₀ projClasses parentIdxs do
          overlaps := overlaps.pushOverlap (fvar₀, clsIsTypeOfFVar₀) cls (fvar, parentIdxs.isEmpty)
      else
        -- `cls` has no representative yet, so insert the current fvar as the representative.
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

/-- `withSetOptionIn` currently breaks infotree searches, so we simply set `Bool` options
until this is fixed in [lean4#11313](https://github.com/leanprover/lean4/pull/11313).

This declaration will be removed in favor of `withSetOptionIn` when lean4#11313 lands. -/
private partial def withSetBoolOptionIn (x : CommandElab) : CommandElab
  | `(command| set_option $opt:ident $val in $cmd:command) => do
    match val.raw with
    | Syntax.atom _ "true"  =>
      withBoolOption opt.getId true <| withSetBoolOptionIn x cmd
    | Syntax.atom _ "false" =>
      withBoolOption opt.getId false <| withSetBoolOptionIn x cmd
    | _ => withSetBoolOptionIn x cmd
  | `(command| $_:command in $cmd:command) => withSetBoolOptionIn x cmd
  | stx => x stx
where
  /-- Set a `Bool` option in `CommandElabM`. Ideally, `CommandElabM` would have a
  `MonadWithOptions` instance to this effect. -/
  withBoolOption (n : Name) (val : Bool) (k : CommandElabM Unit) : CommandElabM Unit := do
    let opts := (← getOptions).setBool n val
    Command.withScope (fun scope => { scope with opts }) k


open Linter in
/--
Lints against data-carrying overlaps between instances in the local contexts of declarations.

Note: currently does not respect `set_option`.
-/
def overlappingInstances : Linter where
  run := withSetBoolOptionIn fun cmd => do
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

end Mathlib.Linter.OverlappingInstances
