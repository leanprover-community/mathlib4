/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Thomas R. Murrills
-/
module

public meta import Lean.Elab.Command
public meta import Mathlib.Lean.ContextInfo
public meta import Mathlib.Lean.Elab.InfoTree

public meta import Mathlib.Tactic.Linter.UnusedInstancesInType

/-!
# A linter for declarations with local instances that have overlapping data

If the same data can be obtained from two different instances in the local context, we risk having
non-defeq versions of that data. This situation, both for declarations and more broadly, is known
as an "instance diamond". This linter warns against instance diamonds in local contexts.

This is a syntax linter. It is run on partially and fully elaborated declarations.

To find diamonds, we compute all data carrying parent classes of any given class.
For classes that are propositions or aren't structures, this returns the class itself.
If any of these classes is duplicated, we throw a warning.

A common case where this linter may fire is if the same type class assumption is given in both a
`variable` statement and a declaration. This kind of variable shadowing does not actually produce
declarations with duplicate type class assumptions, but it is still not desirable.


## TODO

Support declarations without bodies (`structure`s/`class`es/`inductive`s etc.)

-/

open Lean Meta Elab Command

meta section

namespace Mathlib.Linter.OverlappingInstances

/-- Clear the instances from the given application.
This is used to deal with classes that have instance parameters. -/
def eraseInstances (e : Expr) : MetaM Expr := do
  e.withApp fun f args ↦ do
  let finfo ← getFunInfo f
  let mut args := args
  for param in finfo.paramInfo, i in *...args.size do
    if param.binderInfo.isInstImplicit then
      args := args.set! i default
  return mkAppN f args

/-- Compute the data carrying parent classes of `cls`.
This excludes parent classes that have a data carrying parent themselves.
The reason to exclude such classes is that if there is a duplication in such a class,
then there will necessarily also be a duplication in all of its parents.
If `cls` is a `Prop` or a non-structure class, this simply returns `#[cls]`.

The resulting expressions contain bound variables that correspond to the parameters of `cls`.
The universe levels and bound variables need to be instantiated to get concrete data projections.
-/
partial def getAbstractDataProjections (cls : Name) : CoreM (Array Expr) := do
  let cinfo ← getConstInfo cls
  MetaM.run' <| forallTelescope cinfo.type fun xs _ ↦ do
    withLocalDeclD `self (mkAppN (.const cls (cinfo.levelParams.map .param)) xs) fun inst ↦ do
      go cls inst #[] xs |>.run' {}
where
  go (cls : Name) (inst : Expr) (acc : Array Expr) (xs : Array Expr) :
      StateRefT NameSet MetaM (Array Expr) := do
    let type ← whnf (← inferType inst)
    let mut acc := acc
    let mut anyParent := false
    if let some info := getStructureInfo? (← getEnv) cls then
      let .const _ us := type.getAppFn | panic! s!"`{inst} is not an instance"
      for info in info.parentInfo do
        let parent := info.structName
        if (← get).contains parent then continue
        modify (·.insert parent)
        if (← getConstInfo parent).type.getForallBody.isProp then continue
        let proj := Expr.app (mkAppN (.const info.projFn us) type.getAppArgs) inst
        acc ← go parent proj acc xs
        anyParent := true
    if !anyParent then
      acc := acc.push (← eraseInstances (type.abstract xs))
    return acc

/-- A cache for the result of `getAbstractDataProjections`. -/
initialize dataProjectionCache : IO.Ref (NameMap (Array Expr)) ← IO.mkRef {}

/-- Return the result of `getAbstractDataProjections`, using a global cache.
To ensure soundness, the cache is only used for imported declarations. -/
def getAbstractDataProjectionsCached (cls : Name) : CoreM (Array Expr) := do
  if (← getEnv).isImportedConst cls then
    if let some result := (← dataProjectionCache.get).find? cls then
      return result
    else
    let result ← getAbstractDataProjections cls
    dataProjectionCache.modify (·.insert cls result)
    return result
  else
    getAbstractDataProjections cls

/-- Find classes for which multiple different instances can be synthesized in the local context. -/
partial def findOverlappingDataInstances : MetaM (Std.HashMap Expr (Array FVarId)) := do
  let mut overlaps : Std.HashMap Expr (Array FVarId) := {}
  let mut encountered : Std.HashMap Expr FVarId := {}
  for decl in ← getLCtx do
    if decl.binderInfo.isInstImplicit then
      let type ← instantiateMVars decl.type
      let projClasses ← forallTelescopeReducing (whnfType := true) type fun xs type ↦ do
        type.withApp fun f args ↦ do
        let .const cls us := f |
          return #[] -- This can happen when using `set_option checkBinderAnnotations false`
        let info ← getConstInfo cls
        let projs ← getAbstractDataProjectionsCached cls
        projs.mapM fun proj ↦
          mkForallFVars xs <|
            (proj.instantiateLevelParams info.levelParams us).instantiateRev args
      for projCls in projClasses do
        if let some fvarId' := encountered[projCls]? then
          overlaps := overlaps.alter projCls (·.getD #[fvarId'] |>.push decl.fvarId)
        else
          encountered := encountered.insert projCls decl.fvarId
  return overlaps

/-- Lints against data-carrying overlaps between instances in the local contexts of declarations. -/
register_option linter.overlappingInstances : Bool := {
  defValue := true
  descr := "enable the overlapping instances linter."
}

/-- Report a warning message if there are any overlapping instances in the local context. -/
def runLinter (ctx : ContextInfo) (lctx : LocalContext) (expectedType? : Option Expr) :
    IO (Option MessageData) := do
  ctx.runMetaM lctx do
  -- Add the hypotheses of the expected type to the local context, as it may have more instances.
  expectedType?.elim id (forallTelescope · fun _ _ => ·) do
  let overlaps ← findOverlappingDataInstances
  if overlaps.isEmpty then
    return none
  let sortedOverlaps : Std.HashMap (Array FVarId) (Array Expr) :=
    overlaps.fold (init := {}) fun s overlap fvars ↦ s.alter fvars (·.getD #[] |>.push overlap)
  -- Sort the suggestions in a (somewhat) deterministic way.
  let sortedOverlaps := sortedOverlaps.toArray.qsort (Array.lex ·.2 ·.2 Expr.lt)
  let mut msgs := #[]
  for (fvars, overlaps) in sortedOverlaps do
    let parents ← fvars.mapM (do instantiateMVars <| ← ·.getType)
    if parents.all (· == parents[0]!) then
      msgs := msgs.push <| m!"There are {parents.size} `{.sbracket parents[0]!}` instances"
    else
      let parents := parents.map (m!"`{.sbracket ·}`")
      let children := overlaps.map fun overlap => m!"`{overlap}`"
      msgs := msgs.push <|
        m!"{.andList parents.toList} give conflicting instances of {.andList children.toList}."
  -- Create a bulleted list if there are multiple messages, otherwise just a single line
  let declDescr ←
    if let some decl := ctx.parentDecl? then
      -- It is slightly awkward to print `decl` because it is not in the current environment.
      pure m!"Declaration `{← unresolveNameGlobal decl}`"
    else
      pure "The current declaration"
  let mut msg := m!"{declDescr} has overlapping instances:"
  msg := if h : msgs.size = 1 then m!"{msg}\n\n{msgs[0]}" else
    msgs.foldl (init := msg ++ "\n") (m!"{·}\n• {·}")
  msg := msg ++ m!"\n\nConsider choosing different instance hypotheses."
  msg ← addMessageContextFull msg
  return some msg

initialize registerTraceClass `overlappingInstances

open Linter in
/--
Lints against data-carrying overlaps between instances in the local contexts of declarations.
-/
def overlappingInstances : Linter where
  run := UnusedInstancesInType.withSetBoolOptionIn fun cmd => do
    unless getLinterValue linter.overlappingInstances (← getLinterOptions) do
      return
    -- Note: we don't break on errors; we want to lint even on partial declarations
    withTraceNode `overlappingInstances (fun _ ↦ return "looking for a local context") do
    for t in ← getInfoTrees do
      for (ref, ctx, info) in t.getDeclBodyInfos do
        let some (lctx, expectedType?) := info.getLCtx? | pure ()
        withTraceNode `overlappingInstances (fun _ ↦ return m!"linting `{ctx.parentDecl?}`") do
        let some msg ← runLinter ctx lctx expectedType? | pure ()
        logLint linter.overlappingInstances ref msg

initialize addLinter overlappingInstances

end Mathlib.Linter.OverlappingInstances
