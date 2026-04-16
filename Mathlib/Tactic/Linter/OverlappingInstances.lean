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
as an "instance diamond". This linter warns against declarations whose local contexts include
multiple versions of the same data.

This is a hybrid syntax and environment linter.For performance reasons, the syntax linter **only**
runs interactively in the language server. It will not run on the command line during a typical
`lake build`. The syntax linter also only lints the bodies of declarations that appear in source,
and does not currently handle declarations that do not have a "body" such as `structure`s. (The
environment linter does handle these cases.)

Note that since all proofs of a given proposition are definitionally equal, multiple different ways
of obtaining instances of `Prop` classes pose no issue. Hence, this linter only warns against
data-carrying instance projections.

Note that since this linter also warns against the trivial case of the same data-carrying instance
appearing twice, it warns against explicit local instance hypotheses which shadow `variable`s.
These may not influence the resulting type of the declaration, since Lean ignores unused instances,
but they are still duplicated in the local context while editing the body.

## TODO

- Improve performance. Currently running this linter in CI is prohibitively expensive.
- Expand to declarations without bodies (`structure`s/`class`es/`inductive`s etc.)
- The logging location for this linter could be improved.
- Currently it is possible to obtain a message which includes something of the following form:
  ```
  • There are 2 instances of `[NonUnitalSemiring R]`.
  • `[InvolutiveStar R]` is provided by both `[StarRing R]` and `[StarRing R]`.
  ```
  This occurs because each of the two `StarRing`s relies on one of the two different
  `NonUnitalSemiring` instances in the context, making them distinct (despite pretty-printing the
  same way). However, their projection to `InvolutiveStar` no longer depends on this instance, and
  thus coincides. The messages in this scenario could be improved.
- We could add hovers on the declaration name in messages. This is made tricky by the fact that it
  conflicts with the auxdecl of the same name.

-/

open Lean Meta Elab Command

meta section

namespace Mathlib.Linter.OverlappingInstances

/-- Clear the instances from the given application. -/
def eraseInstances (e : Expr) : MetaM Expr := do
  e.withApp fun f args ↦ do
  let finfo ← getFunInfo f
  let mut args := args
  for param in finfo.paramInfo, i in *...args.size do
    if param.binderInfo.isInstImplicit then
      args := args.set! i default
  return mkAppN f args

/-- Compute the data projections of the class `cls`.
If `cls` is a `Prop` or a non-structure class, then return singleton array with just `cls`.
The results contain bound variables corresponding to the parameters of `cls`. -/
partial def abstractDataProjections (cls : Name) : CoreM (Array Expr) := do
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

initialize dataProjectionCache : EnvExtension (NameMap (Array Expr)) ←
  registerEnvExtension (pure {})

def abstractDataProjectionsCached (cls : Name) : CoreM (Array Expr) := do
  if let some result := (dataProjectionCache.getState (← getEnv)).find? cls then
    return result
  let result ← abstractDataProjections cls
  modifyEnv (dataProjectionCache.modifyState · (·.insert cls result))
  return result

/--
Find classes that for which multiple different instances can be synthesized in the local context.
-/
partial def findOverlappingDataInstances : MetaM (Std.HashMap Expr (Array FVarId)) := do
  let mut overlaps : Std.HashMap Expr (Array FVarId) := {}
  let mut encountered : Std.HashMap Expr FVarId := {}
  for decl in ← getLCtx do
    if decl.binderInfo.isInstImplicit then
      let type ← instantiateMVars decl.type
      let projClasses ← forallTelescopeReducing (whnfType := true) type fun xs type ↦ do
        type.withApp fun f args ↦ do
        let .const cls us := f |
          throwError "`{decl.toExpr}` has an instance implicit binder, but it is not an instance"
        let info ← getConstInfo cls
        let projs ← abstractDataProjectionsCached cls
        projs.mapM fun proj ↦
          mkForallFVars xs <|
            (proj.instantiateLevelParams info.levelParams us).instantiate args
      for cls in projClasses do
        if let some fvarId' := encountered[cls]? then
          overlaps := overlaps.alter cls (·.getD #[fvarId'] |>.push decl.fvarId)
        else
          encountered := encountered.insert cls decl.fvarId
  return overlaps

/-- Lints against data-carrying overlaps between instances in the local contexts of declarations. -/
register_option linter.overlappingInstances : Bool := {
  defValue := true
  descr := "enable the overlapping instances linter."
}

/-- Creates a message describing the violations captured in `Overlaps`, assumed to be nonempty. -/
def overlapsToMsg (overlaps : Std.HashMap Expr (Array FVarId)) (ctx : ContextInfo) :
    MetaM MessageData := do
  let declDescr ←
    if let some decl := ctx.parentDecl? then
      pure m!"declaration `{.ofConstName (← unresolveNameGlobal decl)}`"
    else
      pure "current declaration"
  let mut msg := m!"The {declDescr} \
    has instance hypotheses which provide conflicting versions of the same data. Specifically:"
  let mut msgs := #[]
  for (overlap, fvars) in overlaps do
    let parents ← fvars.mapM fun fvarId ↦ return m!"`{.sbracket (← fvarId.getType)}`"
    -- let overlap := MessageData.ofInstanceBinderType overlap
    msgs := msgs.push <|
      m!"{.andList parents.toList} provide conflicting instances of `{overlap}`."
  -- Create a bulleted list if there are multiple messages, otherwise just a single line
  msg := if h : msgs.size = 1 then msg ++ "\n\n" ++ msgs[0] else
    msgs.foldl (init := msg ++ "\n") (m!"{·}\n• {·}")
  msg := msg ++ m!"\n\n\
    There should only be a single instance of these data-carrying typeclasses in the local context \
    at a time. Consider choosing different instance hypotheses for the {declDescr}."
  addMessageContextFull msg

open Linter in
/--
Lints against data-carrying overlaps between instances in the local contexts of declarations.
-/
def overlappingInstances : Linter where
  run :=
    UnusedInstancesInType.withSetBoolOptionIn fun cmd => do
    unless getLinterValue linter.overlappingInstances (← getLinterOptions) do
      return
    -- Note: we don't break on errors; we want to lint even on partial declarations
    for t in ← getInfoTrees do
      for (ref, ctx, info) in t.getDeclBodyInfos do
        let some (lctx, remainingType?) := info.getLCtx? | continue
        ctx.runMetaMWithMessages lctx do withRef ref do
        remainingType?.elim id (forallTelescope · fun _ _ => ·) do
          let overlaps ← findOverlappingDataInstances
          unless overlaps.isEmpty do
            logWarning (← overlapsToMsg overlaps ctx)

initialize addLinter overlappingInstances

end Mathlib.Linter.OverlappingInstances
