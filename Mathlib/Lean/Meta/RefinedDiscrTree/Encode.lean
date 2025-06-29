/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Lean.Meta.RefinedDiscrTree.Basic
import Lean.Meta.DiscrTree

/-!
# Encoding an `Expr` as a sequence of `Key`s

We compute the encoding of an expression in a lazy way.
This means computing only one `Key` at a time
and storing the state of the remaining computation in a `LazyEntry`.

Each step is computed by
`evalLazyEntryWithEta : LazyEntry → MetaM (Option (List (Key × LazyEntry)))`.
It returns `none` when the last `Key` has already been reached.

The first step, which is used when initializing the tree,
is computed by `initializeLazyEntryWithEta`.

To compute all the keys at once, we have
* `encodeExprWithEta`, which computes all possible key sequences.
* `encodeExpr`, which computes the canonical key sequence.
  This will be used for expressions that are looked up in a `RefinedDiscrTree` using `getMatch`.

-/

namespace Lean.Meta.RefinedDiscrTree

/-- The context for the `LazyM` monad -/
private structure Context where
  /-- Variables that come from a lambda or forall binder.
  The list index gives the De Bruijn index. -/
  bvars : List FVarId

/-- The monad used for evaluating a `LazyEntry`. -/
private abbrev LazyM := ReaderT Context <| StateT LazyEntry MetaM

private def mkLabelledStar (mvarId : MVarId) : LazyM Key :=
  modifyGet fun entry =>
    if let some stars := entry.labelledStars? then
      match stars.idxOf? mvarId with
      | some idx => (.labelledStar idx, entry)
      | none => (.labelledStar stars.size, { entry with labelledStars? := stars.push mvarId })
    else
      (.star, entry)

/--
Sometimes, we need to not index lambda binders, in particular when the body is the application of
a metavariable.

In the case where we do index the lambda binders,
`withLams` efficiently adds the lambdas and `key` to the result.
-/
@[inline]
private def withLams (lambdas : List FVarId) (key : Key) : StateT LazyEntry MetaM Key := do
  match lambdas with
  | [] => return key
  | _ :: tail =>
    -- Add `key` and `lambdas.length - 1` lambdas to the result, returning the final lambda.
    modify ({ · with computedKeys := tail.foldl (init := [key]) (fun _ => .lam :: ·) })
    return .lam

open private Lean.Meta.DiscrTree.pushArgs in Lean.Meta.DiscrTree.mkPathAux in
open private toNatLit? in Lean.Meta.DiscrTree.pushArgs in

@[inline]
private def encodingStepAux (e : Expr) (lambdas : List FVarId) (root : Bool) : LazyM Key := do
  withLams lambdas (← go)
where
  go := do
  /-
  If entries need to be added to the stack, we don't do that now, because of the lazy design.
  Instead, we set `previous` to be `e`, and later,
  `processPrevious` adds the required entries to the stack.
  -/
  let setEAsPrevious : LazyM Unit := do
    let info ← mkExprInfo e (lambdas ++ (← read).bvars)
    modify fun s => { s with previous := some info }

  match e.getAppFn with
  | .const n _ =>
    unless root do
      if let some v := toNatLit? e then
        return .lit v
    if e.getAppNumArgs != 0 then
      setEAsPrevious
    return .const n e.getAppNumArgs
  | .proj n i _ =>
    setEAsPrevious
    return .proj n i e.getAppNumArgs
  | .fvar fvarId =>
    let bvars := lambdas ++ (← read).bvars
    if e.getAppNumArgs != 0 then
      setEAsPrevious
    if let some idx := bvars.idxOf? fvarId then
      return .bvar idx e.getAppNumArgs
    else
      return .fvar fvarId e.getAppNumArgs
  | .mvar mvarId =>
    if e.isApp then
      /-
      If `e.isApp`, we don't index `lambdas`,
      since for example `fun x => ?m x x` may be any function.
      -/
      return .star
    else
      /-
      If `e` is `.mvar mvarId`, we do index `lambdas`, since it is a constant function.
      We create a `.labelledStar` key that is identified by `mvarId`,
      so that multiple appearances of `.mvar mvarId` are indexed the same.
      -/
      mkLabelledStar mvarId
  | .forallE .. =>
    setEAsPrevious
    return .forall
  | .lit v      => return .lit v
  | .sort _     => return .sort
  | .letE ..    => return .opaque
  | .lam ..     => return .opaque
  | _           => unreachable!

/-- Run `k` on all pairs of body, bound variables that could possibly appear due to η-reduction -/
private def etaPossibilities (e : Expr) (lambdas : List FVarId) (root : Bool)
    (entry : LazyEntry) : ReaderT Context MetaM (List (Key × LazyEntry)) := do
  return (← (encodingStepAux e lambdas root).run (← read) |>.run entry) ::
      (← match e, lambdas with
      | .app f a, fvarId :: lambdas =>
        if isStarWithArg (.fvar fvarId) a && !f.getAppFn.isMVar then
          etaPossibilities f lambdas root entry
        else
          return []
      | _, _ => return [])
where
  /-- Check whether the expression is represented by `Key.star` and has `arg` as an argument. -/
  isStarWithArg (arg : Expr) : Expr → Bool
    | .app f a => if a == arg then f.getAppFn.isMVar else isStarWithArg arg f
    | _ => false

/-- Repeatedly reduce while stripping lambda binders and introducing their variables -/
@[specialize]
private partial def lambdaTelescopeReduce {m} {α} [Nonempty (m α)] [Monad m] [MonadLiftT MetaM m]
    [MonadControlT MetaM m] (e : Expr) (lambdas : List FVarId) (noIndex : List FVarId → m α)
    (k : Expr → List FVarId → m α) : m α := do
  /- expressions marked with `no_index` should be indexed with a star -/
  if DiscrTree.hasNoindexAnnotation e then
    noIndex lambdas
  else
    match ← DiscrTree.reduce e with
    | .lam n d b bi =>
      withLocalDecl n bi d fun fvar =>
        lambdaTelescopeReduce (b.instantiate1 fvar) (fvar.fvarId! :: lambdas) noIndex k
    | e => k e lambdas

/-- A single step in encoding an `Expr` into `Key`s. -/
private def encodingStepWithEta (e : Expr) (root : Bool)
    (entry : LazyEntry) : ReaderT Context MetaM (List (Key × LazyEntry)) :=
  lambdaTelescopeReduce e []
    (fun lambdas => return [← (withLams lambdas .star).run entry])
    (fun e lambdas => etaPossibilities e lambdas root entry)

/-- A single step in encoding an `Expr` into `Key`s. -/
private def encodingStep (e : Expr) (root : Bool) : LazyM Key := do
  lambdaTelescopeReduce e []
    (fun lambdas => withLams lambdas .star)
    (fun e lambdas => encodingStepAux e lambdas root)

/-- Encode `e` as a sequence of keys, computing only the first `Key`. -/
@[inline] def initializeLazyEntryWithEtaAux (e : Expr) (labelledStars : Bool) :
    MetaM (List (Key × LazyEntry)) := do
  (encodingStepWithEta e true (← mkInitLazyEntry labelledStars)).run { bvars := [] }


/-- Encode `e` as a sequence of keys, computing only the first `Key`. -/
def initializeLazyEntryWithEta (e : Expr) (labelledStars : Bool := true) :
    MetaM (List (Key × LazyEntry)) := do
  withReducible do initializeLazyEntryWithEtaAux e labelledStars

/-- Encode `e` as a sequence of keys, computing only the first `Key`. -/
private def initializeLazyEntry (e : Expr) (labelledStars : Bool) : MetaM (Key × LazyEntry) := do
  ((encodingStep e true).run { bvars := [] }).run (← mkInitLazyEntry labelledStars)


/-- Auxiliary function for `evalLazyEntry` -/
private partial def evalLazyEntryAux (entry : LazyEntry) (eta : Bool) :
    MetaM (Option (List (Key × LazyEntry))) := do
  match entry.stack with
  | [] => return none
  | stackEntry :: stack =>
    let entry := { entry with stack }
    match stackEntry with
    | .star =>
      return some [(.star, entry)]
    | .expr { expr, bvars, lctx, localInsts, cfg, transparency } =>
      withLCtx lctx localInsts do
      withConfig (fun _ => cfg) do withTransparency transparency do
        if eta then
          return some (← encodingStepWithEta expr false entry |>.run { bvars := bvars })
        else
          return some [← encodingStep expr false |>.run { bvars := bvars } |>.run entry]

/-- Determine for each argument whether it should be ignored,
and return a list consisting of one `StackEntry` for each argument. -/
private partial def getStackEntries (fn : Expr) (args : Array Expr) (bvars : List FVarId) :
    MetaM (List StackEntry) := do
  let mut fnType ← inferType fn
  loop fnType 0 0 []
where
  /-- The main loop of `getStackEntries` -/
  loop (fnType : Expr) (i j : Nat) (entries : List StackEntry) : MetaM (List StackEntry) := do
    if h : i < args.size then
      let arg := args[i]
      let cont j d b bi := do
        if ← isIgnoredArg arg d bi then
          loop b (i+1) j (.star :: entries)
        else
          -- Recall that `isDefEq` switches the transparency on implicit arguments.
          let info ← (if bi.isExplicit then id else withInferTypeConfig) do mkExprInfo arg bvars
          loop b (i+1) j (.expr info :: entries)
      let rec reduce := do
        match ← whnfD (fnType.instantiateRevRange j i args) with
        | .forallE _ d b bi => cont i d b bi
        | fnType => throwFunctionExpected fnType
      match fnType with
      | .forallE _ d b bi => cont j d b bi
      | _ => reduce
    else
      return entries
  /-- Determine whether the argument should be ignored. -/
  isIgnoredArg (arg domain : Expr) (binderInfo : BinderInfo) : MetaM Bool := do
    if domain.isOutParam then
      return true
    else match binderInfo with
    | .instImplicit => return true
    | .implicit
    | .strictImplicit => return !(← isType arg)
    | .default => isProof arg

/--
If `entry.previous.isSome`, then replace it with `none`, and add the required entries
to entry.stack`.
-/
private def processPrevious (entry : LazyEntry) : MetaM LazyEntry := do
  let some { expr, bvars, lctx, localInsts, cfg, transparency } := entry.previous | return entry
  let entry := { entry with previous := none }
  withLCtx lctx localInsts do withConfig (fun _ => cfg) do withTransparency transparency do
  expr.withApp fun fn args => do

    let stackArgs (entry : LazyEntry) : MetaM LazyEntry := do
      let entries ← getStackEntries fn args bvars
      return { entry with stack := entries.reverseAux entry.stack }

    match fn with
    | .forallE n d b bi =>
      let d' := .expr (← mkExprInfo d bvars)
      let b' ← withLocalDecl n bi d fun fvar =>
        return .expr (← mkExprInfo (b.instantiate1 fvar) (fvar.fvarId! :: bvars))
      return { entry with stack := d' :: b' :: entry.stack }
    | .proj n _ a =>
      let entry ← stackArgs entry
      if isClass (← getEnv) n then
        return { entry with stack := .star :: entry.stack }
      else
        return { entry with stack := .expr (← mkExprInfo a bvars) :: entry.stack }
    | _ => stackArgs entry

/-- A single step in evaluating a `LazyEntry`. Allow multiple different outcomes. -/
def evalLazyEntry (entry : LazyEntry) (eta : Bool) :
    MetaM (Option (List (Key × LazyEntry))) := do
  if let key :: computedKeys := entry.computedKeys then
    -- If there is already a result available, use it.
    return some [(key, { entry with computedKeys })]
  else withMCtx entry.mctx do
    let entry ← processPrevious entry
    evalLazyEntryAux entry eta

/-- Return all encodings of `e` as a `Array Key`. This is used for testing. -/
partial def encodeExprWithEta (e : Expr) (labelledStars : Bool) : MetaM (Array (Array Key)) :=
  withReducible do
    let entries ← (encodingStepWithEta e true (← mkInitLazyEntry labelledStars)).run { bvars := [] }
    let entries := entries.map fun (key, entry) => (#[key], entry)
    go entries.toArray #[]
where
  /-- The main loop for `encodeExpr`. -/
  go (todo : Array (Array Key × LazyEntry)) (result : Array (Array Key)) :
      MetaM (Array (Array Key)) := do
    if h : todo.size = 0 then
      return result
    else -- use an if-then-else instead of if-then-return, so that `go` is tail recursive
      let (keys, entry) := todo.back
      let todo := todo.pop
      match ← evalLazyEntry entry true with
      | some xs =>
        let rec /--
          This variation on `List.fold` ensures that the array `keys`
          isn't copied unnecessarily. -/
        fold xs todo :=
          match xs with
          | [] => todo
          | (key, entry) :: [] => todo.push (keys.push key, entry)
          | (key, entry) :: xs => fold xs (todo.push (keys.push key, entry))
        go (fold xs todo) result
      | none =>
        go todo (result.push keys)

/-- Completely evaluate a `LazyEntry`. -/
partial def LazyEntry.toList (entry : LazyEntry) (result : List Key := []) : MetaM (List Key) := do
  match ← evalLazyEntry entry false with
  | some [(key, entry')] => entry'.toList (key :: result)
  | some _ => panic! "`evalLazyEntry` with `eta := false` can only give a singleton list"
  | none => return result.reverse

/-- Return the canonical encoding of `e` as a `Array Key`.
This is used for looking up `e` in a `RefinedDiscrTree`. -/
def encodeExpr (e : Expr) (labelledStars : Bool) : MetaM (Key × List Key) := withReducible do
  let (key, entry) ← initializeLazyEntry e labelledStars
  return (key, ← entry.toList)

end Lean.Meta.RefinedDiscrTree
