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

Each step is computed by `evalLazyEntry : LazyEntry → MetaM (Option (List (Key × LazyEntry)))`.
It returns `none` when the last `Key` has already been reached.

The first step, which is used when initializing the tree, is computed by `initializeLazyEntry`.

To compute all the keys at once, we have
* `encodeExpr`, which computes all possible key sequences.
* `encodeExpr'`, which computes the canonical key sequence.
  This will be used for expressions that are looked up in a `RefinedDiscrTree` using `getMatch`.

-/

namespace Lean.Meta.RefinedDiscrTree

/-- This is a copy of the same private function defined for `DiscrTree`.

Return `true` if `e` is one of the following
- A nat literal (numeral)
- `Nat.zero`
- `Nat.succ x` where `isNumeral x`
- `OfNat.ofNat _ x _` where `isNumeral x` -/
private partial def isNumeral (e : Expr) : Bool :=
  if e.isRawNatLit then true
  else
    let f := e.getAppFn
    if !f.isConst then false
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then isNumeral e.appArg!
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then isNumeral (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then true
      else false

/-- This is a copy of the same private function defined for `DiscrTree`.

Return `some n` if `e` is definitionally equal to the natural number `n`. -/
private partial def toNatLit? (e : Expr) : Option Literal :=
  if isNumeral e then
    if let some n := loop e then
      some (.natVal n)
    else
      none
  else
    none
where
  loop (e : Expr) : Option Nat := do
    let f := e.getAppFn
    match f with
    | .lit (.natVal n) => return n
    | .const fName .. =>
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then
        let r ← loop e.appArg!
        return r+1
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then
        loop (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then
        return 0
      else
        failure
    | _ => failure

/-- The context for the `LazyM` monad-/
private structure Context where
  /-- Variables that come from a lambda or forall binder.
  The list index gives the De Bruijn index. -/
  bvars : List FVarId

/-- The monad used for evaluating a `LazyEntry`. -/
private abbrev LazyM := ReaderT Context <| StateT LazyEntry MetaM

variable {α : Type}

private def LazyM.run (k : LazyM α) (context : Context) (entry : LazyEntry) :
    MetaM (α × LazyEntry) :=
  k.run context |>.run entry

private def mkStar (mvarId : MVarId) : LazyM Key :=
  modifyGet fun entry =>
    match entry.stars.find? mvarId with
    | some idx => (.star idx, entry)
    | none => (.star entry.nStars,
      { entry with stars := entry.stars.insert mvarId entry.nStars, nStars := entry.nStars + 1 })

private def mkNewStar : StateT LazyEntry MetaM Key :=
  modifyGet fun entry => (.star entry.nStars, { entry with nStars := entry.nStars + 1 })

@[inline] private def withLams (lambdas : List FVarId) (key : Key) : StateT LazyEntry MetaM Key :=
  do match lambdas with
  | [] => return key
  | _ :: tail =>
    modify ({ · with results := tail.foldl (init := [key]) fun keys _ => .lam :: keys })
    return .lam

private def encodingStepAux (e : Expr) (lambdas : List FVarId) (root : Bool) : LazyM Key := do
  let setEAsPrevious : LazyM Unit := do
    let info := {
      expr       := e
      bvars      := lambdas ++ (← read).bvars
      lctx       := ← getLCtx
      localInsts := ← getLocalInstances }
    modify fun s => { s with previous := some info }

  match e.getAppFn with
  | .const n _ =>
    unless root do
      /- since `(fun _ => 0) = 0` and `(fun _ => 1) = 1`,
      we don't index lambdas before literals -/
      if let some v := toNatLit? e then
        return ← withLams lambdas <| .lit v
    unless e.getAppNumArgs == 0 do
      setEAsPrevious
    withLams lambdas <| .const n e.getAppNumArgs
  | .proj n i _ =>
    setEAsPrevious
    withLams lambdas <| .proj n i e.getAppNumArgs
  | .fvar fvarId =>
    /- we index `fun x => x` as `id` when not at the root -/
    if !root && e.getAppNumArgs == 0 then
      if let fvarId' :: lambdas := lambdas then
        if fvarId' == fvarId then
          let info := {
            expr       := ← fvarId.getType
            bvars      := lambdas ++ (← read).bvars
            lctx       := ← getLCtx
            localInsts := ← getLocalInstances }
          modify fun s => { s with stack := .expr info :: s.stack }
          return ← withLams lambdas <| .const ``id 1
    let bvars := lambdas ++ (← read).bvars
    unless e.getAppNumArgs == 0 do
      setEAsPrevious
    if let some idx := bvars.idxOf? fvarId then
      withLams lambdas <| .bvar idx e.getAppNumArgs
    else
      withLams lambdas <| .fvar fvarId e.getAppNumArgs
  | .mvar mvarId =>
    if root then
      if e.isApp then
        -- if there are arguemnts, we don't index the lambdas:
        -- because, for example `fun x => ?m x x` may be any function
        return .star 0
      else
        -- by indexing the lambdas, we only allow matches with constant functions
        withLams lambdas <| .star 0
    -- even if there are no arguments, we don't index the lambdas:
    -- because, it should be able to match with
    -- `fun _ => x + y`, which is indexed as `(fun _ => x) + (fun _ => y)`.
    else if lambdas.isEmpty then
      mkStar mvarId
    else
      mkNewStar

  | .forallE .. =>
    setEAsPrevious
    withLams lambdas .forall
  | .lit v      => withLams lambdas <| .lit v
  | .sort _     => withLams lambdas <| .sort
  | .letE ..    => withLams lambdas <| .opaque
  | .lam ..     => withLams lambdas <| .opaque
  | _           => unreachable!

/-- Check whether the expression is represented by `Key.star` and has `arg` as an argument. -/
private def isStarWithArg (arg : Expr) : Expr → Bool
  | .app f a => if a == arg then f.getAppFn.isMVar else isStarWithArg arg f
  | _ => false

/-- Run `k` on all pairs of body, bound variables that could possibly appear due to η-reduction -/
private def etaPossibilities (e : Expr) (lambdas : List FVarId) (root : Bool) (entry : LazyEntry) :
    ReaderT Context MetaM (List (Key × LazyEntry)) :=
  return (← (encodingStepAux e lambdas root).run (← read) entry) :: (← match e, lambdas with
  | .app f a, fvarId :: lambdas =>
    if isStarWithArg (.fvar fvarId) a && !f.getAppFn.isMVar then
      etaPossibilities f lambdas root entry
    else
      return []
  | _, _ => return [])

/-- run `etaPossibilities`, and cache the result if there are multiple possibilities. -/
private def cacheEtaPossibilities (e original : Expr) (lambdas : List FVarId) (root : Bool)
    (entry : LazyEntry) : ReaderT Context MetaM (List (Key × LazyEntry)) := do
  match e, lambdas with
  | .app f a, fvarId :: _ =>
    if isStarWithArg (.fvar fvarId) a && !f.getAppFn.isMVar then
      match entry.cache.find? original with
      | some (key :: keys) => return [(key, { entry with results := keys })]
      | some [] => unreachable!
      | none =>
        let entry := { entry with stack := .cache original [] :: entry.stack }
        etaPossibilities e lambdas root entry
    else
      return [← (encodingStepAux e lambdas root).run (← read) entry]
  | _, _ => return [← (encodingStepAux e lambdas root).run (← read) entry]

/-- Repeatedly reduce while stripping lambda binders and introducing their variables -/
@[specialize]
private partial def lambdaTelescopeReduce {m} [Nonempty (m α)] [Monad m] [MonadLiftT MetaM m]
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

private def useReducePi (name : Name) : Array (Option Expr) × List FVarId → LazyM Key
| (args, lambdas) => do
  let bvars := lambdas ++ (← read).bvars
  let lctx ← getLCtx
  let localInsts ← getLocalInstances
  let stack := args.foldr (init := (← get).stack) fun arg stack =>
    match arg with
    | none     => .star :: stack
    | some arg => .expr { expr := arg, bvars, lctx, localInsts } :: stack
  modify ({ · with stack })
  withLams lambdas <| .const name args.size

/-- A single step in encoding an `Expr` into `Key`s. -/
private def encodingStep (original : Expr) (root : Bool)
    (entry : LazyEntry) : ReaderT Context MetaM (List (Key × LazyEntry)) :=
  lambdaTelescopeReduce original []
    (fun lambdas =>
      return [← (do withLams lambdas (← mkNewStar)).run entry])
    (fun e lambdas => cacheEtaPossibilities e original lambdas root entry)

/-- A single step in encoding an `Expr` into `Key`s. -/
private def encodingStep' (original : Expr) (root : Bool) : LazyM Key := do
  lambdaTelescopeReduce original []
    (fun lambdas => do withLams lambdas (← mkNewStar))
    (fun e lambdas => encodingStepAux e lambdas root)

/-- Encode `e` as a sequence of keys, computing only the first `Key`. -/
@[inline] def initializeLazyEntryAux (e : Expr) : MetaM (List (Key × LazyEntry)) := do
  encodingStep e true { mctx := ← getMCtx } |>.run { bvars := [] }


/-- Encode `e` as a sequence of keys, computing only the first `Key`. -/
def initializeLazyEntry (e : Expr) : MetaM (List (Key × LazyEntry)) := do
  withReducible do initializeLazyEntryAux e

/-- Encode `e` as a sequence of keys, computing only the first `Key`. -/
private def initializeLazyEntry' (e : Expr) : MetaM (Key × LazyEntry) := do
  encodingStep' e true |>.run { bvars := [] } { mctx := ← getMCtx }


/-- If there is a loose `.bvar` returns `none`. Otherwise returns the index
of the next branch of the expression. -/
private partial def hasLooseBVarsAux (depth : Nat) (keys : List Key) : Option (List Key) :=
  match keys with
  | [] => none
  | key :: keys =>  match key with
    | .const _ nargs
    | .fvar _ nargs   => recurse nargs keys
    | .bvar i nargs   => if i ≥ depth then none else recurse nargs keys
    | .lam            => hasLooseBVarsAux (depth + 1) keys
    | .forall         => hasLooseBVarsAux depth keys >>= hasLooseBVarsAux (depth + 1)
    | .proj _ _ nargs => recurse (nargs + 1) keys
    | _               => some keys
where
  recurse (nargs : Nat) (keys : List Key) : Option (List Key) :=
    nargs.foldRevM (init := keys) fun _ _ => hasLooseBVarsAux depth

/-- Determine whether `keys` contains a loose bound variable. -/
private def hasLooseBVars (keys : List Key) : Bool :=
  hasLooseBVarsAux 0 keys |>.isNone

private partial def processLazyEntryAux (entry : LazyEntry) :
    MetaM (Option (List (Key × LazyEntry))) := do
  match entry.stack with
  | [] => return none
  | stackEntry :: stack =>
    let entry := { entry with stack }
    match stackEntry with
    | .cache key valueRev =>
      let value := valueRev.reverse
      let entry := if hasLooseBVars value then entry else
        { entry with cache := entry.cache.insert key value }
      processLazyEntryAux entry
    | .star =>
      return some [← mkNewStar.run entry]
    | .expr info =>
      withLCtx info.lctx info.localInsts do
      return some (← encodingStep info.expr false entry |>.run { bvars := info.bvars })

private partial def processLazyEntryAux' (entry : LazyEntry) :
    MetaM (Option (Key × LazyEntry)) := do
  match entry.stack with
  | [] => return none
  | stackEntry :: stack =>
    let entry := { entry with stack }
    match stackEntry with
    | .cache key valueRev =>
      let value := valueRev.reverse
      let entry := if hasLooseBVars value then entry else
        { entry with cache := entry.cache.insert key value }
      processLazyEntryAux' entry
    | .star =>
      return some (← mkNewStar.run entry)
    | .expr info =>
      withLCtx info.lctx info.localInsts do
      return some (← encodingStep' info.expr false |>.run { bvars := info.bvars } entry)

/-- Determine for each argument whether it should be ignored,
and return a list consisting of one `StackEntry` for each argument. -/
private partial def getEntries (fn : Expr) (args : Array Expr) (bvars : List FVarId)
    (lctx : LocalContext) (localInsts : LocalInstances) : MetaM (List StackEntry) := do
  let mut fnType ← inferType fn
  loop fnType 0 0 []
where
  /-- The main loop of `getEntries` -/
  loop (fnType : Expr) (i j : Nat) (entries : List StackEntry) : MetaM (List StackEntry) := do
    if h : i < args.size then
      let arg := args[i]
      let cont j d b bi := do
        if ← isIgnoredArg arg d bi then
          loop b (i+1) j (.star :: entries)
        else
          loop b (i+1) j (( .expr { expr := arg, bvars, lctx, localInsts }) :: entries)
      let rec reduce := do
        match ← whnfD (fnType.instantiateRevRange j i args) with
        | .forallE _ d b bi => cont i d b bi
        | fnType =>
          throwFunctionExpected fnType
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

private def processPrevious (entry : LazyEntry) : MetaM (LazyEntry) := do
  let some { expr, bvars, lctx, localInsts } := entry.previous | return entry
  let entry := { entry with previous := none }
  withLCtx lctx localInsts do
  expr.withApp fun fn args => do

  let stackArgs (entry : LazyEntry) : MetaM (LazyEntry) := do
    let entries ← getEntries fn args bvars lctx localInsts
    return { entry with stack := entries.reverseAux entry.stack }

  match fn with
  | .forallE n d b bi =>
    let d' := .expr { expr := d, bvars, lctx, localInsts }
    let b' ← withLocalDecl n bi d fun fvar =>
      return .expr {
        expr       := b.instantiate1 fvar
        bvars      := fvar.fvarId! :: bvars
        lctx       := ← getLCtx
        localInsts := ← getLocalInstances }
    return { entry with stack := d' :: b' :: entry.stack }
  | .proj n _ a =>
    if isClass (← getEnv) n then
      let entry ← stackArgs entry
      return { entry with stack := .star :: entry.stack}
    else
      let entry ← stackArgs entry
      return { entry with stack := .expr { expr := a, bvars, lctx, localInsts } :: entry.stack}
  | _ => stackArgs entry

private def updateCaches (stack : List StackEntry) (key : Key) : List StackEntry :=
  stack.map fun
    | .cache k value => .cache k (key :: value)
    | x => x

/-- A single step in evaluating a `LazyEntry`. -/
def evalLazyEntry (entry : LazyEntry) :
    MetaM (Option (List (Key × LazyEntry))) := do
  if let key :: results := entry.results then
    return some [(key, { entry with results, stack := updateCaches entry.stack key })]
  else withMCtx entry.mctx do
    let entry ← processPrevious entry
    let result ← processLazyEntryAux entry
    return result.map <| List.map fun (key, entry) =>
          (key, { entry with stack := updateCaches entry.stack key })


/-- A single step in evaluating a `LazyEntry`. -/
private def evalLazyEntry' (entry : LazyEntry) :
    MetaM (Option (Key × LazyEntry)) := do
  if let key :: results := entry.results then
    return some (key, { entry with results, stack := updateCaches entry.stack key })
  else withMCtx entry.mctx do
    let entry ← processPrevious entry
    let result ← processLazyEntryAux' entry
    return result.map fun (key, entry) =>
      (key, { entry with stack := updateCaches entry.stack key })


/-- Return all encodings of `e` as a `Array Key`.
This is used for inserting `e` into a `RefinedDiscrTree`. -/
partial def encodeExpr (e : Expr) : MetaM (Array (Array Key)) :=
  withReducible do
    let entries ← encodingStep e true { mctx := ← getMCtx } |>.run { bvars := [] }
    let entries := entries.map fun (key, entry) => (#[key], entry)
    go entries.toArray #[]
where
  /-- The main loop for `encodeExpr`. -/
  go (todo : Array (Array Key × LazyEntry)) (result : Array (Array Key)) :
      MetaM (Array (Array Key)) := do
    if todo.isEmpty then
      return result
    else
      let (keys, entry) := todo.back!
      let todo := todo.pop
      match ← evalLazyEntry entry with
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
  match ← evalLazyEntry' entry with
  | some (key, entry') => entry'.toList (key :: result)
  | none => return result.reverse

/-- Return the canonical encoding of `e` as a `Array Key`.
This is used for looking up `e` in a `RefinedDiscrTree`. -/
def encodeExpr' (e : Expr) : MetaM (Key × List Key) := withReducible do
  let (key, entry) ← initializeLazyEntry' e
  return (key, ← entry.toList)

end Lean.Meta.RefinedDiscrTree
