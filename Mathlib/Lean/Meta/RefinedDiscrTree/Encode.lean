/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Lean.Meta.RefinedDiscrTree.Basic
import Mathlib.Lean.Meta.RefinedDiscrTree.Pi
import Lean.Meta.DiscrTree

/-!
# Encoding an `Expr` as a sequence of `Key`s

We compute the encoding of and expression in a lazy way.
This means computing only one `Key` at a time,
and storing the state of the remaining computation in a `LazyEntry α`.

Each step is computed by `evalLazyEntry : LazyEntry → MetaM (List (Key × LazyEntry α) ⊕ α)`.

The first step, which is used in initializing the tree, is computed by `initializeLazyEntry`.

To compute all the keys at once, we have
* `encodeExpr`, which computes all possible key sequences
* `encodeExpr'`, which computes the canonical key sequence.
  This is used for expressions that we want to look up in a `RefinedDiscrTree`.

-/

namespace Lean.Meta.RefinedDiscrTree

/-- Return `true` if `e` is one of the following
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

/-- Return `some n` if `e` is definitionally equal to the natural number `n`. -/
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

/-- Check whether the expression is represented by `Key.star`. -/
private def isStar : Expr → Bool
  | .mvar .. => true
  | .app f _ => isStar f
  | _ => false

/-- Check whether the expression is represented by `Key.star` and has `arg` as an argument. -/
private def isStarWithArg (arg : Expr) : Expr → Bool
  | .app f a => if a == arg then isStar f else isStarWithArg arg f
  | _ => false

/-- If there is a loose `.bvar` returns `none`. Otherwise returns the index
of the next branch of the expression. -/
private partial def hasLooseBVarsAux (depth : Nat) (keys : List Key) : Option (List Key) :=
  match keys with
  | [] => none
  | key :: keys =>
  match key with
  | .const _ nargs
  | .fvar _ nargs   => recurse nargs keys
  | .bvar i nargs   => if i ≥ depth then none else recurse nargs keys
  | .lam            => hasLooseBVarsAux (depth + 1) keys
  | .forall         => hasLooseBVarsAux depth keys >>= hasLooseBVarsAux (depth + 1)
  | .proj _ _ nargs => recurse (nargs + 1) keys
  | _               => some keys
where
  recurse (nargs : Nat) (keys : List Key) : Option (List Key) :=
    nargs.foldM (init := keys) (fun _ => hasLooseBVarsAux depth)

/-- Determine whether `keys` contains a loose bound variable. -/
private def hasLooseBVars (keys : List Key) : Bool :=
  hasLooseBVarsAux 0 keys |>.isNone

/-- Reduction procedure for the `RefinedDiscrTree` indexing. -/
private partial def reduce (e : Expr) (config : WhnfCoreConfig) : MetaM Expr := do
  let e ← whnfCore e config
  match (← unfoldDefinition? e) with
  | some e => reduce e config
  | none => match e.etaExpandedStrict? with
    | some e => reduce e config
    | none   => return e



/-- The context for the `LazyM α` monad-/
private structure Context where
  /-- Variables that come from a lambda or forall binder.
  The list index gives the De Bruijn index. -/
  bvars : List FVarId
  /-- The `whnfCore` configuration -/
  config : WhnfCoreConfig


/-- The monad used for evaluating a `LazyEntry α`. -/
private abbrev LazyM (α : Type) := ReaderT Context StateRefT (LazyEntry α) MetaM

variable {α : Type}

private def LazyM.run {β : Type} (k : LazyM α β) (context : Context) (entry : LazyEntry α) :
    MetaM (β × LazyEntry α) :=
  withMCtx entry.mctx do k.run context |>.run entry

private def mkStar (mvarId : MVarId) : LazyM α Key :=
  modifyGet fun entry =>
    match entry.stars.find? mvarId with
    | some idx => (.star idx, entry)
    | none => (.star entry.nStars,
      { entry with stars := entry.stars.insert mvarId entry.nStars, nStars := entry.nStars + 1 })

private def mkNewStar (entry : LazyEntry α) : Key × LazyEntry α :=
  (.star entry.nStars, { entry with nStars := entry.nStars + 1 })

@[inline]
private def withLams (lambdas : List FVarId) (key : Key) : LazyM α Key := do
  match lambdas with
  | [] => return key
  | _ :: tail =>
    modify ({ · with results := tail.foldl (init := [key]) fun keys _ => .lam :: keys })
    return .lam

private def encodingStepAux (e : Expr) (lambdas : List FVarId) (root : Bool) : LazyM α Key := do
  let setEAsPrevious : LazyM α Unit := do
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
        return .lit v
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
    if let some idx := bvars.indexOf? fvarId then
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
      modifyGet mkNewStar

  | .forallE .. =>
    setEAsPrevious
    withLams lambdas .forall
  | .lit v      => withLams lambdas <| .lit v
  | .sort _     => withLams lambdas <| .sort
  | .letE ..    => withLams lambdas <| .opaque
  | .lam ..     => withLams lambdas <| .opaque
  | _           => unreachable!

/-- Run `k` on all pairs of body, bound variables that could possibly appear due to η-reduction -/
@[specialize]
private def etaPossibilities (e : Expr) (lambdas : List FVarId)
    (k : Expr → List FVarId → ReaderT Context MetaM (List α)) : ReaderT Context MetaM (List α) :=
  return (← k e lambdas) ++ (← match e, lambdas with
  | .app f a, fvarId :: lambdas =>
    if isStarWithArg (.fvar fvarId) a && !(f.getAppFn.isMVar || f.containsFVar fvarId) then
      etaPossibilities f lambdas k
    else
      return []
  | _, _ => return [])

/-- run `etaPossibilities`, and cache the result if there are multiple possibilities. -/
@[specialize]
private def cacheEtaPossibilities (e original : Expr) (lambdas : List FVarId)
    (entry : LazyEntry α)
    (ifCached : List Key → (Key × LazyEntry α))
    (k : LazyEntry α → Expr → List FVarId → ReaderT Context MetaM (List (Key × LazyEntry α))) :
    ReaderT Context MetaM (List (Key × LazyEntry α)) := do
  match e, lambdas with
  | .app f a, fvarId :: _ =>
    if isStarWithArg (.fvar fvarId) a && !(f.getAppFn.isMVar || f.containsFVar fvarId) then
      match entry.cache.find? original with
      | some keys => return [ifCached keys]
      | none =>
        let entry := { entry with stack := .cache original [] :: entry.stack }
        etaPossibilities e lambdas (k entry)
    else
      k entry e lambdas
  | _, _ => k entry e lambdas

/-- Repeatedly reduce while stripping lambda binders and introducing their variables -/
@[specialize]
private partial def lambdaTelescopeReduce {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    [Inhabited (m α)] (e : Expr) (lambdas : List FVarId) (config : WhnfCoreConfig)
    (noIndex : List FVarId → m α) (k : Expr → List FVarId → m α) : m α := do
  /- expressions marked with `no_index` are indexed with a star -/
  if DiscrTree.hasNoindexAnnotation e then
    noIndex lambdas
  else
    match ← reduce e config with
    | .lam n d b bi =>
      withLocalDecl n bi d fun fvar =>
        lambdaTelescopeReduce (b.instantiate1 fvar) (fvar.fvarId! :: lambdas) config noIndex k
    | e => k e lambdas

private def useReducePi (name : Name) : Array (Option Expr) × List FVarId → LazyM α Key
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
private def encodingStep (original : Expr) (root : Bool) (entry : LazyEntry α) :
    ReaderT Context MetaM (List (Key × LazyEntry α)) := do
  lambdaTelescopeReduce original [] (← read).config
    (fun lambdas => do
      let (key, entry) := mkNewStar entry
      let (key, entry) ← (withLams lambdas key).run (← read) entry
      pure ([(key, entry)]))
    (fun e lambdas => do
      unless root do
        if let some (n, as) ← reducePi e lambdas then
          return ← as.toList.mapM fun data => do (useReducePi n data).run (← read) entry

      cacheEtaPossibilities e original lambdas entry
        (fun | key :: keys => (key, { entry with results := keys }) | [] => (panic! "", entry))
        (fun entry e lambdas =>
          return [← (encodingStepAux e lambdas root).run (← read) entry]))

/-- A single step in encoding an `Expr` into `Key`s. -/
private def encodingStep' (original : Expr) (root : Bool) :
    LazyM α Key := do
  lambdaTelescopeReduce original [] (← read).config
    (fun lambdas => do withLams lambdas (← modifyGet mkNewStar))
    (fun e lambdas => do
      unless root do
        if let some (n, as) ← reducePi e lambdas then
          return ← useReducePi n as.back
      encodingStepAux e lambdas root)

/-- Encode `e` as a sequence of keys, computing only the first `Key`. -/
def initializeLazyEntry (e : Expr) (val : α) (config : WhnfCoreConfig) :
    MetaM (List (Key × LazyEntry α)) := do
  let mctx ← getMCtx
  encodingStep e true { val, mctx } |>.run { bvars := [], config}

/-- Encode `e` as a sequence of keys, computing only the first `Key`. -/
private def initializeLazyEntry' (e : Expr) (val : α) (config : WhnfCoreConfig) :
    MetaM (Key × LazyEntry α) := do
  let mctx ← getMCtx
  encodingStep' e true |>.run { bvars := [], config} { val, mctx }


private partial def processLazyEntryAux (entry : LazyEntry α) :
    ReaderT WhnfCoreConfig MetaM (List (Key × LazyEntry α) ⊕ α) := do
  match entry.stack with
  | [] => return .inr entry.val
  | stackEntry :: stack =>
    let entry := { entry with stack }
    match stackEntry with
    | .cache key valueRev =>
      let value := valueRev.reverse
      let entry := if hasLooseBVars value then entry else
        { entry with cache := entry.cache.insert key value }
      processLazyEntryAux entry
    | .star =>
      let (key, entry) := mkNewStar entry
      return .inl [(key, entry)]
    | .expr info =>
      withLCtx info.lctx info.localInsts do
      return .inl (
        ← encodingStep info.expr (root := false) entry |>.run { info with config := (← read) })

private partial def processLazyEntryAux' (entry : LazyEntry α) :
    ReaderT WhnfCoreConfig MetaM ((Key × LazyEntry α) ⊕ α) := do
  match entry.stack with
  | [] => return .inr entry.val
  | stackEntry :: stack =>
    let entry := { entry with stack }
    match stackEntry with
    | .cache key valueRev =>
      let value := valueRev.reverse
      let entry := if hasLooseBVars value then
        { entry with cache := entry.cache.insert key value }
        else entry
      processLazyEntryAux' entry
    | .star =>
      let (key, entry) := mkNewStar entry
      return .inl (key, entry)
    | .expr info =>
      withLCtx info.lctx info.localInsts do
      return .inl (← encodingStep' info.expr false |>.run { info with config := (← read)} entry)

private def updateCaches (stack : List StackEntry) (key : Key) : List StackEntry :=
  stack.map fun
    | .cache k value => .cache k (key :: value)
    | x => x


/-- Determine for each argument whether it should be ignored,
and return a list consisting of one `StackEntry` for each argument. -/
private def getEntries (fn : Expr) (args : Array Expr) (bvars : List FVarId) (lctx : LocalContext)
    (localInsts : LocalInstances) : MetaM (List StackEntry) := do
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
      match fnType with
      | .forallE _ d b bi => cont j d b bi
      | fnType =>
        match ← whnfD (fnType.instantiateRevRange j i args) with
        | .forallE _ d b bi => cont i d b bi
        | fnType =>
          throwError m! "expected function type {indentExpr fnType}"
    else
      return entries
  /-- Determine whether the argument should be ignored. -/
  isIgnoredArg (arg domain : Expr) (binderInfo : BinderInfo) : MetaM Bool := do
    if domain.isOutParam then
      return true
    match binderInfo with
    | .instImplicit => return true
    | .implicit
    | .strictImplicit => return !(← isType arg)
    | .default => isProof arg

private def processPrevious (entry : LazyEntry α) : MetaM (LazyEntry α) := do
  let some { expr, bvars, lctx, localInsts } := entry.previous | return entry
  let entry := { entry with previous := none }
  withLCtx lctx localInsts do
  expr.withApp fun fn args => do

  let stackArgs (entry : LazyEntry α) : MetaM (LazyEntry α) := do
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


/-- A single step in evaluating a `LazyEntry α`. -/
def evalLazyEntry (entry : LazyEntry α) (config : WhnfCoreConfig) :
    MetaM (List (Key × LazyEntry α) ⊕ α) := do
  if let key :: results := entry.results then
    return .inl [(key, { entry with results, stack := updateCaches entry.stack key })]
  else withMCtx entry.mctx do
    let entry ← processPrevious entry
    let result ← processLazyEntryAux entry |>.run config
    return match result with
      | .inl entries => .inl <| entries.map fun (key, entry) =>
          (key, { entry with stack := updateCaches entry.stack key })
      | result => result

/-- A single step in evaluating a `LazyEntry α`. -/
private def evalLazyEntry' (entry : LazyEntry α) :
    ReaderT WhnfCoreConfig MetaM ((Key × LazyEntry α) ⊕ α) := do
  if let key :: results := entry.results then
    return .inl (key, { entry with results, stack := updateCaches entry.stack key })
  else withMCtx entry.mctx do
    let entry ← processPrevious entry
    let result ← processLazyEntryAux' entry
    return match result with
      | .inl (key, entry) => .inl (key, { entry with stack := updateCaches entry.stack key })
      | result => result


/-- Return all encodings of `e` as a `Array Key`.
This is used for inserting `e` into a `RefinedDiscrTree`. -/
partial def encodeExpr (e : Expr) (config : WhnfCoreConfig) : MetaM (Array (List Key)) :=
  withReducible do
    let entries ← initializeLazyEntry e () config
    let entries := entries.map fun (key, entry) => ([key], entry)
    go entries.toArray #[]
where
  /-- The main loop for `encodeExpr`. -/
  go (todo : Array (List Key × LazyEntry Unit)) (result : Array (List Key)) :
      MetaM (Array (List Key)) := do
    if todo.isEmpty then
      return result
    else
      let (keys, entry) := todo.back
      let todo := todo.pop
      match ← evalLazyEntry entry config with
      | .inl xs =>
        let todo := xs.foldl (init := todo) fun todo (key, entry) =>
          todo.push (key :: keys, entry)
        go todo result
      | .inr () =>
        go todo (result.push keys.reverse)


/-- Return the canonical encoding of `e` as a `Array Key`.
This is used for looking up `e` in a `RefinedDiscrTree`. -/
def encodeExpr' (e : Expr) (config : WhnfCoreConfig) : MetaM (Key × List Key) := withReducible do
  let (key, entry) ← initializeLazyEntry' e () config
  let mut result := #[]
  let mut entry := entry
  repeat do match ← evalLazyEntry' entry |>.run config with
    | .inl (key, entry') => entry := entry'; result := result.push key
    | .inr () => break
  return (key, result.toList)
