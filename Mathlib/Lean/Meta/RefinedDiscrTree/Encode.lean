import Mathlib.Lean.Meta.RefinedDiscrTree.Basic
import Mathlib.Lean.Meta.RefinedDiscrTree.Pi
import Lean.Meta.DiscrTree
import Batteries.Data.List.Basic

/-!
# Encoding an `Expr` as a sequence of `Key`s

We compute the encoding of and expression in a lazy way.
This is done by computing only one `Key` at a time,
and storing the state of the computation in a `LazyEntry α`.

Each step is computed by `evalLazyEntry : LazyEntry → MetaM (List (Key × LazyEntry α) ⊕ α)`

-/

namespace Lean.Meta.RefinedDiscrTree

private def tmpMVarId : MVarId := { name := `_discr_tree_tmp }
private def tmpStar := mkMVar tmpMVarId

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

/-- Determine for each argument whether it should be ignored. -/
private def getArgsIgnored (fn : Expr) (args : Array Expr) : MetaM (Array Expr) := do
  let mut fnType ← inferType fn
  let mut j := 0
  let mut args := args
  for i in [:args.size] do
    unless fnType.isForall do
      fnType ← whnfD (fnType.instantiateRevRange j i args)
      j := i
    let .forallE _ d b bi := fnType | throwError m! "expected function type {indentExpr fnType}"
    fnType := b
    let arg := args[i]!
    if ← isIgnoredArg arg d bi then
      args := args.set! i tmpStar
  return args
where
  /-- Determine whether the argument should be ignored. -/
  isIgnoredArg (arg domain : Expr) (binderInfo : BinderInfo) : MetaM Bool := do
    if domain.isOutParam then
      return true
    match binderInfo with
    | .instImplicit => return true
    | .implicit
    | .strictImplicit => return !(← isType arg)
    | .default => isProof arg

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
  /-- Variables that come from a lambda that has been removed via η-reduction. -/
  forbiddenVars : List FVarId
  /-- The `whnfCore` configuration -/
  config : WhnfCoreConfig


/-- The monad used for evaluating a `LazyEntr α`. -/
private abbrev LazyM (α : Type) := ReaderT Context StateRefT (LazyEntry α) MetaM

variable {α : Type}

private def mkStar (mvarId : MVarId) : LazyM α Key :=
  modifyGet fun entry =>
    match entry.stars.find? mvarId with
    | some idx => (.star idx, entry)
    | none => (.star entry.nStars,
      { entry with stars := entry.stars.insert mvarId entry.nStars, nStars := entry.nStars + 1 })

private def mkNewStar (entry : LazyEntry α) : Key × LazyEntry α :=
  (.star entry.nStars, {entry with nStars := entry.nStars + 1 })

@[specialize]
private def withLams (lambdas : List FVarId) (key : LazyM α Key) : LazyM α Key := do
  let (key, rest) ← match lambdas with
    | [] => pure (← key, [])
    | _ :: tail => withReader (fun c => { c with bvars := lambdas ++ c.bvars }) do
      pure (.lam, tail.foldl (init := [← key]) fun keys _fvarId => Key.lam :: keys)
  let keys := key :: rest
  modify fun s => { s with
    results := rest
    stack := s.stack.map fun
      | .cache key value => .cache key (keys.foldl (init := value) (·.cons ·))
      | x => x}
  return key

private def makeStackEntry (expr : Expr) : LazyM α StackEntry := do
    return .expr { (← read) with
      expr
      lctx := ← getLCtx
      localInsts := ← getLocalInstances }

private def encodingStepAuxAux (e : Expr) (lambdas : List FVarId) (root : Bool) : LazyM α Key := do
  e.withApp fun fn args => do
  let nargs := e.getAppNumArgs
  let stackArgs : LazyM α Unit := do
    let args ← getArgsIgnored fn args
    args.forRevM fun arg => do
      let arg ← makeStackEntry arg
      modify fun s => { s with stack := arg :: s.stack }

  match fn with
  | .const n _ =>
    unless root do
      /- since `(fun _ => 0) = 0` and `(fun _ => 1) = 1`,
      we don't index lambdas before literals -/
      if let some v := toNatLit? e then
        return ← withLams [] (return .lit v)
    withLams lambdas do
    stackArgs
    return (.const n nargs)
  | .proj n i a =>
    withLams lambdas do
    let struct ← makeStackEntry (if isClass (← getEnv) n then tmpStar else a)
    stackArgs
    modify fun s => { s with stack := struct :: s.stack}
    return .proj n i nargs
  | .fvar fvarId =>
    /- we index `fun x => x` as `id` when not at the root -/
    if args.isEmpty && !root then
      if let fvarId' :: lambdas := lambdas then
        if fvarId' == fvarId then
          return ← withLams lambdas do
          let type ← makeStackEntry (← fvarId.getType)
          modify fun s => { s with stack := type :: s.stack }
          return .const ``id 1
    withLams lambdas do
    if let some idx := (← read).bvars.indexOf? fvarId then
      stackArgs
      return .bvar idx nargs
    stackArgs
    return .fvar fvarId nargs
  | .mvar mvarId =>
    if mvarId == tmpMVarId then
      withLams lambdas (mkStar mvarId)
    /- If there are arguments, don't index the lambdas, as `e` might contain the bound variables
    When not at the root, don't index the lambdas, as it should be able to match with
    `fun _ => x + y`, which is indexed as `(fun _ => x) + (fun _ => y)`. -/
    else if args.isEmpty && (root || lambdas.isEmpty) then
      withLams lambdas (mkStar mvarId)
    else
      withLams [] (modifyGet mkNewStar)

  | .forallE n d b bi =>
    withLams lambdas do
    let d' ← makeStackEntry d
    let b' ← withLocalDecl n bi d fun fvar =>
      withReader (fun c => { c with bvars := fvar.fvarId! :: c.bvars }) do
        makeStackEntry (b.instantiate1 fvar)
    modify fun s => { s with stack := d' :: b' :: s.stack }
    return .forall
  | .lit v      => withLams lambdas <| return .lit v
  | .sort _     => withLams lambdas <| return .sort
  | .letE ..    => withLams lambdas <| return .opaque
  | .lam ..     => withLams lambdas <| return .opaque
  | _           => unreachable!

private def encodingStepAux (e : Expr) (lambdas : List FVarId) (root : Bool) (entry : LazyEntry α) :
    ReaderT Context MetaM (List (Key × LazyEntry α)) := do
  unless root do
    if let some (n, as) ← reducePi e lambdas then
      return ← as.toList.mapM fun (args, lambdas) => do
        (withLams lambdas do
          args.forRevM fun arg => do
            let arg := arg.getD tmpStar
            let arg ← makeStackEntry arg
            modify fun s => { s with stack := arg :: s.stack }
          return .const n args.size).run (← read) |>.run entry

  return [← encodingStepAuxAux e lambdas root |>.run (← read) |>.run entry]

private def encodingStepAux' (e : Expr) (lambdas : List FVarId) (root : Bool) : LazyM α Key := do
  unless root do
    if let some (n, as) ← reducePi e lambdas then
      let (args, lambdas) := as.back
      return ← (withLams lambdas do
        args.forRevM fun arg => do
          let arg := arg.getD tmpStar
          let arg ← makeStackEntry arg
          modify fun s => { s with stack := arg :: s.stack }
        return (.const n args.size))

  encodingStepAuxAux e lambdas root

/-- Run `k` on all pairs of body, bound variables that could possibly appear due to η-reduction -/
@[specialize]
private def etaPossibilities (e : Expr) (lambdas : List FVarId)
    (k : Expr → List FVarId → ReaderT Context MetaM (List α)) : ReaderT Context MetaM (List α) :=
  return (← k e lambdas) ++ (← match e, lambdas with
  | .app f a, fvarId :: lambdas =>
    if isStarWithArg (.fvar fvarId) a then
      withReader (fun c => { c with forbiddenVars := fvarId :: c.forbiddenVars }) do
        etaPossibilities f lambdas k
    else
      return []
  | _, _ => return [])

/-- run `etaPossibilities`, and cache the result if there are multiple possibilities. -/
@[specialize]
private def cacheEtaPossibilities (e original : Expr) (lambdas : List FVarId)
    (cache : AssocList Expr (List Key))
    (ifCached : List Key → (Key × LazyEntry α))
    (k : Expr → List FVarId → ReaderT Context MetaM (List (Key × LazyEntry α))) :
    ReaderT Context MetaM (List (Key × LazyEntry α)) := do
  match e, lambdas with
  | .app _ a, fvarId :: _ =>
    if isStarWithArg (.fvar fvarId) a then
      match cache.find? original with
      | some keys => return ([ifCached keys])
      | none =>
        let possibilities ← etaPossibilities e lambdas k
        return possibilities.map fun (key, entry) =>
          let stackEntry := .cache original (key :: entry.results).reverse
          (key, { entry with stack := stackEntry :: entry.stack })
    else
      k e lambdas
  | _, _ => k e lambdas

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

/-- A single step in encoding an `Expr` into `Key`s. -/
private def encodingStep (original : Expr) (root : Bool) (entry : LazyEntry α) :
    ReaderT Context MetaM (List (Key × LazyEntry α)) := do
  lambdaTelescopeReduce original [] (← read).config
    (fun lambdas => do
      let (key, entry) := mkNewStar entry
      let (key, entry) ← withLams lambdas (pure key) |>.run (← read) |>.run entry
      pure ([(key, entry)]))
    fun e lambdas => do
  cacheEtaPossibilities e original lambdas entry.cache
    (fun | key :: keys => (key, { entry with results := keys }) | [] => (panic! "", entry))
    (fun e lambdas => encodingStepAux e lambdas root entry)

/-- A single step in encoding an `Expr` into `Key`s. -/
private def encodingStep' (original : Expr) (root : Bool) :
    LazyM α Key := do
  lambdaTelescopeReduce original [] (← read).config
    (fun lambdas => withLams lambdas (modifyGet mkNewStar))
    (fun e lambdas => encodingStepAux' e lambdas root)


private partial def processLazyEntryAux (entry : LazyEntry α) :
    ReaderT WhnfCoreConfig MetaM (List (Key × LazyEntry α) ⊕ α) := do
  let stackEntry :: stack := entry.stack | return .inr entry.val
  let entry := { entry with stack }
  match stackEntry with
  | .cache key value =>
    let value := value.reverse
    let entry := if hasLooseBVars value then
      { entry with cache := entry.cache.insert key value }
      else entry
    processLazyEntryAux { entry with cache := entry.cache.insert key (value.reverse) }
  | .star =>
    let (key, entry) := mkNewStar entry
    return .inl [(key, entry)]
  | .expr info =>
    withLCtx info.lctx info.localInsts do
    return .inl (
      ← encodingStep info.expr (root := false) entry |>.run { info with config := ← read})

private partial def processLazyEntryAux' (entry : LazyEntry α) :
    ReaderT WhnfCoreConfig MetaM ((Key × LazyEntry α) ⊕ α) := do
  let stackEntry :: stack := entry.stack | return .inr entry.val
  let entry := { entry with stack }
  match stackEntry with
  | .cache key value =>
    let value := value.reverse
    let entry := if hasLooseBVars value then
      { entry with cache := entry.cache.insert key value }
      else entry
    processLazyEntryAux' { entry with cache := entry.cache.insert key (value.reverse) }
  | .star =>
    let (key, entry) := mkNewStar entry
    return .inl (key, entry)
  | .expr info =>
    withLCtx info.lctx info.localInsts do
    return .inl (
      ← encodingStep' info.expr (root := false) |>.run { info with config := (← read)} |>.run entry)

/-- A single step in evaluating a `LazyEntry α`. -/
def evalLazyEntry (entry : LazyEntry α) (config : WhnfCoreConfig) : MetaM (List (Key × LazyEntry α) ⊕ α) := do
  if let key :: results := entry.results then
    return .inl [(key, { entry with results })]
  else
    processLazyEntryAux entry |>.run config

/-- A single step in evaluating a `LazyEntry α`. -/
private def evalLazyEntry' (entry : LazyEntry α) : ReaderT WhnfCoreConfig MetaM ((Key × LazyEntry α) ⊕ α) := do
  if let key :: results := entry.results then
    return .inl (key, { entry with results })
  else
    processLazyEntryAux' entry

/-- The first step in encoding an `Expr` into `Key`s. -/
private def initializeLazyEntry (e : Expr) (val : α) (config : WhnfCoreConfig) :
    MetaM (List (Key × LazyEntry α)) :=
  encodingStep e true { val } |>.run { bvars := [], forbiddenVars := [], config}

/-- The first step in encoding an `Expr` into `Key`s. -/
private def initializeLazyEntry' (e : Expr) (val : α) (config : WhnfCoreConfig) :
    MetaM (Key × LazyEntry α) :=
  encodingStep' e true |>.run { bvars := [], forbiddenVars := [], config} |>.run { val }


/-- Return as encodings of `e` as a `Array Key`. -/
partial def encodeExpr (e : Expr) (config : WhnfCoreConfig) : MetaM (Array (List Key)) :=
  withReducible do
    let (key, entry) ← initializeLazyEntry' e () config
    go #[([key], entry)] #[]
where
  go (todo : Array (List Key × LazyEntry Unit)) (result : Array (List Key)) :
      MetaM (Array (List Key)) := do
    if todo.isEmpty then
      return result.map List.reverse
    else
      let (keys, entry) := todo.back
      let todo := todo.pop
      match ← evalLazyEntry entry config with
      | .inl xs =>
        let todo := xs.foldl (init := todo) (fun (key, entry) => ·.push (key :: keys, entry))
        go todo result
      | .inr () =>
        go todo (result.push keys)


/-- Return one encoding of `e` as a `Arary Key`. -/
def encodeExpr' (e : Expr) (config : WhnfCoreConfig) : MetaM (List Key) := do
  let (key, entry) ← initializeLazyEntry' e () config
  let mut result := [key]
  let mut entry := entry
  repeat do match ← evalLazyEntry' entry |>.run config with
    | .inl (key, entry') => entry := entry'; result := key :: result
    | .inr () => break
  return result.reverse
