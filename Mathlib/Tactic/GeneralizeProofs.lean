/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Kyle Miller
-/
import Lean.Elab.Tactic.Config
import Lean.Elab.Tactic.Location
import Mathlib.Lean.Expr.Basic
import Batteries.Lean.Expr

/-!
# The `generalize_proofs` tactic

Generalize any proofs occurring in the goal or in chosen hypotheses,
replacing them by local hypotheses.
When these hypotheses are named, this makes it easy to refer to these proofs later in a proof,
commonly useful when dealing with functions like `Classical.choose` that produce data from proofs.
It is also useful to eliminate proof terms to handle issues with dependent types.

For example:
```lean
def List.nthLe {α} (l : List α) (n : ℕ) (_h : n < l.length) : α := sorry
example : List.nthLe [1, 2] 1 (by simp) = 2 := by
  -- ⊢ [1, 2].nthLe 1 ⋯ = 2
  generalize_proofs h
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nthLe 1 h = 2
```

The tactic is similar in spirit to `Lean.Meta.AbstractNestedProofs` in core.
One difference is that it the tactic tries to propagate expected types so that
we get `1 < [1, 2].length` in the above example rather than `1 < Nat.succ 1`.
-/

namespace Mathlib.Tactic
open Lean Meta Elab Parser.Tactic Elab.Tactic

initialize registerTraceClass `Tactic.generalize_proofs

namespace GeneralizeProofs

/--
Configuration for the `generalize_proofs` tactic.
-/
structure Config where
  /-- The maximum recursion depth when generalizing proofs.
  When `maxDepth > 0`, then proofs are generalized from the types of the generalized proofs too. -/
  maxDepth : Nat := 8
  /-- When `abstract` is `true`, then the tactic will create universally quantified proofs
  to account for bound variables.
  When it is `false` then such proofs are left alone. -/
  abstract : Bool := true
  /-- (Debugging) When `true`, enables consistency checks. -/
  debug : Bool := false

/-- Elaborates a `Parser.Tactic.config` for `generalize_proofs`. -/
declare_config_elab elabConfig Config

/-- State for the `MGen` monad. -/
structure GState where
  /-- Mapping from propositions to an fvar in the local context with that type. -/
  propToFVar : ExprMap Expr

/-- Monad used to generalize proofs.
Carries `Mathlib.Tactic.GeneralizeProofs.Config` and `Mathlib.Tactic.GeneralizeProofs.State`. -/
abbrev MGen := ReaderT Config <| StateRefT GState MetaM

/-- Inserts a prop/fvar pair into the `propToFVar` map. -/
def MGen.insertFVar (prop fvar : Expr) : MGen Unit :=
  modify fun s ↦ { s with propToFVar := s.propToFVar.insert prop fvar }

/-- Context for the `MAbs` monad. -/
structure AContext where
  /-- The local fvars corresponding to bound variables.
  Abstraction needs to be sure that these variables do not appear in abstracted terms. -/
  fvars : Array Expr := #[]
  /-- A copy of `propToFVar` from `GState`. -/
  propToFVar : ExprMap Expr
  /-- The recursion depth, for how many times `visit` is called from within `visitProof. -/
  depth : Nat := 0
  /-- The initial local context, for resetting when recursing. -/
  initLCtx : LocalContext
  /-- The tactic configuration. -/
  config : Config

/-- State for the `MAbs` monad. -/
structure AState where
  /-- The prop/proof triples to add to the local context.
  The proofs must not refer to fvars in `fvars`. -/
  generalizations : Array (Expr × Expr) := #[]
  /-- Map version of `generalizations`. Use `MAbs.findProof?` and `MAbs.insertProof`. -/
  propToProof : ExprMap Expr := {}

/--
Monad used to abstract proofs, to prepare for generalization.
Has a cache (of expr/type? pairs),
and it also has a reader context `Mathlib/Tactic/GeneralizeProofs/AContext.lean`
and a state `Mathlib/Tactic/GeneralizeProofs/AState.lean`.
-/
abbrev MAbs := ReaderT AContext <| MonadCacheT (Expr × Option Expr) Expr <| StateRefT AState MetaM

/-- Runs `MAbs` in `MGen`. Returns the value and the `generalizations`. -/
def MGen.runMAbs {α : Type} (mx : MAbs α) : MGen (α × Array (Expr × Expr)) := do
  let s ← get
  let (x, s') ← mx
    |>.run { initLCtx := ← getLCtx, propToFVar := s.propToFVar, config := (← read) }
    |>.run |>.run {}
  return (x, s'.generalizations)

/--
Finds a proof of `prop` by looking at `propToFVar` and `propToProof`.
-/
def MAbs.findProof? (prop : Expr) : MAbs (Option Expr) := do
  if let some pf := (← read).propToFVar[prop]? then
    return pf
  else
    return (← get).propToProof[prop]?

/--
Generalize `prop`, where `proof` is its proof.
-/
def MAbs.insertProof (prop pf : Expr) : MAbs Unit := do
  if (← read).config.debug then
    unless ← isDefEq prop (← inferType pf) do
      throwError "insertProof: proof{indentD pf}does not have type{indentD prop}"
    unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
      throwError "insertProof: proof{indentD pf}\nis not well-formed in the initial context\n\
        fvars: {(← read).fvars}"
    unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx prop do
      throwError "insertProof: proof{indentD prop}\nis not well-formed in the initial context\n\
        fvars: {(← read).fvars}"
  modify fun s ↦
    { s with
      generalizations := s.generalizations.push (prop, pf)
      propToProof := s.propToProof.insert prop pf }

/-- Runs `x` with an additional local variable. -/
def MAbs.withLocal {α : Type} (fvar : Expr) (x : MAbs α) : MAbs α :=
  withReader (fun r => {r with fvars := r.fvars.push fvar}) x

/-- Runs `x` with an increased recursion depth and the initial local context, clearing `fvars`. -/
def MAbs.withRecurse {α : Type} (x : MAbs α) : MAbs α := do
  withLCtx (← read).initLCtx (← getLocalInstances) do
    withReader (fun r => {r with fvars := #[], depth := r.depth + 1}) x

/--
Computes expected types for each argument to `f`,
given that the type of `mkAppN f args` is supposed to be `ty?`
(where if `ty?` is none, there's no type to propagate inwards).
-/
def appArgExpectedTypes (f : Expr) (args : Array Expr) (ty? : Option Expr) :
    MetaM (Array (Option Expr)) :=
  withTransparency .all <| withNewMCtxDepth do
    -- Try using the expected type, but (*) below might find a bad solution
    (guard ty?.isSome *> go f args ty?) <|> go f args none
where
  /-- Core implementation for `appArgExpectedTypes`. -/
  go (f : Expr) (args : Array Expr) (ty? : Option Expr) : MetaM (Array (Option Expr)) := do
    -- Metavariables for each argument to `f`:
    let mut margs := #[]
    -- The current type of `mAppN f margs`:
    let mut fty ← inferType f
    -- Whether we have already unified the type `ty?` with `fty` (once `margs` is filled)
    let mut unifiedFTy := false
    for h : i in [0 : args.size] do
      unless i < margs.size do
        let (margs', _, fty') ← forallMetaBoundedTelescope fty (args.size - i)
        if margs'.isEmpty then throwError "could not make progress at argument {i}"
        fty := fty'
        margs := margs ++ margs'
      let arg := args[i]
      let marg := margs[i]!
      if !unifiedFTy && margs.size == args.size then
        if let some ty := ty? then
          unifiedFTy := (← observing? <| isDefEq fty ty).getD false -- (*)
      unless ← isDefEq (← inferType marg) (← inferType arg) do
        throwError s!"failed isDefEq types {i}, {← ppExpr marg}, {← ppExpr arg}"
      unless ← isDefEq marg arg do
        throwError s!"failed isDefEq values {i}, {← ppExpr marg}, {← ppExpr arg}"
      unless ← marg.mvarId!.isAssigned do
        marg.mvarId!.assign arg
    margs.mapM fun marg => do
      -- Note: all mvars introduced by `appArgExpectedTypes` are assigned by this point
      -- so there is no mvar leak.
      return (← instantiateMVars (← inferType marg)).cleanupAnnotations

/--
Does `mkLambdaFVars fvars e` but
1. zeta reduces let bindings
2. only includes used fvars
3. returns the list of fvars that were actually abstracted
-/
def mkLambdaFVarsUsedOnly (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let i := fvars.size - i' - 1
    let fvar := fvars[i]!
    e ← mkLambdaFVars #[fvar] e
    match e with
    | .letE _ _ v b _ =>
      e := b.instantiate1 v
    | .lam _ _ b _ =>
      if b.hasLooseBVars then
        fvars' := fvar :: fvars'
      else
        e := b
    | _ => unreachable!
  return (fvars'.toArray, e)

/--
Abstract proofs occurring in the expression.
A proof is *abstracted* if it is of the form `f a b ...` where `a b ...` are bound variables
(that is, they are variables that are not present in the initial local context)
and where `f` contains no bound variables.
In this form, `f` can be immediately lifted to be a local variable and generalized.
The abstracted proofs are recorded in the state.

This function is careful to track the type of `e` based on where it's used,
since the inferred type might be different.
For example, `(by simp : 1 < [1, 2].length)` has `1 < Nat.succ 1` as the inferred type,
but from knowing it's an argument to `List.nthLe` we can deduce `1 < [1, 2].length`.
-/
partial def abstractProofs (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then
    MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else
    return e
where
  /--
  Core implementation of `abstractProofs`.
  -/
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    trace[Tactic.generalize_proofs] "visit (fvars := {(← read).fvars}) e is {e}"
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← whnfD ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?)
          | .letE n t v b nondep =>
            let t' ← visit t none
            mapLetDecl n t' (← visit v t') (nondep := nondep) fun x ↦ MAbs.withLocal x do
              visit (b.instantiate1 x) ty?
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          -- Giving up propagating expected types for `.proj`, which we shouldn't see anyway:
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  /--
  Core implementation of abstracting a proof.
  -/
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    -- Strip metadata and beta reduce, in case there are some false dependencies
    let e := e.withApp' fun f args => f.beta args
    -- If head is atomic and arguments are bound variables, then it's already abstracted.
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then
      return e
    -- Abstract `fvars` out of `e` to make the abstracted proof `pf`
    -- The use of `mkLambdaFVarsUsedOnly` is *key* to make sure that the fvars in `fvars`
    -- don't leak into the expression, since that would poison the cache in `MonadCacheT`.
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    trace[Tactic.generalize_proofs] "before mkLambdaFVarsUsedOnly, e = {e}\nfvars={fvars}"
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      trace[Tactic.generalize_proofs] "'abstract' is false and proof uses fvars, not abstracting"
      return eOrig
    trace[Tactic.generalize_proofs] "after mkLambdaFVarsUsedOnly, pf = {pf}\nfvars'={fvars'}"
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    -- Visit the proof type to normalize it and abstract more proofs
    let pfTy ← abstractProofs pfTy none
    -- Check if there is already a recorded proof for this proposition.
    trace[Tactic.generalize_proofs] "finding {pfTy}"
    if let some pf' ← MAbs.findProof? pfTy then
      trace[Tactic.generalize_proofs] "found proof"
      return mkAppN pf' fvars'
    -- Record the proof in the state and return the proof.
    MAbs.insertProof pfTy pf
    trace[Tactic.generalize_proofs] "added proof"
    return mkAppN pf fvars'

/--
Create a mapping of all propositions in the local context to their fvars.
-/
def initialPropToFVar : MetaM (ExprMap Expr) := do
  -- Visit decls in reverse order so that in case there are duplicates,
  -- earlier proofs are preferred
  (← getLCtx).foldrM (init := {}) fun decl m => do
    if !decl.isImplementationDetail then
      let ty := (← instantiateMVars decl.type).cleanupAnnotations
      if ← Meta.isProp ty then
        return m.insert ty decl.toExpr
    return m

/--
Generalizes the proofs in the type `e` and runs `k` in a local context with these propositions.
This continuation `k` is passed
1. an array of fvars for the propositions
2. an array of proof terms (extracted from `e`) that prove these propositions
3. the generalized `e`, which refers to these fvars

The `propToFVar` map is updated with the new proposition fvars.
-/
partial def withGeneralizedProofs {α : Type} [Nonempty α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  trace[Tactic.generalize_proofs] "pre-abstracted{indentD e}\npropToFVar: {propToFVar.toArray}"
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs e ty?
  trace[Tactic.generalize_proofs] "\
    post-abstracted{indentD e}\nnew generalizations: {generalizations}"
  let rec
    /-- Core loop for `withGeneralizedProofs`, adds generalizations one at a time. -/
    go [Nonempty α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          trace[Tactic.generalize_proofs] "after: e' = {e}"
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

/--
Main loop for `Lean.MVarId.generalizeProofs`.
The `fvars` array is the array of fvars to generalize proofs for,
and `rfvars` is the array of fvars that have been reverted.
The `g` metavariable has all of these fvars reverted.
-/
partial def generalizeProofsCore
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) :=
  go g 0 #[]
where
  /-- Loop for `generalizeProofsCore`. -/
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      trace[Tactic.generalize_proofs] "generalizeProofsCore {i}{g}\n{(← get).propToFVar.toArray}"
      let fvar := rfvars[i]
      if fvars.contains fvar then
        -- This is one of the hypotheses that was intentionally reverted.
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          -- Clear the proof value (using proof irrelevance) and `go` again
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar[ty]? then
          -- Eliminate this local hypothesis using the pre-existing proof, using proof irrelevance
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        -- Now the main case, handling forall or let
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g') pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              -- Make this prop available as a proof
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b nondep =>
          withGeneralizedProofs t none fun hs' pfs' t' => do
            withGeneralizedProofs v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b nondep
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g') (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        -- This is one of the hypotheses that was incidentally reverted.
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      trace[Tactic.generalize_proofs] "\
        generalizeProofsCore target{g}\n{(← get).propToFVar.toArray}"
      withGeneralizedProofs (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g') pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)


end GeneralizeProofs

/--
Generalize proofs in the hypotheses `fvars` and, if `target` is true, the target.
Returns the fvars for the generalized proofs and the new goal.

If a hypothesis is a proposition and a `let` binding, this will clear the value of the let binding.

If a hypothesis is a proposition that already appears in the local context, it will be eliminated.

Only *nontrivial* proofs are generalized. These are proofs that aren't of the form `f a b ...`
where `f` is atomic and `a b ...` are bound variables.
These sorts of proofs cannot be meaningfully generalized, and also these are the sorts of proofs
that are left in a term after generalization.
-/
partial def _root_.Lean.MVarId.generalizeProofs
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : GeneralizeProofs.Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← GeneralizeProofs.initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore g fvars rfvars target |>.run config |>.run' s

/--
`generalize_proofs ids* [at locs]?` generalizes proofs in the current goal,
turning them into new local hypotheses.

- `generalize_proofs` generalizes proofs in the target.
- `generalize_proofs at h₁ h₂` generalized proofs in hypotheses `h₁` and `h₂`.
- `generalize_proofs at *` generalizes proofs in the entire local context.
- `generalize_proofs pf₁ pf₂ pf₃` uses names `pf₁`, `pf₂`, and `pf₃` for the generalized proofs.
  These can be `_` to not name proofs.

If a proof is already present in the local context, it will use that rather than create a new
local hypothesis.

When doing `generalize_proofs at h`, if `h` is a let binding, its value is cleared,
and furthermore if `h` duplicates a preceding local hypothesis then it is eliminated.

The tactic is able to abstract proofs from under binders, creating universally quantified
proofs in the local context.
To disable this, use `generalize_proofs -abstract`.
The tactic is also set to recursively abstract proofs from the types of the generalized proofs.
This can be controlled with the `maxDepth` configuration option,
with `generalize_proofs (config := { maxDepth := 0 })` turning this feature off.

For example:
```lean
def List.nthLe {α} (l : List α) (n : ℕ) (_h : n < l.length) : α := sorry
example : List.nthLe [1, 2] 1 (by simp) = 2 := by
  -- ⊢ [1, 2].nthLe 1 ⋯ = 2
  generalize_proofs h
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nthLe 1 h = 2
```
-/
elab (name := generalizeProofsElab) "generalize_proofs" config:Parser.Tactic.optConfig
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← GeneralizeProofs.elabConfig config
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← g.generalizeProofs fvars target config
    -- Rename the proofs using `hs` and record info
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      withLCtx lctx (← getLocalInstances) do
        let g' ← mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Mathlib.Tactic
