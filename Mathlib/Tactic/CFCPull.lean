/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import Lean.Elab.Tactic.Conv.Basic
public meta import Lean.Meta.DiscrTree
public import Mathlib.Init

/-!
# The `cfc_pull` tactic

`cfc_pull R a` rewrites expressions `e` in a C⋆-algebra into the form `cfc f a`, where the scalar
ring `R` and the element `a` are specified by the user, and the function `f : R → R` is computed
by the tactic. For example, if `a` is self-adjoint then `cfc_pull ℂ a` rewrites
`a + I • cfcₙ (√·) (1 - a ^ 2)` to `cfc (fun x : ℂ ↦ x + I * ↑√(1 - x.re ^ 2)) a`.

The tactic works top-down. To pull an expression `e` in the context `(R, a)` it looks up the
lemmas tagged `@[cfc_pull]` whose "pattern" matches `e`, and tries them in order of priority.
There are two kinds of lemmas:

* *Pull lemmas* have the form `cfc F a = P[cfc f₁ a, …, cfc fₙ a]`, e.g.
  `cfc_add : cfc (fun x ↦ f x + g x) a = cfc f a + cfc g a`.
  The pattern is `P[?x₁, …, ?xₙ]`. Each subterm `cfc fᵢ a` of the right-hand side, where `fᵢ` is
  a variable of the lemma and `a` is the element on the left-hand side, is a *hole*. After
  matching `e` against the pattern, the tactic recursively writes each `?xᵢ` as `cfc fᵢ a`. The
  holes may use a different scalar ring than the left-hand side; this is how the tactic changes
  rings, e.g. using `cfc_real_eq_complex` from right to left. A pattern that is a single hole is
  only used when `e` is itself an application of `cfc` over the scalar ring of the hole, since
  it would otherwise match every expression.
  The composition lemma `cfc_comp'` is a pull lemma with pattern `cfc ?g ?x`: on `cfc g b` the
  tactic writes `b` as `cfc f a` *over the scalar ring of `g`*, and then composes. This is what
  makes the tactic context-aware: inside `cfc (√·) (1 - a ^ 2)` over `ℝ`, the expression
  `1 - a ^ 2` is pulled over `ℝ`, even if the outer context is `ℂ`.
* *Rewrite lemmas* are all other lemmas `L = M` (the left-hand side does not have `cfc` as its
  head). If `e` matches `L` then the tactic continues by pulling `M`. For example,
  `cfcₙ_eq_cfc : cfcₙ f a = cfc f a` lets the tactic handle `cfcₙ`.

After normalization succeeds, the remaining hypotheses are deduplicated and discharged. A
hypothesis whose type is `autoParam T tac` is discharged by running `tac` (e.g. `cfc_cont_tac`).
Other hypotheses are tried with `assumption`. If a tactic fails, its hypothesis is left as a
side goal; it does not prevent the structural normalization from succeeding.
-/

public meta section

namespace Mathlib.Tactic.CFCPull

open Lean Meta Elab Tactic

/-- Whether a `cfc_pull` lemma is a pull lemma (left-hand side is `cfc F a`) or a rewrite lemma. -/
inductive Kind where
  | pull
  | rewrite
  deriving Inhabited, BEq, Repr

/-- An entry in the `cfc_pull` discrimination tree. -/
structure Entry where
  /-- The name of the lemma. -/
  declName : Name
  /-- Whether the lemma is used from right to left. -/
  inv : Bool
  /-- The kind of the lemma. -/
  kind : Kind
  /-- The priority of the lemma; higher priority lemmas are tried first. -/
  prio : Nat
  deriving Inhabited, BEq

/-- The `cfc_pull` environment extension. -/
initialize cfcPullExt :
    SimpleScopedEnvExtension (Array DiscrTree.Key × Entry) (DiscrTree Entry) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun d (keys, e) => d.insertKeyValue keys e
  }

/-- If `e` is a fully applied `cfc f a`, return its scalar ring, function, and base.
Only the final two arguments are used, so adding implicit parameters to `cfc` is harmless. -/
def cfcApp? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  unless e.isAppOf `cfc do return none
  unless e.getAppNumArgs == (← getConstInfo `cfc).type.getNumHeadForalls do return none
  let f := e.appFn!.appArg!
  let .forallE _ R _ _ ← whnf (← inferType f) | return none
  return some (R, f, e.appArg!)

/-- The subterms `cfc ?f a` of `t` (in order, without repetitions), where `?f` is a
metavariable. -/
partial def collectHoles (a t : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  match ← cfcApp? t with
  | some (_, f, a') =>
    if f.isMVar && a' == a then
      return if acc.contains t then acc else acc.push t
    else go acc
  | none => go acc
where
  /-- Recurse into the children of `t`. -/
  go (acc : Array Expr) : MetaM (Array Expr) := do
    match t with
    | .app f x => collectHoles a x (← collectHoles a f acc)
    | .lam _ d b _ | .forallE _ d b _ => collectHoles a b (← collectHoles a d acc)
    | .letE _ t v b _ => collectHoles a b (← collectHoles a v (← collectHoles a t acc))
    | .mdata _ e | .proj _ _ e => collectHoles a e acc
    | _ => return acc

/-- The holes in the right-hand side `rhs` of a pull lemma whose left-hand side has element `a`:
the subterms `cfc ?f a` where `?f` is an unassigned metavariable. -/
def findHoles (rhs a : Expr) : MetaM (Array Expr) := do
  collectHoles (← instantiateMVars a) (← instantiateMVars rhs)

/-- Replace the holes of `rhs` by bound variables, giving the motive `fun y₁ … yₙ ↦ P[y]`. -/
def mkMotive (rhs : Expr) (holes : Array Expr) : MetaM Expr := do
  let rhs ← instantiateMVars rhs
  let decls ← holes.mapIdxM fun i h => return (Name.mkSimple s!"y{i}", ← inferType h)
  withLocalDeclsDND decls fun ys => do
    let body := rhs.replace fun t => (holes.findIdx? (· == t)).map (ys[·]!)
    mkLambdaFVars ys body

/-- Compute the discrimination tree keys and the kind of a `cfc_pull` lemma. -/
def mkEntry (declName : Name) (inv : Bool) (prio : Nat) :
    MetaM (Array DiscrTree.Key × Entry) := do
  let lem ← mkConstWithFreshMVarLevels declName
  let (_, _, type) ← forallMetaTelescopeReducing (← inferType lem)
  let some (_, lhs, rhs) := (← whnfR type).eq? |
    throwError "`cfc_pull` lemma {.ofConstName declName} is not an equality"
  let (lhs, rhs) := if inv then (rhs, lhs) else (lhs, rhs)
  match ← cfcApp? lhs with
  | some (_, _, a) =>
    let holes ← findHoles rhs a
    let motive ← mkMotive rhs holes
    let xs ← holes.mapM fun h => do mkFreshExprMVar (← inferType h)
    let pattern := motive.beta xs
    let keys ← DiscrTree.mkPath pattern
    return (keys, { declName, inv, kind := .pull, prio })
  | none =>
    if lhs.getAppFn.isMVar then
      throwError "the left-hand side of `cfc_pull` rewrite lemma {.ofConstName declName} must \
        not be a variable"
    let keys ← DiscrTree.mkPath lhs
    return (keys, { declName, inv, kind := .rewrite, prio })

/--
The `cfc_pull` attribute marks lemmas used by the `cfc_pull` tactic. A lemma of the form
`cfc F a = P[cfc f₁ a, …, cfc fₙ a]` is a *pull lemma*: the tactic matches the pattern `P` and
recursively pulls the subterms in the positions of the holes `cfc fᵢ a`. Any other equation
`L = M` is a *rewrite lemma*: the tactic rewrites `L` to `M` and continues.

Use `@[cfc_pull ←]` to use the lemma from right to left.
-/
syntax (name := cfcPullAttr) "cfc_pull" (" ←" <|> " <-")? (ppSpace prio)? : attr

@[inherit_doc cfcPullAttr]
initialize registerBuiltinAttribute {
  name := `cfcPullAttr
  descr := "lemmas used by the `cfc_pull` tactic"
  add := fun declName stx kind => MetaM.run' do
    let inv := !stx[1].isNone
    let prio ← getAttrParamOptPrio stx[2]
    cfcPullExt.add (← mkEntry declName inv prio) kind
}

/-- The result of pulling an expression `e`. -/
structure Result where
  /-- The function `f`. -/
  f : Expr
  /-- The expression `cfc f a`. -/
  cfcExpr : Expr
  /-- A proof of `e = cfc f a`. -/
  proof : Expr

/-- Unify `t` and `s`, unfolding at most instances. -/
def isDefEqI (t s : Expr) : MetaM Bool := withTransparency .instances <| isDefEq t s

/-- Synthesize the instance arguments among `args` which are not yet assigned.
If `strict` is false, instances that cannot (yet) be synthesized are skipped. -/
def synthInstances (args : Array Expr) (bis : Array BinderInfo) (strict : Bool) : MetaM Unit := do
  for x in args, bi in bis do
    if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
      let type ← instantiateMVars (← inferType x)
      let saved ← saveState
      match ← trySynthInstance type with
      | .some inst =>
        unless ← isDefEq x inst do
          throwError "cfc_pull: failed to assign instance {inst}"
      | _ =>
        saved.restore
        if strict then throwError "cfc_pull: failed to synthesize {type}"

/-- A rule may leave propositions for the user, but must determine all data, including functions. -/
def checkProofMVars (proof : Expr) : MetaM Unit := do
  for g in ← getMVars proof do
    let type ← instantiateMVars (← g.getType)
    unless ← isProp type do
      throwError "cfc_pull: could not determine {mkMVar g} : {type}"

/-- Instantiate the lemma `declName` with fresh metavariables, returning the arguments, their
binder infos, and the left- and right-hand sides (swapped if `inv`). -/
def instantiateLemma (declName : Name) (inv : Bool) :
    MetaM (Array Expr × Array BinderInfo × Expr × Expr × Expr) := do
  let lem ← mkConstWithFreshMVarLevels declName
  let (args, bis, type) ← forallMetaTelescopeReducing (← inferType lem)
  let some (_, lhs, rhs) := (← whnfR type).eq? |
    throwError "`cfc_pull` lemma {.ofConstName declName} is not an equality"
  let pf := mkAppN lem args
  let pf ← if inv then mkEqSymm pf else pure pf
  return if inv then (args, bis, pf, rhs, lhs) else (args, bis, pf, lhs, rhs)

mutual

/-- Write `e` as `cfc f a` over the scalar ring `R`. -/
partial def pull (R a e : Expr) (ancestors : List (Expr × Expr × Expr) := []) :
    MetaM Result := withIncRecDepth do
  checkSystem "cfc_pull"
  let e ← instantiateMVars e
  let key := (← instantiateMVars R, ← instantiateMVars a, e)
  if ancestors.contains key then
    throwError "cfc_pull: cyclic normalization rule"
  -- `e` is already of the form `cfc f a` over `R`.
  if let some (R', f, a') ← cfcApp? e then
    if (← withNewMCtxDepth <| isDefEqI R' R <&&> isDefEqI a' a) then
      return { f, cfcExpr := e, proof := ← mkEqRefl e }
  let entries := (← (cfcPullExt.getState (← getEnv)).getMatch e).insertionSort
    (fun e₁ e₂ => e₁.prio > e₂.prio)
  for entry in entries do
    let s ← saveState
    try
      if let some r ← tryEntry entry R a e (key :: ancestors) then
        return { r with proof := ← mkExpectedTypeHint r.proof (← mkEq e r.cfcExpr) }
      s.restore
    catch ex =>
      if ex.isInterrupt || ex.isMaxHeartbeat || ex.isMaxRecDepth then
        s.restore
        throw ex
      trace[Tactic.cfc_pull] "{.ofConstName entry.declName} failed on {e}: {ex.toMessageData}"
      s.restore
  throwError "cfc_pull: could not write{indentExpr e}\nin the form `cfc _ {a}` over {R}"

/-- Try to pull `e` in the context `(R, a)` using the lemma `entry`. -/
partial def tryEntry (entry : Entry) (R a e : Expr) (ancestors : List (Expr × Expr × Expr)) :
    MetaM (Option Result) := do
  let (args, bis, pf, lhs, rhs) ← instantiateLemma entry.declName entry.inv
  match entry.kind with
  | .rewrite =>
    unless ← isDefEqI lhs e do return none
    synthInstances args bis (strict := true)
    let r ← pull R a (← instantiateMVars rhs) ancestors
    checkProofMVars pf
    let proof ← mkEqTrans (← instantiateMVars pf) r.proof
    return some { r with proof }
  | .pull =>
    let some (R', F, a') ← cfcApp? lhs | return none
    unless ← isDefEqI (← inferType a') (← inferType a) do return none
    unless ← isDefEqI R' R <&&> isDefEqI a' a do return none
    synthInstances args bis (strict := false)
    let holes ← findHoles rhs a
    let motive ← mkMotive rhs holes
    let xs ← holes.mapM fun h => do mkFreshExprMVar (← inferType h)
    let pattern := motive.beta xs
    if pattern.isMVar then
      -- A pattern consisting of a single hole matches everything, so we only use it to change
      -- the scalar ring of an expression `cfc g b` to the scalar ring of the hole.
      let some (S, _, _) ← cfcApp? e | return none
      let some (S', _, _) ← cfcApp? holes[0]! | return none
      unless ← isDefEqI S S' do return none
    unless ← isDefEqI pattern e do return none
    synthInstances args bis (strict := false)
    let mut hs := #[]
    for x in xs, hole in holes do
      let some (S, f, _) ← cfcApp? hole | unreachable!
      let r ← pull (← instantiateMVars S) a (← instantiateMVars x) ancestors
      unless ← isDefEqI f r.f do
        throwError "cfc_pull: failed to assign {f} := {r.f}"
      hs := hs.push r.proof
    synthInstances args bis (strict := true)
    -- `congr : motive xs = motive (cfc fᵢ a)`
    let motive ← instantiateMVars motive
    let mut congr ← mkEqRefl motive
    for h in hs do
      congr ← mkCongr congr h
    let pf ← instantiateMVars pf
    checkProofMVars pf
    let F ← Core.betaReduce (← instantiateMVars F)
    let lhs ← instantiateMVars lhs
    let cfcExpr := mkApp2 lhs.appFn!.appFn! F lhs.appArg!
    let proof ← mkEqTrans congr (← mkEqSymm pf)
    return some { f := F, cfcExpr, proof }

end

initialize registerTraceClass `Tactic.cfc_pull

/-- Share identical obligations, respecting the local contexts of goals created by tactics. -/
def dedupGoals (goals : Array MVarId) : MetaM (List MVarId) := do
  let mut kept : Array MVarId := #[]
  for g in goals do
    if ← g.isAssigned then continue
    let type ← g.getType
    match ← kept.findM? fun k => g.withContext do
        unless (← k.getDecl).lctx.isSubPrefixOf (← g.getDecl).lctx do return false
        withNewMCtxDepth <| withReducible <| isDefEq (← k.getType) type with
    | some k => g.assign (.mvar k)
    | none => kept := kept.push g
  return kept.toList

/-- Discharge only the obligations used in the completed proof. Failed automation leaves a goal. -/
def discharge (proofs : Array Expr) : TermElabM (List MVarId) := do
  let mut remaining := #[]
  let goals ← proofs.foldlM (fun gs proof => return gs ++ (← getMVars proof)) #[]
  for mvarId in ← dedupGoals goals do
    let type ← instantiateMVars (← mvarId.getType)
    let g ← mvarId.withContext <| mkFreshExprSyntheticOpaqueMVar type.consumeTypeAnnotations
    mvarId.assign g
    let g := g.mvarId!
    if ← g.assumptionCore then continue
    let saved ← saveState
    try
      if let some (.const tacticDecl ..) := type.getAutoParamTactic? then
        match evalSyntaxConstant (← getEnv) (← getOptions) tacticDecl with
        | .error err => throwError err
        | .ok tac =>
          remaining := remaining ++ (← Term.withoutErrToSorry <| Tactic.run g (evalTactic tac))
      else
        remaining := remaining.push g
    catch ex =>
      if ex.isInterrupt || ex.isMaxHeartbeat || ex.isMaxRecDepth then
        saved.restore
        throw ex
      trace[Tactic.cfc_pull] "Side-condition tactic failed: {ex.toMessageData}"
      saved.restore
      remaining := remaining.push g
  dedupGoals remaining

/-- Elaborate the scalar ring and the element arguments of `cfc_pull`. -/
def elabArgs (R a : Term) : TacticM (Expr × Expr) := do
  let R ← Term.elabType R
  let a ← Term.elabTerm a none
  Term.synthesizeSyntheticMVarsNoPostponing
  return (← instantiateMVars R, ← instantiateMVars a)

/--
`cfc_pull R a` rewrites both sides of an equation `x = y` in a C⋆-algebra into the form
`cfc f a` and `cfc g a` respectively, where `f g : R → R`. If the resulting functions are
syntactically equal the goal is closed. Hypotheses of the lemmas used which cannot be discharged
automatically are added as new goals.

For example:
```lean
example {a : A} (ha : IsSelfAdjoint a) :
    a + I • cfcₙ (√·) (1 - a ^ 2) = cfc (fun x : ℂ ↦ x + I * ↑√(1 - x.re ^ 2)) a := by
  cfc_pull ℂ a
```

In `conv` mode, `cfc_pull R a` rewrites the focused expression into the form `cfc f a`.

The lemmas used are tagged with `@[cfc_pull]`; see the documentation of that attribute.
-/
syntax (name := cfcPull) "cfc_pull " term:max ppSpace term:max : tactic

@[inherit_doc cfcPull]
syntax (name := cfcPullConv) "cfc_pull " term:max ppSpace term:max : conv

elab_rules : tactic
  | `(tactic| cfc_pull $R $a) => withMainContext do
    let (R, a) ← elabArgs R a
    let goal ← getMainGoal
    let some (_, lhs, rhs) := (← whnfR (← instantiateMVars (← goal.getType))).eq? |
      throwError "cfc_pull: the goal is not an equation"
    let r₁ ← pull R a lhs
    let r₂ ← pull R a rhs
    let goals ← discharge #[r₁.proof, r₂.proof]
    let newGoal ← mkFreshExprSyntheticOpaqueMVar (← mkEq r₁.cfcExpr r₂.cfcExpr)
    goal.assign (← mkEqTrans r₁.proof (← mkEqTrans newGoal (← mkEqSymm r₂.proof)))
    let mainGoals ← if ← withReducible <| isDefEq r₁.cfcExpr r₂.cfcExpr then
        newGoal.mvarId!.refl
        pure []
      else pure [newGoal.mvarId!]
    replaceMainGoal (mainGoals ++ goals)

elab_rules : conv
  | `(conv| cfc_pull $R $a) => withMainContext do
    let (R, a) ← elabArgs R a
    let r ← pull R a (← Conv.getLhs)
    let goals ← discharge #[r.proof]
    Conv.updateLhs r.cfcExpr r.proof
    replaceMainGoal ((← getMainGoal) :: goals)

end Mathlib.Tactic.CFCPull
