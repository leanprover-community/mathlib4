module

public import Mathlib.Tactic

/-!
## haha
-/


-- TODO: version of `getRel` that checks that the relation is a transport relation.

meta section

open Mathlib Tactic GRewrite

open Lean Meta GCongr

namespace Test

inductive RelKind where
  | imp | eq | other
  deriving Inhabited, BEq, Ord

/-- `GCongrKey` is the key used in the dictionary for looking up `gcongr` lemmas. -/
structure TransportKey where
  /-- The kind of relation. -/
  relKind : RelKind
  /-- The name of the head function. For example, `a + b ≤ a + c` has ``head := `HAdd.hAdd``. -/
  head : Name
  /-- The number of arguments that `head` is applied to.
  For example, `a + b ≤ a + c` has `arity := 6`, because `HAdd.hAdd` has 6 arguments. -/
  arity : Nat
deriving Inhabited, BEq

instance : Ord TransportKey where
  compare a b := a.2.quickCmp b.2 |>.then (compare a.1 b.1) |>.then (compare a.3 b.3)

/-- Structure recording the data for a "generalized congruence" (`gcongr`) lemma. -/
structure TransportLemma where
  /-- The keys under which the lemma is stored. This is usually one key,
  but for `gcongr strict` lemmas, this stores two keys, for the LHS and RHS respectively. -/
  keys : List TransportKey
  /-- The name of the lemma. -/
  declName : Name
  /-- `mainSubgoals` are the subgoals on which `gcongr` will be recursively called. -/
  mainSubgoals : Array GCongrHyp
  /-- The number of arguments that `declName` takes when applying it. -/
  numHyps : Nat
  /-- The given priority of the lemma, for example as `@[gcongr high]`. -/
  prio : Nat
  /-- The number of arguments in the application of `head` that are different.
  This is used for sorting the lemmas.
  For example, `a + b ≤ a + c` has `numVarying := 1`. -/
  numVarying : Nat
  /-- Whether the lemma is suitable for use in `grw`. For most lemmas this is `true`,
  but there are lemmas that aren't quite congruence lemmas, but can still be used in `gcongr`. -/
  forGrw : Bool
  /-- All pairs of types `α`, `β` such that `α` translates to/from `β`. -/
  relatedTypes : Option (Nat × Nat)
  deriving Inhabited


def translateType (type : Expr) : MetaM Expr :=
  match type with
  | .app (.const ``Option us) α => return .app (.const ``Option us) (← translateType α)
  | .app (.const ``Set us) α => return .app (.const ``Finset us) α
  | .app (.const ``Finset us) α => return .app (.const ``Set us) α
  | _ => return type


/-- Run the `intro` tactic `n` times on the given goal. -/
private def introN (goal : MVarId) (n : Nat) : GCongrM (List MVarId) := do
  let (goals, patterns) ← goal.rintroWithPats (← get).patterns n
  modify ({· with patterns})
  return goals

/-- Apply generalized congruence lemma `lem` to goal `g`, throwing an error if it fails.
Return an array of main subgoals and an array of side goals.
For each main subgoal, also return whether the sides of the relation are swapped
(i.e. whether it is contravariant).

This function is used by both the `gcongr` and `grw` tactic.
In the case of `grw`, one of the two sides of the goal is a metavariable that is filled in
by this function.

In the main subgoals, the forall binders are introduced. They are named using the `with` clause of
`gcongr`, or otherwise using binder names in the goal. `grw` relies on these names to ensure that
binder names are preserved in the goal.
-/
def applyGCongrLemma (g : MVarId) (lem : TransportLemma) :
    GCongrM (Array (MVarId × Bool) × Array MVarId) := do
  let const ← mkConstWithFreshMVarLevels lem.declName
  let type ← inferType const
  -- Use `withDefault` so that we can unfold `Monotone`.
  let (mvars, bis, type) ← withDefault <| forallMetaTelescopeReducing type lem.numHyps
  guard <| ← approxDefEq <| isDefEq (← g.getType) (← preprocess type)
  if let some (i, j) := lem.relatedTypes then
    let some α := mvars[i]? |
      throwError "expected `{.ofConstName lem.declName}` to have at least {i} arguments"
    let some β := mvars[j]? |
      throwError "expected `{.ofConstName lem.declName}` to have at least {j} arguments"
    let α ← instantiateMVars α; let β ← instantiateMVars β
    let setType (oldType mvar : Expr) := do
      let newType ← translateType oldType
      unless ← isDefEq newType mvar do throwError "failed to assing {mvar} with `{newType}`"
    match α.isMVar, β.isMVar with
    | false, true => setType α β
    | true, false => setType β α
    | _, _ => throwError "expected exactly one of `{α}` and `{β}` to be a metavariable"
  g.assign (mkAppN const mvars)
  let mut sideGoals := #[]
  for mvar in mvars, i in 0...* do
    let mvarId := mvar.mvarId!
    if ← mvarId.isAssigned then continue
    -- Filter out metavariables from the main subgoals
    if lem.mainSubgoals.any (fun h ↦ h.lhsIdx == i || h.rhsIdx == i || h.hypIdx == i) then continue
    -- Synthesize instance implicit arguments.
    -- We allow synthesis to get stuck, because in the case of `grw`
    -- there may be unassigned metavariables in the type.
    if bis[i]!.isInstImplicit then
      match ← trySynthInstance (← mvarId.getType) with
      | .some inst => mvarId.assign inst; continue
      | .none => failure
      | .undef => sideGoals := sideGoals.push mvarId
    else
      sideGoals := sideGoals.push mvarId
  let mainGoals ← lem.mainSubgoals.flatMapM fun h ↦ do
    let mvarId := mvars[h.hypIdx]!.mvarId!
    if (← get).patterns.isEmpty then
      -- If the user did not provide binders (using `gcongr with ...`),
      -- instead use binder names appearing in the LHS/RHS of the target relation.
      let lhsNames := lambdaBinderNames (← instantiateMVars mvars[h.lhsIdx]!)
      let rhsNames := lambdaBinderNames (← instantiateMVars mvars[h.rhsIdx]!)
      let lambdaNames := if lhsNames.size ≥ rhsNames.size then lhsNames else rhsNames
      let names := h.hypsPos.map (·.elim `_ (lambdaNames.getD · `_))
      return #[((← mvarId.introN h.hypsPos.length names).2, h.isContra)]
    else
      return (← introN mvarId h.hypsPos.length).toArray.map (·, h.isContra)
  return (mainGoals, sideGoals)
where
  /-- Get the binder names from a lambda function. -/
  lambdaBinderNames (e : Expr) (acc : Array Name := #[]) : Array Name :=
    match e with
    | .lam n _ b _ => lambdaBinderNames b (acc.push n)
    | _ => acc
  /-- Remove any redundant eta expansions in the arguments on either side of the relation `e`.
  As a result, the corresponding binder names are removed, so they cannot end up in the expression
  produced by `grw`. -/
  preprocess (e : Expr) : MetaM Expr := do
    let normArgs (x : Expr) := x.headBeta.withApp (mkAppN · <| ·.map Expr.eta)
    match ← whnf e with
    | .forallE _ lhs rhs _ => return e.updateForallE! (normArgs lhs) (normArgs rhs)
    | mkApp2 rel lhs rhs => return mkApp2 rel (normArgs lhs) (normArgs rhs)
    | _ => throwError "internal `gcongr` error: expected `{e}` to be a relation"

/-- A collection of `TransportLemma`, to be stored in the environment extension. -/
abbrev TransportLemmas := Std.TreeMap TransportKey (List TransportLemma)

/-- Return `true` if the priority of `a` is less than or equal to the priority of `b`. -/
def TransportLemma.prioLE (a b : TransportLemma) : Bool :=
  (compare a.prio b.prio).then (compare b.numVarying a.numVarying) |>.isLE

/-- Insert a `TransportLemma` in a collection of lemmas, making sure they are sorted by priority. -/
def addTransportLemmaEntry (m : TransportLemmas) (l : TransportLemma) : TransportLemmas :=
  l.keys.foldl (init := m) fun m key ↦ m.alter key fun
    | none    => [l]
    | some es => insert l es
where
  /--- Insert a `TransportLemma` in the correct place in a list of lemmas. -/
  insert (l : TransportLemma) : List TransportLemma → List TransportLemma
    | []     => [l]
    | l'::ls => if l'.prioLE l then l::l'::ls else l' :: insert l ls

/-- Environment extension for "generalized congruence" (`gcongr`) lemmas. -/
initialize transportExt : SimpleScopedEnvExtension TransportLemma TransportLemmas ←
  registerSimpleScopedEnvExtension {
    addEntry := addTransportLemmaEntry
    initial := {}
  }

/-- Get the `gcongr` lemmas whose conclusion has the shape
`relName (head ..) _`, if `forward := true`, or `rel _ (head ..)`, if `forward := false`.
`arity` is the number of arguments in `..`. This is used by the `grw` tactic. -/
def findTransportLemmas? (relKind : RelKind) (head : Name) (forward : Bool) (arity : Nat) :
    CoreM (List TransportLemma) := do
  let lemmas := transportExt.getState (← getEnv)
  let some lemmas := lemmas.get? { relKind, head, arity } | return []
  if forward then
    return lemmas.filter (·.keys.head!.head == head)
  else
    return lemmas.filter (·.keys.getLast!.head == head)

/-- If `e` is of the form `r a b`, return `(r, a, b)`.
Note: we assume that `e` does not have an `Expr.mdata` annotation. -/
def getRel (e : Expr) : Option (RelKind × Expr × Expr) :=
  match e with
  | mkApp2 (.app (.const ``Eq _) _) lhs rhs => some (.eq, lhs, rhs)
  | mkApp2 _ lhs rhs => some (.other, lhs, rhs)
  | .forallE _ lhs rhs _ =>
    if !rhs.hasLooseBVars then
      some (.imp, lhs, rhs)
    else
      none
  | _ => none

/-- Version of `getRel` that also returns the expression of the relation. -/
def getRel' (e : Expr) : Option (RelKind × Option Expr × Expr × Expr) :=
  match e with
  | mkApp2 rel@(.app (.const ``Eq _) _) lhs rhs => some (.eq, rel, lhs, rhs)
  | mkApp2 rel lhs rhs => some (.other, rel, lhs, rhs)
  | .forallE _ lhs rhs _ =>
    if !rhs.hasLooseBVars then
      some (.imp, none, lhs, rhs)
    else
      none
  | _ => none


/-- Try to construct the `TransportLemma` for a lemma with hypotheses `hyps` and
conclusion `target`. -/
def makeTransportLemma (hyps : Array Expr) (target : Expr) (declName : Name) (prio : Nat)
    (intro? : Bool) : MetaM TransportLemma := do
  let some (relKind, lhs, rhs) := getRel (← whnf target) | throwError "No relation found"
  let some (lhsHead, lhsArgs) := getCongrAppFnArgs lhs | throwError "LHS is not suitable"
  let some (rhsHead, rhsArgs) := getCongrAppFnArgs rhs | throwError "RHS is not suitable"
  let mut mainSubgoals := #[]
  let lhsVars' := (collectFVars {} lhs).fvarSet
  let rhsVars' := (collectFVars {} rhs).fvarSet
  let lhsVars := lhsVars'.diff rhsVars'
  let rhsVars := rhsVars'.diff lhsVars'
  -- iterate over antecedents `hyp` to the lemma
  for hyp in hyps, i in 0...* do
    -- Checks if `∀ xs, lhs ~ rhs` is a valid "main goal".
    let isMainGoal? (lhs rhs : Expr) (xs : Array Expr) : Option GCongrHyp :=
      lhs.withApp fun lhs lhsArgs => rhs.withApp fun rhs rhsArgs => do
      /- The relation needs to be of the form `lhs y₁ ... yₙ ~ rhs y₁ ... yₙ`,
      where `yᵢ` are free variables from `xs`,
      and `(lhs, rhs)` is a varying argument pair from the conclusion to the lemma
      We relax these conditions for lemmas that are not used by `grw`. -/
      let .fvar lhsFVarId := lhs | none
      let .fvar rhsFVarId := rhs | none
      guard <| lhsArgs.all xs.contains && rhsArgs.all xs.contains
      let isContra ←
        if lhsVars.contains lhsFVarId && rhsVars.contains rhsFVarId then pure false else
        if lhsVars.contains rhsFVarId && rhsVars.contains lhsFVarId then pure true else
        none
      let lhsIdx ← hyps.idxOf? lhs
      let rhsIdx ← hyps.idxOf? rhs
      let hypsPos := xs.toList.map lhsArgs.idxOf?
      some { lhsIdx, rhsIdx, hypIdx := i, hypsPos, isContra }
    -- Checks if `hyp` is a valid "main goal".
    let go := forallTelescopeReducing (← inferType hyp) fun xs hypTy => do
      if let some (_, lhs₁, rhs₁) := getRel (← whnf hypTy) then
        return isMainGoal? lhs₁ rhs₁ xs
      else if let some lastFVar := xs.back? then
        return isMainGoal? (← inferType lastFVar) hypTy xs.pop
      return none
    if let some mainSubgoal ← go then
      mainSubgoals := mainSubgoals.push mainSubgoal
  -- store all the information from this parse of the lemma's structure in a `TransportLemma`
  let mut keys := [{ relKind, head := rhsHead, arity := rhsArgs.size }]
  if lhsHead != rhsHead then
    keys := { relKind, head := lhsHead, arity := lhsArgs.size } :: keys
  return {
    keys, declName, mainSubgoals, numHyps := hyps.size, prio,
    numVarying := mainSubgoals.size, forGrw := true
    relatedTypes := if intro? then some (0, 1) else none }

/-- Mark `declName` with the `transport` attribute. -/
def addTransportLemma (declName : Name) (stx : Syntax) (kind : AttributeKind) : MetaM Unit :=
  withReducible do
  let intro? := !stx[1].isNone
  let prio ← getAttrParamOptPrio stx[2]
  let cinfo ← getConstInfo declName
  let type := cinfo.type
  forallTelescope type fun xs type => do
  -- If the conclusion is a free variable, it is a lemma like `imp_imp_imp` or `forall_imp`,
  -- so we revert the last two variables.
  if type matches .fvar _ | .app (.fvar _) _ then
    let type ← mkForallFVars xs[(xs.size-2)...xs.size] type
    transportExt.add (← makeTransportLemma xs.pop.pop type declName prio intro?) kind
    return
  try
    -- Add a `transport` lemma in the "normal" way.
    transportExt.add (← makeTransportLemma xs type declName prio intro?) kind
  catch e => try
    addImpGCongrLemma cinfo xs type prio intro?
  catch _ =>
    -- If none of the methods work, we throw the error thrown by the "normal" attempt.
    throw e
where
  addImpGCongrLemma (cinfo : ConstantInfo) (xs : Array Expr) (type : Expr) (prio : Nat)
      (intro? : Bool) : MetaM Unit := do
    let some x := xs.back? | failure
    let type ← mkForallFVars #[x] type
    transportExt.add (← makeTransportLemma xs.pop type declName prio intro?) kind

/-- Attribute marking transport lemmas. -/
syntax (name := transportAttr) "transport" (&"intro")? (ppSpace prio)? : attr

@[inherit_doc transportAttr]
initialize registerBuiltinAttribute {
  name := `transportAttr
  descr := "transport"
  add := (addTransportLemma · · · |>.run')
}





/-- The result returned by `Lean.MVarId.grewrite`. -/
public structure GRewriteResult where
  /-- The rewritten expression -/
  eNew : Expr
  /-- The proof of the implication. The direction depends on the argument `forwardImp`. -/
  impProof : Expr
  /-- The new side goals -/
  mvarIds : List MVarId -- new goals




/-- The state used in `GRewriteM`. -/
structure State where
-- /-- The cache used in `grw` to avoid trying and failing to rewrite the same term multiple times.
-- Each key stores the relation (`none` encodes the `→` relation), rewritten expression,
-- and direction of the rewrite.
-- This lets us avoid an exponential blowup when there are multiple `gcongr` lemmas for rewriting
-- in the same place, such as `add_le_add`, `add_le_add_left` and `add_le_add_right`. -/
-- cache : Std.HashSet (Option Expr × Expr × Bool) := {}
-- /-- The current progress level. -/
-- progress : Progress := .noMatch

/-- The information about the given rewrite lemma. -/
structure GRewriteLemma where


/-- The monad used for `grw`. -/
abbrev GRewriteM := ReaderT GRewriteLemma StateRefT State GCongr.GCongrM

/-- Create the `gcongr` goal corresponding to rewriting `e` by relation `rel?`,
so that we can apply `gcongr` lemmas to it. -/
def makeGCongrGoal (rel? : Option Expr) (e : Expr) (forward : Bool) : MetaM (Expr × Expr) := do
  if let some rel := rel? then
    let .forallE _ d₁ (.forallE _ d₂ _ _) _ ← whnf (← inferType rel) | throwFunctionExpected rel
    -- note that `@[gcongr]`'s checks should prevent this happening
    if d₂.hasLooseBVars then throwError "grw: {rel} is a dependent relation"
    if forward then
      let mvar ← mkFreshExprMVar d₂
      return (mvar, ← mkFreshExprMVar <| mkApp2 rel e mvar)
    else
      let mvar ← mkFreshExprMVar d₁
      return (mvar, ← mkFreshExprMVar <| mkApp2 rel mvar e)
  else
    let mvar ← mkFreshTypeMVar
    let target := if forward then .forallE `_a e mvar .default else .forallE `_a mvar e .default
    return (mvar, ← mkFreshExprMVar (some target))


mutual

/-- Recursively call `transportCore` to process a subgoal of a `gcongr` lemma.

Returns whether we have done a rewrite in this subgoal, in which case it has been closed. -/
partial def processGCongrHypothesis (goal : MVarId) (forward : Bool) :
    MetaM Bool := do
  goal.withContext do
  let some (relName, rel?, lhs, rhs) := getRel' (← whnf (← goal.getType)) |
    throwError "internal `grewrite` error: invalid `gcongr` goal {goal}"
  let (target, mvarApp) := if forward then (lhs, rhs) else (rhs, lhs)
  let target ← instantiateMVars target; let rel? ← rel?.mapM instantiateMVars
  if let some (result, proof) ← transportCore relName rel? target forward then
    -- Assign any remaining universe variables
    unless ← isDefEq (← inferType mvarApp) (← inferType result) do
      throwError "internal `transport` error: couldn't set `{mvarApp}` to `{result}`"
    mvarApp.withApp fun mvar xs ↦ do
      /- Note: the names of the free variables `xs` end up in the new goal as lambda binders.
      `applyGCongrLemma` ensures that these are the binder names that appear in the original goal.
      As a result, when rewriting inside of `{x | p x}`, the binder name `x` is preserved. -/
      mvar.mvarId!.assign (← mkLambdaFVars xs result)
      goal.assign proof
      return true
  else
    return false

/-- Apply the `gcongr` lemma to the goal. The main subgoals are visited for rewriting in,
and otherwise closed `by rfl`. If at least one rewrite has happened, we commit to this lemma,
and we try to discharge the side goals.

Returns whether we have done a rewrite in this subgoal, in which case it has been closed. -/
partial def processGCongrLemma (goal : MVarId) (lem : TransportLemma) (forward : Bool) :
    MetaM Bool :=
  withTraceNode `Meta.grewrite (fun _ ↦
    return m!"applying `gcongr` lemma `{.ofConstName lem.declName}`") do
  let ((mainGoals, sideGoals), _) ← try (applyGCongrLemma goal lem).run catch _ => return false
  -- Recursively rewrite in the main subgoals
  for (goal, isContra) in mainGoals do
    if ← processGCongrHypothesis goal (forward != isContra) then
      continue
    try
      -- Due to an issue in `rfl`, we need this transparency bump. See https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.60with_reducible.20rfl.60.20failing/with/590957602
      withReducibleAndInstances goal.applyRflOrId
    catch _ =>
      return false
  -- Finally, run the discharger on the side goals.
  for mvarId in sideGoals do
    let type ← mvarId.getType
    -- There may be instance side goals that still had metavariables before recursively rewriting.
    if (← isClass? type).isSome then
      if let some inst ← synthInstance? type then
        mvarId.assign inst
        continue
    -- else
    --   dischargeSide mvarId
  return true

/-- The core of the `grw` implementation. Rewrite in the expression `e` which occurs under the
relation `relName`/`rel?`, using the `GRewriteLemma` stored in `MetaM`.
If `e` itself cannot be rewritten, descend into subexpressions of `e` using `@[gcongr]` lemmas.

`rel?` should be an expression with head symbol `relName`,
unless the relation is `→`: `relName` is `_Implies` and `rel?` is `none`.

Returns the new expression and a proof that it is related to `e`, if a rewrite was found. -/
partial def transportCore (relKind : RelKind) (rel? : Option Expr) (e : Expr) (forward : Bool)
    (inSimp := false) :
    MetaM (Option (Expr × Expr)) :=
  withTraceNodeBefore `Meta.grewrite (fun _ ↦ return m!"visiting `{e}` in the \
    {if forward then "LHS" else "RHS"} of relation `{rel?.elim m!"→" (m!"{·}")}`") do
  -- Try all applicable `@[gcongr]` lemmas.
  let some (head, args) := getCongrAppFnArgs e |
    let (mvar, goal) ← makeGCongrGoal rel? e forward
    for ldecl in ← getLCtx do
      if !ldecl.isImplementationDetail then
        if ← isDefEq ldecl.type (← inferType goal) then
          goal.mvarId!.assign ldecl.toExpr
          return some (← instantiateMVars mvar, goal)
    return none
  let lemmas ← findTransportLemmas? relKind head forward args.size
  unless lemmas.isEmpty do
    let (mvar, goal) ← makeGCongrGoal rel? e forward
    let mctx ← getMCtx
    for gcongrLem in lemmas do
      if gcongrLem.forGrw then
        if ← processGCongrLemma goal.mvarId! gcongrLem forward then
          -- Preserve the binder name/info in a forall.
          match e, ← instantiateMVars mvar with
          | .forallE n _ _ bi, .forallE _ d b _ => return some (.forallE n d b bi, goal)
          | _, result => return some (result, goal)
        setMCtx mctx
  if relKind matches .eq then
    -- Use `Eq.symm`, and then try again to find an applicable lemma
    let lemmas ← findTransportLemmas? relKind head (!forward) args.size
    unless lemmas.isEmpty do
      let (mvar, goal) ← makeGCongrGoal rel? e forward
      let symmGoal ← goal.mvarId!.applySymm
      let mctx ← getMCtx
      for gcongrLem in lemmas do
        if gcongrLem.forGrw then
          if ← processGCongrLemma symmGoal gcongrLem (!forward) then
            -- Preserve the binder name/info in a forall.
            match e, ← instantiateMVars mvar with
            | .forallE n _ _ bi, .forallE _ d b _ => return some (.forallE n d b bi, goal)
            | _, result => return some (result, goal)
          setMCtx mctx
  if relKind matches .eq | .imp && !inSimp then
    let methods := { pre e := do
      unless e.isApp do return .continue
      let α ← inferType e
      let some (e', pf) ←
          transportCore .eq (Expr.app (.const `Eq [← getLevel α]) α) e true true |
        return .continue
      return .done { expr := e', proof? := pf }
      }
    let (r, _) ← Simp.main e (← Simp.mkContext Simp.neutralConfig) (methods := methods)
    if let some proof := r.proof? then
      if relKind matches .eq then
        return some (r.expr, ← if forward then pure proof else mkAppM ``Eq.symm #[proof])
      else
        return some (r.expr, ← mkAppM (if forward then ``Eq.mp else ``Eq.mpr) #[proof])
  return none

end

open Elab Tactic

elab "transport" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do withReducible do
    let type ← mvarId.getType
    let some (e, pf) ← transportCore .imp none type false |
      throwError "transport made no progress"
    let newGoal ← mkFreshExprMVar e
    mvarId.assign (.app pf newGoal)
    replaceMainGoal [newGoal.mvarId!]


end Test
