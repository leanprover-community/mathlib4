module

public import Mathlib.Tactic

/-!
## haha
-/


-- TODO: version of `getRel` that checks that the relation is a transport relation.

open Lean Meta Simp

#check Simp.main


meta section

open Mathlib Tactic GRewrite

open Lean Meta GCongr

namespace Test

/-- Environment extension for "generalized congruence" (`gcongr`) lemmas. -/
initialize transportExt : SimpleScopedEnvExtension GCongrLemma GCongrLemmas ←
  registerSimpleScopedEnvExtension {
    addEntry := addGCongrLemmaEntry
    initial := {}
  }

/-- Get the `gcongr` lemmas whose conclusion has the shape
`relName (head ..) _`, if `forward := true`, or `rel _ (head ..)`, if `forward := false`.
`arity` is the number of arguments in `..`. This is used by the `grw` tactic. -/
def findTransportLemmas? (relName head : Name) (forward : Bool) (arity : Nat) :
    CoreM (List GCongrLemma) := do
  let lemmas := transportExt.getState (← getEnv)
  let some lemmas := lemmas.get? { relName, head, arity } | return []
  if forward then
    return lemmas.filter (·.keys.head!.head == head)
  else
    return lemmas.filter (·.keys.getLast!.head == head)


/-- Try to construct the `GCongrLemma` for a lemma with hypotheses `hyps` and
conclusion `target`. -/
def makeTransportLemma (hyps : Array Expr) (target : Expr) (declName : Name) (prio : Nat) :
    MetaM GCongrLemma := do
  let some (relName, lhs, rhs) := getRel (← whnf target) | throwError "No relation found"
  let some (lhsHead, lhsArgs) := getCongrAppFnArgs lhs | throwError "LHS is not suitable"
  let some (rhsHead, rhsArgs) := getCongrAppFnArgs rhs | throwError "RHS is not suitable"
  let mut mainSubgoals := #[]
  let lhsArgs := lhsArgs.map .eta; let rhsArgs := rhsArgs.map .eta
  let lhsVars := lhsArgs.filter (fun v ↦ v.isFVar && !rhsArgs.contains v)
  let rhsVars := rhsArgs.filter (fun v ↦ v.isFVar && !lhsArgs.contains v)
  -- iterate over antecedents `hyp` to the lemma
  for hyp in hyps, i in 0...* do
    -- Checks if `∀ xs, lhs ~ rhs` is a valid "main goal".
    let isMainGoal? (lhs rhs : Expr) (xs : Array Expr) : Option GCongrHyp :=
      lhs.withApp fun lhs lhsArgs => rhs.withApp fun rhs rhsArgs => do
      /- The relation needs to be of the form `lhs y₁ ... yₙ ~ rhs y₁ ... yₙ`,
      where `yᵢ` are free variables from `xs`,
      and `(lhs, rhs)` is a varying argument pair from the conclusion to the lemma
      We relax these conditions for lemmas that are not used by `grw`. -/
      guard <| lhs.isFVar && lhsArgs.all xs.contains
      guard <| rhs.isFVar && rhsArgs.all xs.contains
      let isContra ←
        if lhsVars.contains lhs && rhsVars.contains rhs then pure false else
        if lhsVars.contains rhs && rhsVars.contains lhs then pure true else
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
  -- store all the information from this parse of the lemma's structure in a `GCongrLemma`
  let mut keys := [{ relName, head := rhsHead, arity := rhsArgs.size }]
  if lhsHead != rhsHead then
    keys := { relName, head := lhsHead, arity := lhsArgs.size } :: keys
  return {
    keys, declName, mainSubgoals, numHyps := hyps.size, prio,
    numVarying := mainSubgoals.size, forGrw := true }

/-- Mark `declName` with the `transport` attribute. -/
def addTransportLemma (declName : Name) (stx : Syntax) (kind : AttributeKind) : MetaM Unit :=
  withReducible do
  let prio ← getAttrParamOptPrio stx[1]
  let cinfo ← getConstInfo declName
  let type := cinfo.type
  forallTelescope type fun xs type => do
  -- If the conclusion is a free variable, it is a lemma like `imp_imp_imp` or `forall_imp`,
  -- so we revert the last two variables.
  if type.getAppFn.isFVar then
    let type ← mkForallFVars xs[(xs.size-2)...xs.size] type
    transportExt.add (← makeTransportLemma xs.pop.pop type declName prio) kind
    return
  try
    -- Add a `transport` lemma in the "normal" way.
    transportExt.add (← makeTransportLemma xs type declName prio) kind
  catch e => try
    addImpGCongrLemma prio cinfo xs type
  catch _ =>
    -- If none of the methods work, we throw the error thrown by the "normal" attempt.
    throw e
where
  addImpGCongrLemma (prio : Nat) (cinfo : ConstantInfo)
      (xs : Array Expr) (type : Expr) : MetaM Unit := do
    let some x := xs.back? | failure
    let type ← mkForallFVars #[x] type
    transportExt.add (← makeTransportLemma xs.pop type declName prio) kind

/-- Attribute marking transport lemmas. -/
syntax (name := transportAttr) "transport" (prio)? : attr

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

/-- Version of `getRel` that also returns the expression of the relation. -/
def getRel' (e : Expr) : Option (Name × Option Expr × Expr × Expr) :=
  match e with
  | .app (.app rel lhs) rhs => rel.getAppFn.constName?.map (·, rel, lhs, rhs)
  | .forallE _ lhs rhs _ =>
    if !rhs.hasLooseBVars then
      some (`_Implies, none, lhs, rhs)
    else
      none
  | _ => none

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
partial def processGCongrLemma (goal : MVarId) (lem : GCongrLemma) (forward : Bool) :
    MetaM Bool :=
  withTraceNode `Meta.grewrite (fun _ ↦
    return m!"applying `gcongr` lemma `{.ofConstName lem.declName}`") do
  let ((mainGoals, sideGoals), _) ← try (applyGCongrLemma goal lem).run catch _ => return false
  -- Recursively rewrite in the main subgoals
  for (goal, isContra) in mainGoals do
    if ← processGCongrHypothesis goal (forward != isContra) then
      continue
    else
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
partial def transportCore (relName : Name) (rel? : Option Expr) (e : Expr) (forward : Bool)
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
  let lemmas ← findTransportLemmas? relName head forward args.size
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
  if relName == ``Eq then
    -- Use `Eq.symm`, and then try again to find an applicable lemma
    let lemmas ← findTransportLemmas? relName head (!forward) args.size
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
  if relName matches ``Eq | `_Implies && !inSimp then
    let methods := { pre e := do
      unless e.isApp do return .continue
      let α ← inferType e
      let some (e', pf) ←
          transportCore ``Eq (Expr.app (.const `Eq [← getLevel α]) α) e true true |
        return .continue
      return .done { expr := e', proof? := pf }
      }
    let (r, _) ← Simp.main e (← Simp.mkContext neutralConfig) (methods := methods)
    if let some proof := r.proof? then
      if relName matches ``Eq then
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
    let some (e, pf) ← transportCore `_Implies none type false |
      throwError "transport made no progress"
    let newGoal ← mkFreshExprMVar e
    mvarId.assign (.app pf newGoal)
    replaceMainGoal [newGoal.mvarId!]


end Test
