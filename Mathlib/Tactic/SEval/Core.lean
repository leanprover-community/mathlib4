import Lean
import Std.Util.TermUnsafe
import Std.Lean.Meta.DiscrTree
import Mathlib.Tactic.NormNum

namespace Mathlib.SEval
open Lean Meta Elab

/-- Attribute for identifying `seval` symbolic evaluators. -/
syntax (name := seval) "sevaluator " term : attr

initialize registerTraceClass `Tactic.seval

/-- Evaluation result. -/
structure Result where
  expr : Expr
  /-- Whether to stop evaluating this expression. -/
  stop : Bool := false
  /-- If none, assumed to be reflexivity -/
  proof? : Option Expr := none
  deriving Inhabited

def Result.rfl (e : Expr) (stop : Bool := false) : Result where
  expr := e
  stop := stop

def Result.trans (r₁ r₂ : Result) : MetaM Result := do
  match r₁.proof? with
  | none => return r₂
  | some p₁ => match r₂.proof? with
    | none    => return { r₂ with proof? := r₁.proof? }
    | some p₂ => return { r₂ with proof? := ← Meta.mkEqTrans p₁ p₂ }

def Result.proof (r : Result) : MetaM Expr := do
  match r.proof? with
  | some p => return p
  | none   => mkEqRefl r.expr

def Result.isRfl (r : Result) : Bool := r.proof?.isNone


def Result.mkCongrFun (r : Result) (a : Expr) : MetaM Result :=
  match r.proof? with
  | none   => return { expr := Expr.app r.expr a, proof? := none }
  | some h => return { expr := Expr.app r.expr a, proof? := (← Meta.mkCongrFun h a) }

def Result.mkCongr (r₁ r₂ : Result) : MetaM Result :=
  let e := Expr.app r₁.expr r₂.expr
  match r₁.proof?, r₂.proof? with
  | none,     none   => return { expr := e, proof? := none }
  | some h,  none    => return { expr := e, proof? := (← Meta.mkCongrFun h r₂.expr) }
  | none,    some h  => return { expr := e, proof? := (← Meta.mkCongrArg r₁.expr h) }
  | some h₁, some h₂ => return { expr := e, proof? := (← Meta.mkCongr h₁ h₂) }


structure Context where

structure State where
  --cache : ExprMap Result

abbrev SEvalM := ReaderT Context $ StateRefT State MetaM

instance : MonadBacktrack SavedState SEvalM where
  saveState      := Meta.saveState
  restoreState s := s.restore

/-- An extension for `seval`. -/
structure SEvaluator where
  /-- The evaluator should be run in the `pre` phase. -/
  pre := false
  /-- The evaluator should be run in the `post` phase. -/
  post := true
  /-- Attempts to prove an expression is equal to some explicit number of the relevant type. -/
  eval : Expr → SEvalM Result
  /-- The name of the constant for this evaluator. -/
  name : Name := by exact decl_name%

/-- Read an evaluator from a declaration of the right type. -/
def mkSEvaluator (n : Name) : ImportM SEvaluator := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck SEvaluator opts ``SEvaluator n

/-- Each evaluator is labeled with a patterns
that determines the expression to which it should be applied. -/
abbrev Entry := Array (DiscrTree.Key true) × Name

/-- The state of the `seval` extension environment -/
structure SEvalExt where
  /-- The tree of evaluators. -/
  tree : DiscrTree SEvaluator true := {}
  /-- Erased evaluators. -/
  erased  : PHashSet Name := {}
  deriving Inhabited

/-- Environment extensions for `seval` -/
initialize sEvalExt : ScopedEnvExtension Entry (Entry × SEvaluator) SEvalExt ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq SEvaluator := ⟨fun _ _ ↦ false⟩
  /- Insert `v : SEvaluator` into the tree `dt` on all key sequences given in `kss`. -/
  registerScopedEnvExtension {
    mkInitial := pure {}
    ofOLeanEntry := fun _ e@(_, n) ↦ return (e, ← mkSEvaluator n)
    toOLeanEntry := (·.1)
    addEntry := fun { tree, erased } ((ks, n), ext) ↦
      { tree := tree.insertCore ks ext, erased := erased.erase n }
  }

/-- Run each registered `seval` evaluator on an expression,
returning a `Result` if any succeed. -/
def evaluator? (e : Expr) (post : Bool) : SEvalM (Option Result) := do
  profileitM Exception "seval" (← getOptions) do
    let s ← saveState
    let sEvals := sEvalExt.getState (← getEnv)
    let arr ← sEvals.tree.getMatch e
    for ev in arr do
      if (bif post then ev.post else ev.pre) && ! sEvals.erased.contains ev.name then
        try
          let new ← ev.eval e
          trace[Tactic.seval] "{ev.name}:\n{e} ==> {new.expr}"
          return new
        catch err =>
          trace[Tactic.seval] "{e} failed: {err.toMessageData}"
          s.restore
    return none

/-- Returns whether `declName` has the `seval` attribute and that it hasn't been erased. -/
def SEvalExt.hasAttr (d : SEvalExt) (declName : Name) : Bool :=
  d.tree.values.any (·.name == declName) && !d.erased.contains declName

/-- Erases a name marked `seval` by adding it to the state's `erased` field and
removing it from the state's list of `Entry`s. -/
def SEvalExt.eraseCore (d : SEvalExt) (declName : Name) : SEvalExt :=
 { d with erased := d.erased.insert declName }

/-- Erase a name marked as a `seval` attribute. Throws an error if it  -/
def SEvalExt.erase [Monad m] [MonadError m] (d : SEvalExt) (declName : Name) : m SEvalExt := do
  unless d.hasAttr declName do
    throwError "'{declName}' does not have [seval] attribute"
  return d.eraseCore declName

initialize registerBuiltinAttribute {
  name := `seval
  descr := "adds an seval evaluator"
  applicationTime := .afterCompilation
  add := fun declName stx kind ↦ match stx with
    | `(attr| seval $patt) => do
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute seval, declaration is in an imported module"
      unless (IR.getSorryDep env declName).isNone do
        return -- ignore in-progress definitions
      let ev ← mkSEvaluator declName
      let key ← MetaM.run' do
        let e ← Term.TermElabM.run' <| withSaveInfoContext <| Term.withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← Term.elabTerm patt none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
      sEvalExt.add ((key, declName), ev) kind
    | _ => throwUnsupportedSyntax
  erase := fun declName => do
    let s := sEvalExt.getState (← getEnv)
    let s ← s.erase declName
    modifyEnv fun env => sEvalExt.modifyState env fun _ => s
}

#check whnfHeadPred

/-- Returns `true` if `e` is computationally irrelevant. -/
def isIrrelevant (e : Expr) : MetaM Bool := withDefault do
  if ← Meta.isType e then
    return true
  if ← Meta.isProof e then
    return true
  return false

-- @[specialize] partial def evalEasyCases (r : Result) (k : Result → SEvalM Result) :
--     SEvalM Result := do
--   if r.stop then
--     return r
--   if ← isIrrelevant r.expr then
--     return {r with stop := true}
--   match r.expr with
--   | .forallE ..    => return {r with stop := true}
--   | .lam ..        => return {r with stop := true}
--   | .sort ..       => return {r with stop := true}
--   | .lit ..        => return {r with stop := true}
--   | .bvar ..       => panic! "loose bvar in expression"
--   | .letE ..       => k r
--   | .const ..      => k r
--   | .app ..        => k r
--   | .proj ..       => k r
--   | .mdata _ e'     => evalEasyCases {r with expr := e'} k
--   | .fvar fvarId   =>
--     match ← fvarId.getDecl with
--     | .cdecl .. => return {r with stop := true}
--     | .ldecl (value := v) .. =>
--       -- We assume that local values have been more-or-less evaluated already.
--       evalEasyCases {r with expr := v} k
--   | .mvar mvarId   =>
--     match ← getExprMVarAssignment? mvarId with
--     | some v => evalEasyCases {r with expr := v} k
--     | none   => return {r with stop := true}

/-- Cache what `x` evaluates to. -/
abbrev cached (α : Type u) (x y : α) (_ : x = y) : α := x

/-- Prevents evaluation of the argument. -/
abbrev hold {α : Sort u} (x : α) : α := x


partial def eval (e : Expr) : SEvalM Result := do
  trace[Tactic.seval] e
  evalCore (.rfl e)
where
  evalCore (r : Result) : SEvalM Result := do
    trace[Tactic.seval] "evalCore: {r.expr}"
    let r ← evalHead r
    trace[Tactic.seval] "evalHead -> {r.expr}"
    if r.stop then return r
    let r ← evalApp r
    trace[Tactic.seval] "evalApp -> {r.expr}"
    if r.stop then return r
    let r ← evalNormNum r
    trace[Tactic.seval] "evalNormNum -> {r.expr}"
    if r.stop then return r
    let r ← evalUnfold r
    trace[Tactic.seval] "evalUnfold -> {r.expr}"
    if r.stop then return r
    return {r with stop := true}
  /-- Evaluator for things like let bindings and lambda applications.
  Does not visit function arguments or unfold constants,
  unless they are function arguments being passed to a lambda. -/
  evalHead (r : Result) : SEvalM Result := do
    if ← isIrrelevant r.expr then
      return {r with stop := true}
    match r.expr with
    | .forallE .. | .lam .. | .sort .. | .lit .. => return {r with stop := true}
    | .bvar .. => panic! "loose bvar in expression"
    | .letE .. => evalHeadLet r
    | .app .. => evalHeadApp r
    | .proj .. => evalHeadProj r
    | .mdata _ e' => evalHead {r with expr := e'}
    | .fvar fvarId =>
      match ← fvarId.getDecl with
      | .cdecl .. => return {r with stop := true}
      | .ldecl (value := v) .. =>
        -- We assume that local values have been more-or-less evaluated already.
        evalHead {r with expr := v}
    | _ => return r
  evalHeadLet (r : Result) : SEvalM Result := do
    let .letE n ty val body _ := r.expr | unreachable!
    let rv ← eval val
    -- Note: if `val` is irrelevant then `rv.proof? = none`
    trace[Tactic.seval] "let {n} := {rv.expr}"
    match rv.proof? with
    | none => evalHead {r with expr := body.instantiate1 rv.expr}
    | some pf =>
      match ← Simp.getSimpLetCase n ty body with
      | .nondep =>
        let bv := body.instantiate1 rv.expr
        let r' : Result :=
          { expr := bv, proof? := some (← mkLetValCongr (.lam n ty body .default) pf) }
        evalHead (← r.trans r')
      | _ =>
        -- In more complicated cases, we can still evaluate the value, at the cost
        -- of pushing equality proofs down into the body.
        let c ← mkAppM ``cached #[ty, val, rv.expr]
        let bc := body.instantiate1 c
        let e := r.expr
        let e' := e.updateLet! ty c body
        let r' : Result :=
          { expr := bc, proof? := some (← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e e')) }
        evalHead (← r.trans r')
  /-- Evaluate special functions at the head, including lambdas. -/
  evalHeadApp (r : Result) : SEvalM Result := do
    let e := r.expr
    if e.isAppOf ``cached && e.getAppNumArgs ≥ 4 then
      let args := e.getAppArgs
      let mut e' := args[2]!
      let mut pf := args[3]!
      for i in [4:args.size] do
        let arg := args[i]!
        e' := Expr.app e' arg
        pf ← mkCongrFun pf arg
      let r' : Result := { expr := e', proof? := some pf }
      return ← evalHead (← r.trans r')
    else if e.isAppOf ``hold then
      return {r with stop := true}
    else if e.isAppOfArity ``OfNat.ofNat 3 && e.appFn!.appArg!.isNatLit then
      return {r with stop := true}
    else if e.getAppFn.isLambda then
      -- Transform it into a `let`
      let f := e.getAppFn
      let args := e.getAppArgs
      let mut body' := f.bindingBody!
      for i in [1:args.size] do
        body' := Expr.app body' args[i]!
      let e' := Expr.letE f.bindingName! f.bindingDomain! args[0]! body' false
      evalHead {r with expr := e'}
    else if let some e' ← reduceRecMatcher? e then
      -- This doesn't evaluate the motive...
      evalCore {r with expr := e'}
    else
      return r
  evalHeadProj (r : Result) : SEvalM Result := do
    trace[Tactic.seval] "evalHeadProj: {r.expr}"
    let e := r.expr
    let s := e.projExpr!
    let rs ← eval s
    match rs.proof? with
    | none =>
      match ← project? rs.expr e.projIdx! with
      | none => return {r with expr := e.updateProj! rs.expr, stop := true}
      | some e => return {r with expr := e, stop := true}
    | some rspf =>
      let motive? ← withLocalDeclD `s (← inferType s) fun s => do
        let p := e.updateProj! s
        if (← dependsOn (← inferType p) s.fvarId!) then
          return none
        else
          let motive ← mkLambdaFVars #[s] (← mkEq e p)
          if !(← isTypeCorrect motive) then
            return none
          else
            return some motive
      if let some motive := motive? then
        let eNew := e.updateProj! rs.expr
        let hNew ← mkEqNDRec motive (← mkEqRefl e) rspf
        r.trans {expr := eNew, proof? := some hNew, stop := true}
      else
        return {r with stop := true}
  visitAppFn (e : Expr) : SEvalM Result := do
    let f := e.getAppFn
    let rf ← eval f
    if rf.expr == f then
      return .rfl e
    let args := e.getAppArgs
    let e' := mkAppN rf.expr args
    if rf.isRfl then
      return .rfl e'
    let mut proof ← rf.proof
    for arg in args do
      proof ← Meta.mkCongrFun proof arg
    return { expr := e', proof? := proof }
  congrArgs (f : Expr) (args : Array Expr) : SEvalM Result := do
    if args.isEmpty then
      return .rfl (mkAppN f args)
    else
      let infos := (← getFunInfoNArgs f args.size).paramInfo
      let mut r := Result.rfl f
      let mut i := 0
      for arg in args do
        if i < infos.size && !infos[i]!.hasFwdDeps then
          r ← r.mkCongr (← eval arg)
        else if (← whnfD (← inferType r.expr)).isArrow then
          r ← r.mkCongr (← eval arg)
        else
          r ← r.mkCongrFun arg
        i := i + 1
      return r
  evalApp (r : Result) : SEvalM Result := do
    trace[Tactic.seval] "evalApp: {r.expr}"
    unless r.expr.isApp do return r
    let r ← r.trans (← visitAppFn r.expr)
    let e := r.expr
    let f := e.getAppFn
    let args := e.getAppArgs
    if f.isLambda then
      return ← evalCore r
    r.trans (← congrArgs f args)
  evalUnfold (r : Result) : SEvalM Result := do
    if let some e' ← reduceRecMatcher? e then
      evalCore {r with expr := e'}
    else if let some e' ← unfoldDefinition? r.expr then
      evalCore {r with expr := e'}
    else
      return r
  evalNormNum (r : Result) : SEvalM Result := do
    try
      let r' ← Mathlib.Meta.NormNum.eval (post := true) r.expr
      let r' : Result := {r' with}
      r.trans r'
    catch _ =>
      return r

def runEval (e : Expr) : MetaM Result := do
  eval e |>.run {} |>.run' {}

elab ref:"#seval " t:term : command => Command.runTermElabM fun _ => do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsUsingDefault
  let e ← instantiateMVars e
  let r ← runEval e
  check (← r.proof)
  logInfoAt ref m!"{r.expr}"
  logInfoAt ref m!"proof = {← r.proof}"

-- partial def evalCore (e : Expr) (simpleReduceOnly := false) : SEvalM Expr :=
--   go e
-- where
--   go (e : Expr) : MetaM Expr :=
--     evalEasyCases e fun e => do
--       trace[Meta.whnf] e
--       match e with
--       | Expr.const ..  => pure e
--       | Expr.letE _ _ v b _ => go <| b.instantiate1 v
--       | Expr.app f ..       =>
--         let f := f.getAppFn
--         let f' ← go f
--         if f'.isLambda then
--           let revArgs := e.getAppRevArgs
--           go <| f'.betaRev revArgs
--         else if let some eNew ← whnfDelayedAssigned? f' e then
--           go eNew
--         else
--           let e := if f == f' then e else e.updateFn f'
--           if simpleReduceOnly then
--             return e
--           else
--             match (← reduceMatcher? e) with
--             | ReduceMatcherResult.reduced eNew => go eNew
--             | ReduceMatcherResult.partialApp   => pure e
--             | ReduceMatcherResult.stuck _      => pure e
--             | ReduceMatcherResult.notMatcher   =>
--               matchConstAux f' (fun _ => return e) fun cinfo lvls =>
--                 match cinfo with
--                 | ConstantInfo.recInfo rec    => reduceRec rec lvls e.getAppArgs (fun _ => return e) go
--                 | ConstantInfo.quotInfo rec   => reduceQuotRec rec lvls e.getAppArgs (fun _ => return e) go
--                 | c@(ConstantInfo.defnInfo _) => do
--                   if (← isAuxDef c.name) then
--                     deltaBetaDefinition c lvls e.getAppRevArgs (fun _ => return e) go
--                   else
--                     return e
--                 | _ => return e
--       | Expr.proj _ i c =>
--         let c ← sEvalCore c
--         match (← projectCore? c i) with
--         | some e => go e
--         | none => return e
--       | _ => unreachable!
