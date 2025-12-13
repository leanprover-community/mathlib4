import Mathlib.Tactic.DataSynth.Types
import Mathlib.Tactic.DataSynth.Theorems
import Mathlib.Tactic.FunProp.Elab
import Batteries.Tactic.Exact

import Lean.Meta.Transform

set_option linter.unusedVariables false

namespace Mathlib.Meta.DataSynth

open Lean Meta

/-- Tracing node that does not do any pretty printing so it is usefull for profiling. -/
private def withProfileTrace {α : Type} (msg : String) (x : DataSynthM α) : DataSynthM α :=
  withTraceNode `Meta.Tactic.data_synth.profile (fun _ => return msg) x

private def withMainTrace {α : Type} (msg : Except Exception α → DataSynthM MessageData)
  (x : DataSynthM α) :
    DataSynthM α :=
  withTraceNode `Meta.Tactic.data_synth msg x

private def _root_.Lean.Meta.Simp.Result.andThen (r : Simp.Result) (f : Simp.Simproc) :
    SimpM Simp.Result := do
  match ← Simp.mkEqTransResultStep r (← f r.expr) with
  | .done r | .visit r | .continue (some r) => return r
  | .continue none => return r

def normalize (e : Expr) : DataSynthM (Simp.Result) := do
  withProfileTrace "normalization" do

  let e ← instantiateMVars e

  let simpCache := (← getThe Simp.State).cache
  match simpCache.find? e with
  | some r =>
    trace[Meta.Tactic.data_synth.normalize] m!"cached normalization\n{e}\n==>\n{r.expr}"
    return r
  | none =>

    let cfg := (← read).config

    let e₀ := e
    let mut e := e

    if cfg.norm_dsimp then
      e ← Simp.dsimp e

    let mut r : Simp.Result := { expr := e}

    if cfg.norm_simp then
      r ← r.mkEqTrans (← Simp.simp r.expr)

    -- user specified normalization
    r ← r.mkEqTrans (← (← read).norm r.expr)

    -- report only when something has been done
    if ¬(e₀==r.expr) then
      trace[Meta.Tactic.data_synth.normalize] m!"\n{e₀}\n==>\n{r.expr}"

    Simp.cacheResult e { cfg with } r


def Result.normalize (r : Result) : DataSynthM Result := do
  withProfileTrace "normalize result" do
  r.congr (← r.xs.mapM DataSynth.normalize)


def Goal.getCandidateTheorems (g : Goal) : DataSynthM (Array Theorem) := do
  let (_,e) ← g.mkFreshProofGoal
  let keys ← Lean.Meta.RefinedDiscrTree.initializeLazyEntryWithEta e
  trace[Meta.Tactic.data_synth] "keys: {keys.map (·.1)}"
  getTheorems e


/-- Takes goal `e` solvable by `data_synth` and return `g : Goal`. Mainly, it replaces output
arguments with bound variables.

For example, it takes `HasFDerivAt ℝ f ?f' x` and returns `g : Goal` with `g.goal` being
`fun f' =>  HasFDerivAt ℝ f f' x` -/
def isDataSynthGoal? (e : Expr) : MetaM (Option Goal) := do
  let .some dataSynthDecl ← getDataSynth? e | return none

  let fn := e.getAppFn'
  let args := e.getAppArgs

  let mut outArgs := Array.replicate args.size false
  for i in dataSynthDecl.outputArgs do
    outArgs := outArgs.set! i true

  let e' ← go fn args.toList outArgs.toList #[]

  return some {
    -- instantiating mvars is important otherwise we can get different hashes for
    -- the same expression which breaks caching
    goal := ← instantiateMVars e'
    dataSynthName := dataSynthDecl.name
  }
where
  -- replaces out arguments in `e` with free variables
  go (fn : Expr) (args : List Expr) (outArgs : List Bool) (fvars : Array Expr) :=
    match args, outArgs with
    | a :: as, false :: os => go (fn.app a) as os fvars
    | a :: as, true :: os => do
      withLocalDeclD `x (← inferType a) fun var => do
        go (fn.app var) as os (fvars.push var)
    | [], _
    | _ , [] => mkLambdaFVars fvars fn

def Goal.assumption? (goal : Goal) : DataSynthM (Option Result) := do
  withProfileTrace "assumption?" do
  (← getLCtx).findDeclRevM? fun localDecl => do
    forallTelescope localDecl.type fun _xs type => do
    if localDecl.isImplementationDetail then
      return none
    else if type.isAppOf goal.dataSynthName then
      let (_,e) ← goal.mkFreshProofGoal
      let (ys, _, type') ← forallMetaTelescope localDecl.type
      if (← isDefEq e type') then
        trace[Meta.Tactic.data_synth] "using local hypothesis {localDecl.toExpr}"
        return ← goal.getResultFrom (mkAppN (.fvar localDecl.fvarId) ys)
      else
        return none
    else
      return none

def discharge? (e : Expr) : DataSynthM (Option Expr) := do
  (← read).disch e

def synthesizeAutoParam (x X : Expr) : DataSynthM Bool := do
  let .some (.const tacticDecl ..) := X.getAutoParamTactic?
    | return false
  let env ← getEnv
  match Lean.Elab.evalSyntaxConstant env (← getOptions) tacticDecl with
  | .error err       => throwError err
  | .ok tacticSyntax =>
    let X' := X.appFn!.appArg! -- extract the actual type from `autoParam _ _`
    let disch := Mathlib.Meta.FunProp.tacticToDischarge ⟨tacticSyntax⟩
    trace[Meta.Tactic.data_synth]
      "calling auto param tactic {tacticSyntax.prettyPrint} to prove {X'}"
    let some r ← disch X' | return false
    try
      x.mvarId!.assignIfDefEq r
      trace[Meta.Tactic.data_synth] "auto param success"
      return true
    catch _e =>
      trace[Meta.Tactic.data_synth] "auto param failed"
      return false

/-- Try to fill in `x` if it is metavariable. -/
def synthesizeArgument (x : Expr) : DataSynthM Bool := do
  let x ← instantiateMVars x
  let X ← inferType x

  -- skip if already synthesized
  unless x.isMVar do return true
  withProfileTrace "synthesizeArgument" do

  let b ← forallTelescope X fun ys X => do
    if let .some g ← isDataSynthGoal? X then
      -- call `data_synth` recursively
      if let .some r ← do dataSynth g then
        try
          x.mvarId!.assignIfDefEq (← mkLambdaFVars ys r.proof)
          return true
        catch e =>
          trace[Meta.Tactic.data_synth] m!"failed to assign {(← mkLambdaFVars ys r.proof)} to {x}"
          trace[Meta.Tactic.data_synth] e.toMessageData
          pure ()

    return false
  if b then return true

  -- type class synthesis
  if let .some _ ← isClass? X then
    try
      let inst ← synthInstance X
      x.mvarId!.assignIfDefEq inst
      return true
    catch _ =>
      pure ()

  -- try auto param
  if X.isAppOfArity' ``autoParam 2 then
    if ← synthesizeAutoParam x X then
      return true

  -- try assumptions
  if (← inferType X).isProp then
    try
      x.mvarId!.assumption
      return true
    catch _ =>
      pure ()

  -- try user defined discharger
  if (← inferType X).isProp then
    if let .some prf ← discharge? X then
      if ← isDefEq (← inferType prf) X then
        try
          x.mvarId!.assignIfDefEq prf
          return true
        catch _ =>
          trace[Meta.Tactic.data_synth] m!"failed to assign {prf} to {x}"
          pure ()

  return false

-- todo: move to batteries
private def getConstArgNames {m} [Monad m] [MonadEnv m] [MonadError m]
    (constName : Name) (fixAnonymousNames := false) : m (Array Name) := do
  let info ← getConstInfo constName
  return getArgNames info.type #[] 0
where
  getArgNames (e : Expr) (names : Array Name) (i : Nat) : Array Name :=
    match e with
    | .forallE name _ body _ =>
      if ¬fixAnonymousNames then
        getArgNames body (names.push name) i
      else
        if name.hasMacroScopes then
          getArgNames body (names.push (name.eraseMacroScopes.appendAfter (toString i))) (i+1)
        else
          getArgNames body (names.push name) i
    | _ => names

/- Apply theorem `thm` to solve `e`.

You can provide certain theorem arguments explicitelly with `hint` i.e. for `hint = #[(id₁,e₁),...]`
we assign `eᵢ` to `idᵢ`-th argument of theorem `thm`.

Hints `hintPre` are applied before unification of `e` with theorem statement and `hintPost` are
applied after unification. The main application if this is the theorem `HasFDerivAt.comp` where
we want to  provide `g` and `f` as `hintPre`. Only after unification the arguments `hg` and `hf`
have the right type, i.e. `g` and `f` are filled in,
 -/
def tryTheorem? (e : Expr) (thm : Theorem) (hintPre hintPost : Array (Nat × Expr) := #[]) :
    DataSynthM (Option Expr) := do

  withMainTrace
    (fun r => return m!"[{ExceptToEmoji.toEmoji r}] applying {← ppOrigin (.decl thm.thmName)}") do

  let thmProof ← thm.getProof
  let type ← inferType thmProof
  let (xs, _, type) ← forallMetaTelescope type
  let thmProof := thmProof.beta xs

  let argNames ← getConstArgNames thm.thmName
  let applyHints (hints : Array (Nat×Expr)) : DataSynthM Bool :=  do
    for (id, arg) in hints do
      let mvarId := xs[id]!.mvarId!
      if ¬(← mvarId.isAssigned) then
        try
          mvarId.assignIfDefEq arg
          trace[Meta.Tactic.data_synth] "setting {argNames[id]!} to {arg}"
        catch e =>
          trace[Meta.Tactic.data_synth] "failed to set {Expr.mvar mvarId} to {arg}"
          return false
    return true

  unless ← applyHints hintPre do return none

  unless (← isDefEq e type) do
    trace[Meta.Tactic.data_synth] "unification failed\n{e}\n=?=\n{type}"
    return none

  unless ← applyHints hintPost do return none

  -- todo: redo this, make a queue of all argument an try synthesize them over and over,
  --       until done or no progress
  -- try to synthesize all arguments
  for x in xs do
    let _ ← synthesizeArgument x

  -- check if all arguments have been synthesized
  for x in xs do
    let x ← instantiateMVars x
    if x.isMVar then
      logError m!"failed to synthesize argument {← inferType x} \
                  when applying {(← ppOrigin (.decl thm.thmName))}"
      trace[Meta.Tactic.data_synth] "failed to synthesize argument {x} : {← inferType x}"
      return none

  return some thmProof


def Goal.tryTheorem? (goal : Goal) (thm : Theorem) (hintPre hintPost : Array (Nat × Expr) := #[]) :
    DataSynthM (Option Result) := do
  withProfileTrace "tryTheorem" do

  let (xs, e) ← goal.mkFreshProofGoal

  let .some prf ← DataSynth.tryTheorem? e thm hintPre hintPost | return none

  let mut r := Result.mk (← xs.mapM instantiateMVars) (← instantiateMVars prf) goal

  r ← r.normalize

  return r


def Goal.getDataSynthDecl (g : Goal) : CoreM DataSynthDecl := do
  let ext := dataSynthDeclsExt.getState (← getEnv)
  let .some decl := ext.find? g.dataSynthName
    | throwError m!"invalid goal {g.goal}"
  return decl

-- main function that looks up theorems
partial def main (goal : Goal) : DataSynthM (Option Result) := do
  increaseStepOrThrow
  withProfileTrace "main" do

  let thms ← goal.getCandidateTheorems

  trace[Meta.Tactic.data_synth] "candidates {thms.map (fun t => t.thmName)}"
  if thms.size = 0 then
    logError m!"no candidate theorems for {← goal.pp}"

  -- try global theorems
  for thm in thms do
    if let .some r ← goal.tryTheorem? thm then
      return r

  -- try local hypothesis
  if let .some r ← goal.assumption? then
    return r

  -- try custom dispatch
  if let .some dispatch ← (← goal.getDataSynthDecl).getCustomDispatch then
    if let .some r ← dispatch goal then
      return r

  return none

def mainCached (goal : Goal) (initialTrace := true) :
    DataSynthM (Option Result) := do
  let go := do
    match (← get).cache[goal]? with
    | some r =>
      trace[Meta.Tactic.data_synth] "using cached result"
      return r
    | none =>
      if (← get).failedCache.contains goal then
        trace[Meta.Tactic.data_synth] "same goal failed previously"
        return none
      match ← main goal with
      | some r =>
        modify (fun s => {s with cache := s.cache.insert goal r})
        return r
      | none =>
        modify (fun s => {s with failedCache := s.failedCache.insert goal})
        return none

  if initialTrace then
    withMainTrace
      (fun r =>
        match r with
        | .ok (some _r) => return m!"[✅] {← goal.pp}"
        | .ok none => return m!"[❌] {← goal.pp}"
        | .error e => return m!"[💥️] {← goal.pp}\n{e.toMessageData}")
      do
        go
  else
    go

def dataSynthImpl (goal : Goal) : DataSynthM (Option Result) := do
  mainCached goal

initialize dataSynthRef.set dataSynthImpl

end Mathlib.Meta.DataSynth
