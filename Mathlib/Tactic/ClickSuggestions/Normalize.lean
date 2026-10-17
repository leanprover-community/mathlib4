/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public meta import Lean.Elab.Tactic.NormCast
public import Mathlib.Tactic.ClickSuggestions.Util
public import Mathlib.Tactic.Widget.Conv
public import Mathlib.Util.AtomM
public import Mathlib.Tactic.Push

/-!
# Normalizing tactics in `#click_suggestions`

This file implements an extensible mechanism for suggesting normalization tactics,
given by the function `suggestNormTactics`.

We implement special built-in behaviour for `dsimp only`/`dsimp`/`simp` and for
`push Not`/`push +distrib Not`, to avoid duplicates when these normalize to the same expression.

This file implements suggestions for `dsimp`, `simp`, `push`, `norm_cast` and `push_cast`.
Downstream files add extensions for e.g. `norm_num`, `ring_nf` and `field_simp`.
-/

meta section

namespace Mathlib.Tactic.ClickSuggestions.Normalize

open Lean Meta ProofWidgets Jsx

/-- The information that a normalizing tactic needs for where to apply. -/
public structure PositionInfo where
  /-- At the goal or a hypothesis. -/
  hyp? : Option Name
  /-- At which subexpression. -/
  convPath? : Option Conv.Path

/-- A `NormStx` stores the syntax for a normalization tactic. -/
public structure NormStx where
  /-- The `tactic` syntax. -/
  tacStx : Option (TSyntax ``Parser.Tactic.location) → CoreM (TSyntax `tactic)
  /-- The `conv` syntax. -/
  convStx : OptionT CoreM (TSyntax `conv)

/-- `NormTactic` stores the information needed for suggesting a normalizing tactic. -/
public structure NormTactic extends NormStx where
  /-- Normalize the given expression, throwing an error if the tactic doesn't apply. -/
  run : Expr → MetaM Expr

/--
Given that some normalization tactic changes `old` to `new`, return the suggestion for this tactic.
Note that some tactics have no `conv` analogue, so in that case we
default to suggesting the usual version of the tactic.
-/
def suggestNormalize (old new : Expr) (info : PositionInfo) (stx : NormStx) :
    ClickSuggestionsM (Option Html) := do
  if ← isExplicitEq old new then return none
  let tac ← match ← stx.convStx.run, info.convPath? with
    | some convStx, some path => Conv.pathToStx convStx path info.hyp?
    | _, _ => stx.tacStx (← info.hyp?.mapM fun hyp ↦
      `(Lean.Parser.Tactic.location| at $(mkIdent hyp):ident))
  let mut html ← exprToHtml new
  let solves := info.convPath?.isNone &&
    (info.hyp?.isNone && new.isTrue || info.hyp?.isSome && new.isFalse)
  if solves then
    addSolvingSuggestion tac
  let button := (← PrettyPrinter.ppTactic (← stx.tacStx none)).pretty
  mkSuggestion tac button html (solves := solves)

section Cast

/-- The entry for `norm_cast` in `#click_suggestions`. -/
public def normCast : NormTactic where
  run e := return (← Lean.Elab.Tactic.NormCast.derive e).1
  tacStx loc? := `(tactic| norm_cast $[$loc?]?)
  convStx := `(conv| norm_cast)

/-- The entry for `push_cast` in `#click_suggestions`. -/
public def pushCast : NormTactic where
  run e := do
    let ctx ← Simp.mkContext
      (simpTheorems := #[← NormCast.pushCastExt.getTheorems])
      (congrTheorems := ← getSimpCongrTheorems)
    return (← Lean.Meta.simp e ctx).1.expr
  tacStx loc? := `(tactic| push_cast $[$loc?:location]?)
  -- There is no `conv` version of `push_cast`.
  convStx := failure

end Cast

section Push

/-- Return the tactic syntax for `push`. -/
def pushStx (head : Push.Head) (distrib : Bool) : NormStx :=
  let cfg :=
    if distrib then `(Parser.Tactic.optConfig| +$(mkIdent `distrib))
    else `(Parser.Tactic.optConfig|)
  let head :=
    match head with
    | .lambda => `(fun _ ↦ _)
    | .forall => `(∀ _, _)
    | .const ``Membership.mem => `(_ ∈ _)
    | .const c => return mkIdent (← unresolveNameGlobal c)
  {
    tacStx loc? := do `(tactic| push $(← cfg) $(← head):term $[$loc?:location]?)
    convStx := do `(conv| push $(← cfg) $(← head):term)
  }

/-- Run `push head`. -/
def runPush (head : Push.Head) (distrib : Bool) (e : Expr) : MetaM Expr := do
  return (← Push.pushCore head { distrib } none e).expr

/-- Get the head of expression `e` for use in the `push` tactic. -/
def getHead (e : Expr) : Option Push.Head :=
  match e.getAppFn with
  | .forallE .. => some .forall
  | .lam .. => some .lambda
  | .const c _ => some (.const c)
  | _ => none

/-- Create a suggestion for `push` using the head constant of `e`.
If the constant is `Not`, then also suggest `push +distrib Not` if that does something different.
-/
public def suggestPush (e : Expr) (info : PositionInfo)
  (update : Html → ClickSuggestionsM Unit) : ClickSuggestionsM Unit := do
  let some head := getHead (← whnfR e) | return
  if let .const headConst := head then
    -- Make sure that there are actually push theorems for this constant, otherwise return.
    let thms := Push.pushExt.getState (← getEnv)
    try
      thms.root.forM fun key _ ↦ do if let .const c _ := key then if c == headConst then failure
      return
    catch _ => pure ()
  let e₁ ← runPush head false e
  if let some html ← suggestNormalize e e₁ info (pushStx head false) then
    update html
    if head matches .const ``Not then
      -- Also suggest `push +distrib Not` if it behaves differently from `push Not`.
      let e₂ ← runPush head true e
      if let some html ← suggestNormalize e₁ e₂ info (pushStx head true) then
        update html

end Push

section Simp

def dsimpOnlyStx : NormStx where
  tacStx loc? := `(tactic| dsimp only $[$loc?]?)
  convStx := `(conv| dsimp only)

def dsimpStx : NormStx where
  tacStx loc? := `(tactic| dsimp $[$loc?:location]?)
  convStx := `(conv| dsimp)

def simpStx : NormStx where
  tacStx loc? := `(tactic| simp $[$loc?:location]?)
  convStx := `(conv| simp)


/-- Run `dsimp only`. -/
def runDSimpOnly (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext (congrTheorems := ← getSimpCongrTheorems)
  return (← Lean.Meta.dsimp e ctx).1

/-- Run `dsimp`. -/
def runDSimp (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext
    (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← Lean.Meta.dsimp e ctx #[← Simp.getSimprocs]).1

/-- Run `simp`. -/
def runSimp (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext
    (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← Lean.Meta.simp e ctx #[← Simp.getSimprocs]).1.expr

/-- Create suggestions for `dsimp only`, `dsimp` and/or `simp`.
Only suggest a tactic if it gives a different result from the previous one.
-/
public def suggestSimp (e : Expr) (info : PositionInfo)
    (update : Html → ClickSuggestionsM Unit) : ClickSuggestionsM Unit := do
  let e₁ ← runDSimpOnly e
  if let some html ← suggestNormalize e e₁ info dsimpOnlyStx then
    update html
  let e₂ ← runDSimp e
  if let some html ← suggestNormalize e₁ e₂ info dsimpStx then
    update html
  let e₃ ← runSimp e
  if let some html ← suggestNormalize e₂ e₃ info simpStx then
    update html

end Simp

/-- An `IO.Ref` for normalization tactics in `#click_suggestions`. -/
public initialize normTacticRef : IO.Ref (Array NormTactic) ← IO.mkRef #[normCast, pushCast]

/-- Create a suggestion for tactics that normalize the selected expression.
The suggestions are shown incrementally, so they show up as soon as they are computed.
We currently use one thread for these, but we might parallelize it in the future.
-/
public def suggestNormTactics (e rootExpr : Expr) (fvarId? : Option FVarId) (pos : SubExpr.Pos) :
    ClickSuggestionsM Html :=
  mkIncrementalSuggestions "Normalization" fun update ↦ withNewMCtxDepth do
    let info : PositionInfo := {
      hyp? := ← fvarId?.mapM (·.getUserName)
      convPath? := ← if pos.isRoot then pure none else some <$> Conv.Path.ofSubExprPos rootExpr pos
    }
    suggestPush e info update
    suggestSimp e info update
    for tac in ← normTacticRef.get do
      let e' ← try tac.run e catch _ => continue
      if let some html ← suggestNormalize e e' info tac.toNormStx then
        update html

section Algebra

/-- Run a tactic like `ring_nf` or `abel_nf`. -/
public def runNF (e : Expr) (evalExpr : Expr → AtomM Simp.Result)
    (cleanup : Simp.Result → MetaM Simp.Result) : MetaM Expr := do
  let expr ← AtomM.run .reducible do
    if let mkApp2 rel lhs rhs := e then
      if rel.isAppOfArity ``Eq 1 || rel.isAppOfArity ``LE.le 2 || rel.isAppOfArity ``LT.lt 2 then
        -- Allow `evalExpr` to fail on at most one of `lhs` and `rhs`.
        let (lhs, rhs) ←
          try
            let lhs := (← evalExpr lhs).expr
            let rhs ← try pure (← evalExpr rhs).expr catch _ => pure rhs
            pure (lhs, rhs)
          catch _ =>
            pure (lhs, (← evalExpr rhs).expr)
        if ← isDefEq lhs rhs then
          if rel.isAppOfArity ``LT.lt 2 then
            return .const ``False []
          else
            return .const ``True []
        return mkApp2 rel lhs rhs
    return (← evalExpr e).expr
  return (← cleanup { expr }).expr

/-- Simplify `e` using normalization tactic `tac`, such as `group` or `noncomm_ring`. -/
public def runFromStx (tac : TSyntax `tactic) (e : Expr) : MetaM Expr := do
  let e' ← mkFreshExprMVar (← inferType e)
  let mvar ← mkFreshExprMVar (← mkAppM ``Eq #[e, e'])
  let [mvarId] ← (Elab.Tactic.run mvar.mvarId! (Elab.Tactic.evalTactic tac)).run' | failure
  _ ← mvarId.applyConst ``rfl
  instantiateMVars e'

/-- Check that `e` is suitable for normalization by a tactic for class `cls`.
This is used for unstructured normalization tactics such as `group` and `noncomm_ring`. -/
public def involvesClass (e : Expr) (cls : Name) : MetaM Bool := do
  let type ← match_expr e with
    | Eq α _ _ => pure α
    | LE.le α _ _ _ => pure α
    | LT.lt α _ _ _ => pure α
    | _ => inferType e
  return (← trySynthInstance (← mkAppM cls #[type])) matches .some _

end Algebra

end Mathlib.Tactic.ClickSuggestions.Normalize
