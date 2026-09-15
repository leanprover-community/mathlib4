/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.Util
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Push
public meta import Lean.Elab.Tactic.NormCast

/-!
# Normalizing tactics in `#click_suggestions`

This file implement the following suggestions for normalizing tactics:
- `suggestNormCast`: `norm_cast`, `push_cast`
- `suggestPush`: `push _`/`push +distrib Not`
- `suggestSimp`: `dsimp only`/`dsimp`/`simp`/`norm_num`
- `suggestAlgebraicNormalization`: `field_simp`, `ring_nf`/`noncomm_ring`/`abel`/`group`
-/

meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta ProofWidgets Jsx Mathlib.Tactic Mathlib.Meta

/-- The information that a normalizing tactic needs for where to apply. -/
public structure RewritingInfo where
  /-- At the goal or a hypothesis. -/
  hyp? : Option Name
  /-- At which subexpression. -/
  convPath? : Option Conv.Path

/-- A `NormStx` stores the syntax for a normalization tactic. -/
structure NormStx where
  /-- The `tactic` syntax. -/
  tac : Option Ident → CoreM (TSyntax `tactic)
  /-- The `conv` syntax. -/
  conv : OptionT CoreM (TSyntax `conv)

/--
Given that some normalization tactic changes `old` to `new`, return the suggestion for this tactic.
Note that some tactics have no `conv` analogue, so in that case we
default to suggesting the usual version of the tactic.
-/
def suggestNormalize (old new : Expr) (info : RewritingInfo) (stx : NormStx) :
    ClickSuggestionsM (Option Html) := do
  if ← isExplicitEq old new then return none
  let tac ← match ← stx.conv.run, info.convPath? with
    | some convStx, some path => Conv.pathToStx convStx path info.hyp?
    | _, _ => stx.tac (info.hyp?.map mkIdent)
  let mut html ← exprToHtml new
  if info.convPath?.isNone then
    if info.hyp?.isNone && new.isTrue || info.hyp?.isSome && new.isFalse then
      -- The goal is `True` or a hypothesis is `False`, so we are happy.
      html := <span> {html} {.text " 🎉"} </span>
  mkTacticSuggestion tac (← stx.tac none) html

section Cast

def normCastStx : NormStx where
  tac hyp? := `(tactic| norm_cast $[at $hyp?:ident]?)
  conv     := `(conv| norm_cast)

-- There is no `conv` version of `push_cast`.
def pushCastStx : NormStx where
  tac hyp? := `(tactic| push_cast $[at $hyp?:ident]?)
  conv     := failure

/-- Run `norm_cast`. -/
def runNormCast (e : Expr) : MetaM Expr := do
  return (← Lean.Elab.Tactic.NormCast.derive e).1

/-- Run `push_cast`. -/
def runPushCast (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext
    (simpTheorems := #[← NormCast.pushCastExt.getTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← Lean.Meta.simp e ctx).1.expr

/-- Create a suggestion for `norm_cast` and/or `push_cast`. -/
public def suggestNormCast (e : Expr) (info : RewritingInfo) : ClickSuggestionsM Html :=
  mkIncrementalSuggestions "cast" fun update ↦ do
    let e' ← runNormCast e
    if let some html ← suggestNormalize e e' info normCastStx then
      update html
    let e' ← runPushCast e
    if let some html ← suggestNormalize e e' info pushCastStx then
      update html

end Cast

section Push

/-- Return the tactic syntax for `push head`. -/
def pushStx (head : Push.Head) (distrib : Bool) : NormStx :=
  let cfg := do
    if distrib then `(Parser.Tactic.optConfig| +$(mkIdent `distrib))
    else `(Parser.Tactic.optConfig| )
  let head := do
    match head with
    | .lambda => `(fun _ ↦ _)
    | .forall => `(∀ _, _)
    | .const ``Membership.mem => `(_ ∈ _)
    | .const c => pure <| mkIdent (← unresolveNameGlobal c)
  {
    tac hyp? := do `(tactic| push $(← cfg) $(← head):term $[at $hyp?:ident]?)
    conv     := do `(conv| push $(← cfg) $(← head):term)
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

/-- Create a suggestion for `push`. -/
public def suggestPush (e : Expr) (info : RewritingInfo) : ClickSuggestionsM Html := do
  let some head := getHead (← whnfR e) | return .text ""
  let thms := Push.pushExt.getState (← getEnv)
  if let .const headConst := head then
    -- Make sure that there are actually push theorems for this constant, otherwise return.
    try
      thms.root.forM fun | .const c _, _ => do if c == headConst then failure | _, _ => pure ()
      return .text ""
    catch _ => pure ()
  mkIncrementalSuggestions "push" fun update ↦ do
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
  tac hyp? := `(tactic| dsimp only $[at $hyp?:ident]?)
  conv     := `(conv| dsimp only)

def dsimpStx : NormStx where
  tac hyp? := `(tactic| dsimp $[at $hyp?:ident]?)
  conv     := `(conv| dsimp)

def simpStx : NormStx where
  tac hyp? := `(tactic| simp $[at $hyp?:ident]?)
  conv     := `(conv| simp)

def normNumStx : NormStx where
  tac hyp? := `(tactic| norm_num $[at $hyp?:ident]?)
  conv     := `(conv| norm_num)

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

/-- Run `norm_num`. -/
def runNormNum (e : Expr) : MetaM Expr := do
  let ctx ← Simp.mkContext
    (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← NormNum.deriveSimp ctx #[← Simp.getSimprocs] (e := e)).expr

/-- Create suggestions for `dsimp only`, `dsimp`, `simp`, `norm_num`.
We only suggest a tactic if it gives a different result compared to the previous result.
-/
public def suggestSimp (e : Expr) (info : RewritingInfo) : ClickSuggestionsM Html :=
  mkIncrementalSuggestions "simp" fun update ↦ do
    let e₁ ← runDSimpOnly e
    if let some html ← suggestNormalize e e₁ info dsimpOnlyStx then
      update html
    let e₂ ← runDSimp e
    if let some html ← suggestNormalize e₁ e₂ info dsimpStx then
      update html
    let e₃ ← runSimp e
    if let some html ← suggestNormalize e₂ e₃ info simpStx then
      update html
    let e₄ ← runNormNum e
    if let some html ← suggestNormalize e₃ e₄ info normNumStx then
      update html

end Simp

section Algebra

def ringNFStx : NormStx where
  tac hyp? := `(tactic| ring_nf $[at $hyp?:ident]?)
  conv     := `(conv| ring_nf)

def abelNFStx : NormStx where
  tac hyp? := `(tactic| abel_nf $[at $hyp?:ident]?)
  conv     := `(conv| abel_nf)

def fieldSimpStx : NormStx where
  tac hyp? := `(tactic| field_simp $[at $hyp?:ident]?)
  conv     := `(conv| field_simp)

-- `group` doesn't have a `conv` version.
def groupStx : NormStx where
  tac hyp? := `(tactic| group $[at $hyp?:ident]?)
  conv     := failure

 -- `noncomm_ring` doesn't even have an `at h` version.
def noncommRingStx : NormStx where
  tac _ := `(tactic| noncomm_ring)
  conv     := failure

open RingNF in
/-- Run `ring_nf`. -/
def runRing (e : Expr) (ineq? : Option Mathlib.Ineq) : MetaM Expr := do
  let expr ← AtomM.run .reducible do
    if let some ineq := ineq? then
      let mkApp2 rel lhs rhs := e | failure
      let lhs := (← evalExpr lhs).expr; let rhs := (← evalExpr rhs).expr
      if ← isDefEq lhs rhs then
        match ineq with
        | .eq | .le => return mkConst ``True
        | .lt => return mkConst ``False
      return mkApp2 rel lhs rhs
    else
      return (← evalExpr e).expr
  return (← cleanup {} { expr }).expr

open Abel in
/-- Run `abel_nf`. -/
def runAbel (e : Expr) (ineq? : Option Mathlib.Ineq) : MetaM Expr := do
  let expr ← AtomM.run .reducible do
    if let some ineq := ineq? then
      let mkApp2 rel lhs rhs := e | failure
      let lhs := (← evalExpr lhs).expr; let rhs := (← evalExpr rhs).expr
      if ← isDefEq lhs rhs then
        match ineq with
        | .eq | .le => return mkConst ``True
        | .lt => return mkConst ``False
      return mkApp2 rel lhs rhs
    else
      return (← evalExpr e).expr
  return (← cleanup {} { expr }).expr

/-- Run `field_simp`. -/
def runField (e : Expr) (isProp : Bool) : MetaM Expr := AtomM.run .reducible do
  let ctx ← Simp.mkContext
    (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let disch := fun e ↦ Prod.fst <$> (FieldSimp.discharge e).run ctx >>= Option.getM
  if isProp then
    return (← FieldSimp.reduceProp disch e).expr
  else
    return (← FieldSimp.reduceExpr disch e).expr

/-- Run the given tactic `stx`. -/
private def tryTactic (stx : TSyntax `tactic) (e : Expr) : MetaM Expr := do
  let mvar ← mkFreshExprMVar e
  match ← (Elab.Tactic.run mvar.mvarId! (Elab.Tactic.evalTactic stx)).run' with
  | [] => return mkConst ``True
  | [mvarId] => mvarId.getType
  | _ => failure

/-- Run `group`. -/
def runGroup (e : Expr) : MetaM Expr := do tryTactic (← `(tactic| group)) e

/-- Run `noncomm_ring`. -/
def runNoncommRing (e : Expr) : MetaM Expr := do tryTactic (← `(tactic| noncomm_ring)) e

/-- Check if `e` is a target for algebraic simplification.
If so, return the type in which the operations take place, and optionally the relation. -/
def isAlgebraic (e : Expr) : MetaM (Option (Expr × Option Mathlib.Ineq)) := do
  if (← whnfR e).getAppFn.constName matches
    ``HAdd.hAdd | ``Add.add |
    ``HMul.hMul | ``Mul.mul |
    ``HSMul.hSMul | ``SMul.smul |
    ``HPow.hPow | ``Pow.pow |
    ``Neg.neg |
    ``HSub.hSub | ``Sub.sub |
    ``Inv.inv |
    ``HDiv.hDiv | ``Div.div then
    return some (← inferType e, none)
  try
    let (kind, α, _, _) ← e.ineq?
    return some (α, some kind)
  catch _ =>
    return none

/--
Create a suggestion for an algebraic normalization tactic.

We suggest `field_simp` when applicable, and additionally we suggest at most one of
`ring`, `noncomm_ring`, `abel` and `group`, depending on which type class is satisfied.

There are 2 cases where we may suggest this
1. The selected expression is an algebraic expression.
2. The selected expression is an equality or inequality of algebraic expressions.
-/
public def suggestAlgebraicNormalization (e : Expr) (info : RewritingInfo) :
    ClickSuggestionsM Html := do
  let some (type, ineq?) ← isAlgebraic e | return .text ""
  mkIncrementalSuggestions "algebra" fun update ↦ do
    if let some e' ← try? <| runField e ineq?.isSome then
      if let some html ← suggestNormalize e e' info fieldSimpStx then
        update html
    if let some e' ← try? <| runRing e ineq? then
      if let some html ← suggestNormalize e e' info ringNFStx then
        update html
    else if let .some _ ← trySynthInstance (← mkAppM ``NonAssocSemiring #[type]) then
      if ineq?.isSome then
        if let some e' ← try? <| runNoncommRing e then
          if let some html ← suggestNormalize e e' info noncommRingStx then
            update html
    else if let some e' ← try? <| runAbel e ineq? then
      if let some html ← suggestNormalize e e' info abelNFStx then
        update html
    else if let .some _ ← trySynthInstance (← mkAppM ``Group #[type]) then
      if ineq?.isSome then
        if let some e' ← try? <| runGroup e then
          if let some html ← suggestNormalize e e' info groupStx then
            update html

end Algebra

end Mathlib.Tactic.ClickSuggestions
