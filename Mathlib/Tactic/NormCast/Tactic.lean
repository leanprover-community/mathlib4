/-
Copyright (c) 2019 Paul-Nicolas Madelaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Nicolas Madelaine, Robert Y. Lewis, Mario Carneiro, Gabriel Ebner
-/

import Mathlib.Tactic.NormCast.Ext
import Mathlib.Tactic.OpenPrivate
import Mathlib.Tactic.SudoSetOption
import Mathlib.Util.Simp
import Mathlib.Algebra.Group.Defs

open Lean Meta Simp

namespace Tactic.NormCast

initialize registerTraceClass `Tactic.norm_cast

/-- Prove `a = b` using the given simp set. -/
def proveEqUsing (s : SimpTheorems) (a b : Expr) : MetaM (Option Simp.Result) := do
  let go : SimpM (Option Simp.Result) := do
    let methods := Simp.DefaultMethods.methods
    let a' ← Simp.simp a methods
    let b' ← Simp.simp b methods
    unless ← isDefEq a'.expr b'.expr do return none
    mkEqTrans a' (← mkEqSymm b b')
  withReducible do
    (go { simpTheorems := #[s], congrTheorems := ← Meta.getSimpCongrTheorems }).run' {}

/-- Prove `a = b` by simplifying using move and squash lemmas. -/
def proveEqUsingDown (a b : Expr) : MetaM (Option Simp.Result) := do
  trace[Tactic.norm_cast] "proving: {← mkEq a b}"
  proveEqUsing (← normCastExt.down.getTheorems) a b

def mkCoe (e : Expr) (ty : Expr) : MetaM Expr := do
  let eType ← inferType e
  let u ← getLevel eType
  let v ← getLevel ty
  let coeTInstType := mkAppN (mkConst ``CoeT [u, v]) #[eType, e, ty]
  let inst ← synthInstance coeTInstType
  expandCoe <| mkAppN (mkConst ``CoeT.coe [u, v]) #[eType, e, ty, inst]

def isCoeOf? (e : Expr) : MetaM (Option Expr) := do
  if let Expr.const fn .. := e.getAppFn then
    if let some info ← getCoeFnInfo? fn then
      if e.getAppNumArgs == info.numArgs then
        return e.getArg! info.coercee
  return none

def isNumeral? (e : Expr) : Option (Expr × Nat) :=
  if e.isConstOf ``Nat.zero then
    (mkConst ``Nat, 0)
  else if let Expr.app (Expr.app (Expr.app (Expr.const ``OfNat.ofNat ..) α ..)
      (Expr.lit (Literal.natVal n) ..) ..) .. := e then
    some (α, n)
  else
    none

/--
This is the main heuristic used alongside the elim and move lemmas.
The goal is to help casts move past operators by adding intermediate casts.
An expression of the shape: op (↑(x : α) : γ) (↑(y : β) : γ)
is rewritten to:            op (↑(↑(x : α) : β) : γ) (↑(y : β) : γ)
when (↑(↑(x : α) : β) : γ) = (↑(x : α) : γ) can be proven with a squash lemma
-/
def splittingProcedure (expr : Expr) : MetaM Simp.Result := do
  let Expr.app (Expr.app op x ..) y .. := expr | return {expr := expr}

  let Expr.forallE _ γ (Expr.forallE _ γ' ty ..) .. ← inferType op | return {expr := expr}
  if γ'.hasLooseBVars || ty.hasLooseBVars then return {expr := expr}
  unless ← isDefEq γ γ' do return {expr := expr}

  try
    let some x' ← isCoeOf? x | failure
    let some y' ← isCoeOf? y | failure
    let α ← inferType x'
    let β ← inferType y'

    -- TODO: fast timeout
    (try
      let x2 ← mkCoe (← mkCoe x' β) γ
      let some x_x2 ← proveEqUsingDown x x2 | failure
      Simp.mkCongrFun (← Simp.mkCongr {expr := op} x_x2) y
    catch _ =>
      let y2 ← mkCoe (← mkCoe y' α) γ
      let some y_y2 ← proveEqUsingDown y y2 | failure
      Simp.mkCongr {expr := mkApp op x} y_y2)
  catch _ => try
    let some (β, n) := isNumeral? y | failure
    let some x' ← isCoeOf? x | failure
    let α ← inferType x'
    let y2 ← mkCoe (← mkNumeral α n) γ
    let some y_y2 ← proveEqUsingDown y y2 | failure
    Simp.mkCongr {expr := mkApp op x} y_y2
  catch _ => try
    let some (α, n) := isNumeral? x | failure
    let some y' ← isCoeOf? y | failure
    let β ← inferType y'
    let x2 ← mkCoe (← mkNumeral β n) γ
    let some x_x2 ← proveEqUsingDown x x2 | failure
    Simp.mkCongrFun (← Simp.mkCongr {expr := op} x_x2) y
  catch _ =>
    return {expr := expr}

/--
Discharging function used during simplification in the "squash" step.

TODO: normCast takes a list of expressions to use as lemmas for the discharger
TODO: a tactic to print the results the discharger fails to proove
-/
def prove (e : Expr) : SimpM (Option Expr) := do
  trace[Tactic.norm_cast] "discharging {e}"
  return (← findLocalDeclWithType? e).map mkFVar

/--
Core rewriting function used in the "squash" step, which moves casts upwards
and eliminates them.

It tries to rewrite an expression using the elim and move lemmas.
On failure, it calls the splitting procedure heuristic.
-/
partial def upwardAndElim (up : SimpTheorems) (e : Expr) : SimpM Simp.Step := do
  let r ← Simp.rewrite? e up.post up.erased prove (tag := "squash") (rflOnly := false)
  let r := r.getD { expr := e }
  let r ← mkEqTrans r <|← splittingProcedure r.expr
  if r.expr == e then return Simp.Step.done {expr := e}
  return Simp.Step.visit r

/--
If possible, rewrite `(n : α)` to `(Nat.cast n : α)` where `n` is a numeral and `α ≠ ℕ`.
Returns a pair of the new expression and proof that they are equal.
-/
def numeralToCoe (e : Expr) : MetaM Simp.Result := do
  let some (α, n) := isNumeral? e | failure
  if (← whnf α).isConstOf ``Nat then failure
  let newE ← mkAppOptM ``Nat.cast #[α, none, toExpr n]
  let some pr ← proveEqUsingDown e newE | failure
  return pr

/--
The core simplification routine of `normCast`.
-/
def derive (e : Expr) : MetaM Simp.Result := do
  let e ← instantiateMVars e

  let config : Simp.Config := {
    zeta := false
    beta := false
    eta  := false
    proj := false
    iota := false
  }
  let congrTheorems ← Meta.getSimpCongrTheorems

  let r := {expr := e}

  trace[Tactic.norm_cast] "before: {r.expr}"

  -- step 1: pre-processing of numerals
  let r ← mkEqTrans r <|<- Simp.main r.expr { config := config, congrTheorems }
    { post := fun e => return Simp.Step.done (← try numeralToCoe e catch _ => pure {expr := e}) }
  trace[Tactic.norm_cast] "after numeralToCoe: {r.expr}"

  -- step 2: casts are moved upwards and eliminated
  let r ← mkEqTrans r <|<- Simp.main r.expr { config := config, congrTheorems }
    { post := upwardAndElim (← normCastExt.up.getTheorems) }
  trace[Tactic.norm_cast] "after upwardAndElim: {r.expr}"

  -- step 3: casts are squashed
  let r ← mkEqTrans r <|<- simp r.expr {
    simpTheorems := #[← normCastExt.squash.getTheorems]
    config, congrTheorems
  }
  trace[Tactic.norm_cast] "after squashing: {r.expr}"

  return r

open Elab.Term in
elab "mod_cast " e:term : term <= expectedType => do
  if (← instantiateMVars expectedType).hasExprMVar then tryPostpone
  let expectedType' ← derive expectedType
  let e ← elabTerm e expectedType'.expr
  synthesizeSyntheticMVars
  let eTy ← instantiateMVars (← inferType e)
  if eTy.hasExprMVar then tryPostpone
  let eTy' ← derive eTy
  unless ← isDefEq eTy'.expr expectedType'.expr do
    throwTypeMismatchError "mod_cast" expectedType'.expr eTy'.expr e
  let eTy_eq_expectedType ← mkEqTrans eTy' (← mkEqSymm expectedType expectedType')
  mkCast eTy_eq_expectedType e

open Tactic Parser.Tactic Elab.Tactic

def normCastTarget : TacticM Unit :=
  liftMetaTactic1 fun mvarId => do
    let tgt ← instantiateMVars (← getMVarType mvarId)
    let prf ← derive tgt
    applySimpResultToTarget mvarId tgt prf

def normCastHyp (fvarId : FVarId) : TacticM Unit :=
  liftMetaTactic1 fun mvarId => do
    let hyp ← instantiateMVars (← getLocalDecl fvarId).type
    let prf ← derive hyp
    return (← applySimpResultToLocalDecl mvarId fvarId prf false).map (·.snd)

elab "norm_cast0" loc:((ppSpace location)?) : tactic =>
  withMainContext do
    match expandOptLocation loc with
    | Location.targets hyps target =>
      if target then normCastTarget
      (← getFVarIds hyps).forM normCastHyp
    | Location.wildcard =>
      normCastTarget
      (← getNondepPropHyps (← getMainGoal)).forM normCastHyp

/-- `assumption_mod_cast` runs `norm_cast` on the goal. For each local hypothesis `h`, it also
normalizes `h` and tries to use that to close the goal. -/
macro "assumption_mod_cast" : tactic => `(norm_cast0 at * <;> assumption)

/--
Normalize casts at the given locations by moving them "upwards".
-/
macro "norm_cast" loc:(ppSpace location)? : tactic =>
  `(tactic| norm_cast0 $[$loc:location]? <;> try trivial)

/--
Rewrite with the given rules and normalize casts between steps.
-/
syntax "rw_mod_cast" (config)? rwRuleSeq (ppSpace location)? : tactic
macro_rules
  | `(tactic|rw_mod_cast $[$config:config]? [$rules,*] $[$loc:location]?) => do
    let tacs ← rules.getElems.mapM fun rule =>
      `(tactic| norm_cast at *; rw $[$config]? [$rule] $[$loc:location]?)
    `(tactic| ($[$tacs:tactic]*))

/--
Normalize the goal and the given expression, then close the goal with exact.
-/
macro "exact_mod_cast " e:term : tactic => `(exact mod_cast ($e : _))

/--
Normalize the goal and the given expression, then apply the expression to the goal.
-/
macro "apply_mod_cast " e:term : tactic => `(apply mod_cast ($e : _))

syntax (name := convNormCast) "norm_cast" : conv
@[tactic convNormCast] def evalConvNormCast : Tactic :=
  open Elab.Tactic.Conv in fun stx => withMainContext do
    applySimpResult (← derive (← getLhs))

syntax (name := pushCast) "push_cast " (config)? (discharger)? (&"only ")? ("[" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic
@[tactic pushCast] def evalPushCast : Tactic := fun stx => do
  let { ctx := ctx, fvarIdToLemmaId, dischargeWrapper } ← withMainContext do
    mkSimpContext' (← pushCastExt.getTheorems) stx (eraseLocal := false)
  dischargeWrapper.with fun discharge? =>
    simpLocation ctx discharge? fvarIdToLemmaId (expandOptLocation stx[5])

-- add_hint_tactic "norm_cast at *"

/-
The `norm_cast` family of tactics is used to normalize casts inside expressions.
It is basically a simp tactic with a specific set of lemmas to move casts
upwards in the expression.
Therefore it can be used more safely as a non-terminating tactic.
It also has special handling of numerals.

For instance, given an assumption
```lean
a b : ℤ
h : ↑a + ↑b < (10 : ℚ)
```

writing `norm_cast at h` will turn `h` into
```lean
h : a + b < 10
```

You can also use `exact_mod_cast`, `apply_mod_cast`, `rw_mod_cast`
or `assumption_mod_cast`.
Writing `exact_mod_cast h` and `apply_mod_cast h` will normalize the goal and
`h` before using `exact h` or `apply h`.
Writing `assumption_mod_cast` will normalize the goal and for every
expression `h` in the context it will try to normalize `h` and use
`exact h`.
`rw_mod_cast` acts like the `rw` tactic but it applies `norm_cast` between steps.

`push_cast` rewrites the expression to move casts toward the leaf nodes.
This uses `norm_cast` lemmas in the forward direction.
For example, `↑(a + b)` will be written to `↑a + ↑b`.
It is equivalent to `simp only with push_cast`.
It can also be used at hypotheses with `push_cast at h`
and with extra simp lemmas with `push_cast [int.add_zero]`.

```lean
example (a b : ℕ) (h1 : ((a + b : ℕ) : ℤ) = 10) (h2 : ((a + b + 0 : ℕ) : ℤ) = 10) :
  ((a + b : ℕ) : ℤ) = 10 :=
begin
  push_cast,
  push_cast at h1,
  push_cast [int.add_zero] at h2,
end
```

The implementation and behavior of the `norm_cast` family is described in detail at
<https://lean-forward.github.io/norm_cast/norm_cast.pdf>.
-/
-- add_tactic_doc
-- { name := "norm_cast",
--   category   := doc_category.tactic,
--   decl_names := [``tactic.interactive.norm_cast, ``tactic.interactive.rw_mod_cast,
--                  ``tactic.interactive.apply_mod_cast, ``tactic.interactive.assumption_mod_cast,
--                  ``tactic.interactive.exact_mod_cast, ``tactic.interactive.push_cast],
--   tags       := ["coercions", "simplification"] }
-- TODO
