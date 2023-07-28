/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
--import Mathlib.Lean.Meta.Simp

/-! # `congr(...)` congruence quotations

This module defines a term elaborator for generating congruence lemmas by writing patterns
using quotation-like syntax.
One can write `congr($hf $hx)` with `hf : f = f'` and `hx : x = x'` to get `f x = f' x'`.
While in simple cases it might be possible to use `congr_arg` or `congr_fun`,
congruence quotations are more general,
since `f` could have implicit arguments and complicated dependent types.
-/

namespace Mathlib.Tactic.TermCongr
open Lean Elab Meta

initialize registerTraceClass `Tactic.congr

/--
`congr(expr)` generates an congruence where `expr` is an expression containing
congruence holes of the form `$h` or `$(h)`.
In these congruence holes, `h : a = b` indicates that, in the generated congruence,
on the left-hand side `a` is substituted for `$h`
and on the right-hand side `b` is substituted for `$h`.

For example, if `h : a = b` then `congr(1 + $h) : 1 + a = 1 + b`.
-/
syntax (name := termCongr) "congr(" withoutForbidden(ppDedentIfGrouped(term)) ")" : term

/-- Extracts the LHS of an equality while holding onto the equality for later use.
The antiquotations in `congr(...)` are replaced by this during elaboration of `congr(...)`. -/
@[reducible] def c_lhs {α : Sort _} {x y : α} (_ : x = y) : α := x

/-- Extracts the RHS of an equality while holding onto the equality for later use.
The antiquotations in `congr(...)` are replaced by this during elaboration of `congr(...)`. -/
@[reducible] def c_rhs {α : Sort _} {x y : α} (_ : x = y) : α := y

/-- Returns an application of `c_lhs` or `c_rhs`. Used to make sure everything has been
properly accounted for in congruence generation (none should remain). -/
def findCFn? (e : Expr) : Option Expr := e.find? fun e => e.isAppOf ``c_lhs || e.isAppOf ``c_rhs

/-- Ensures the expected type is an equality. Returns the equality along with the type
of the terms being equated, the lhs, and the rhs. -/
private def mkEqForExpectedType (expectedType? : Option Expr) :
    Term.TermElabM (Expr × Expr × Expr × Expr) := do
  let ty ← Meta.mkFreshTypeMVar
  let a ← Meta.mkFreshExprMVar ty
  let b ← Meta.mkFreshExprMVar ty
  let eq ← Meta.mkEq a b
  if let some expectedType := expectedType? then
    unless ← Meta.isDefEq expectedType eq do
      throwError m!"Term {← Meta.mkHasTypeButIsExpectedMsg eq expectedType}"
  return (eq, ty, a, b)

/-- `ensure_eq% h` ensures that `h : x = y`. If `h : x ↔ y` then uses `propext`. -/
syntax (name := ensureEq) "ensure_eq% " term : term

@[term_elab ensureEq]
def elabEnsureEq : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(ensure_eq% $eStx) =>
    let (eq, _) ← mkEqForExpectedType expectedType?
    let mut e ← Term.elabTerm eStx none
    if let some .. := (← whnfR (← inferType e)).iff? then
      e ← mkPropExt e
    Term.ensureHasType eq e
  | _ => throwUnsupportedSyntax

/-- (Internal for `congr(...)`)
Helper to expand antiquotations into `c_lhs` expressions. Produces an annotated term
to ensure `c_lhs` is always regarded as having exactly four arguments. -/
syntax (name := cLhsExpand) "c_lhs% " term : term

/-- (Internal for `congr(...)`)
Helper to expand antiquotations into `c_rhs` expressions. Produces an annotated term
to ensure `c_rhs` is always regarded as having exactly four arguments. -/
syntax (name := cRhsExpand) "c_rhs% " term : term

/-- Gives the un-annotated expression for expressions elaborated by `c_lhs%` or `c_rhs%`.
Returns `(isLhs, α, x : α, y : α, h : x = y)` -/
def cFn? (e : Expr) : Option (Bool × Expr × Expr × Expr × Expr) := do
  let e ← annotation? ``cLhsExpand e
  let .app (.app (.app (.app (.const n ..) ty) x) y) h := e | failure
  return (n == ``c_lhs, ty, x, y, h)

/-- Remove all `c_lhs%` and `c_rhs%` nodes, replacing them with their lhs or rhs. -/
def removeCFns (e : Expr) : Expr := e.replace fun e' =>
  if let some (isLhs, _, x, y, _) := cFn? e' then
    if isLhs then x else y
  else
    none

/-- (Internal for `congr(...)`)
Helper to remove any `c_lhs%` and `c_rhs%` nodes from the expected type. -/
syntax (name := withoutCFns) "without_expected_c_fns% " term : term

def

@[term_elab cLhsExpand, term_elab cRhsExpand]
def elabCExpand : Term.TermElab := fun stx expectedType? => do
  let e ← match stx with
    | `(c_lhs% $e) => Term.elabTerm (← `(c_lhs (ensure_eq% $e))) expectedType?
    | `(c_rhs% $e) => Term.elabTerm (← `(c_rhs (ensure_eq% $e))) expectedType?
    | _ => throwUnsupportedSyntax
  return mkAnnotation ``cLhsExpand e



/-- Elaborates to the LHS of the type of an equality proof. -/
syntax (name := eq_lhs_term) "eq_lhs% " term:max : term

/-- Elaborates to the RHS of the type of an equality proof. -/
syntax (name := eq_rhs_term) "eq_rhs% " term:max : term

@[term_elab eq_lhs_term, term_elab eq_rhs_term]
def elabEqLhsRhsTerm : Term.TermElab := fun stx expectedType? => do
  let (isLhs, term) ← match stx with
    | `(eq_lhs% $t) => pure (true, t)
    | `(eq_rhs% $t) => pure (false, t)
    | _ => throwUnsupportedSyntax
  let (eq, _, lhs, rhs) ← mkEqForExpectedType expectedType?
  discard <| Term.elabTermEnsuringType term eq
  return if isLhs then lhs else rhs

/-- Replace all `term` antiquotations in a term using the `expand` function. -/
def processAntiquot (t : Term) (expand : Term → Term.TermElabM Term) : Term.TermElabM Term := do
  let t' ← t.raw.replaceM fun s => do
    if s.isAntiquots then
      let ks := s.antiquotKinds
      unless ks.any (fun (k, _) => k == `term) do
        throwErrorAt s "Expecting term"
      let h : Term := ⟨s.getCanonicalAntiquot.getAntiquotTerm⟩
      expand h
    else
      pure none
  return ⟨t'⟩

def elaboratePattern (t : Term) (expectedType : Expr) (forLhs : Bool) : Term.TermElabM Expr :=
  Term.withoutErrToSorry do
    let t' ← processAntiquot t (fun h => if forLhs then `(c_lhs% $h) else `(c_rhs% $h))
    let x ← Term.observing <| Term.elabTermEnsuringType t' expectedType
    if x matches .ok .. then
      Term.applyResult x
    else
      -- Failed, so let's re-elaborate with the actual LHS/RHS to get a better error message.
      let t'' ← processAntiquot t (fun h => if forLhs then `(eq_lhs% $h) else `(eq_rhs% $h))
      discard <| Term.elabTermEnsuringType t'' expectedType
      -- That should fail, but if it didn't we at least can throw the original exception:
      Term.applyResult x

/-- A congruence lemma between two expressions. -/
structure CongrResult where
  (lhs rhs : Expr)
  /-- A proof that `lhs = rhs`. If `none`, then the proof is `rfl`. -/
  (pf? : Option Expr)

/-- Returns the proof that `lhs = rhs`.

If `pf? = none`, this returns the `rfl` proof. If `lhs` and `rhs` are not syntactically equal, then
uses `mkExpectedTypeHint`. -/
def CongrResult.pf (res : CongrResult) : MetaM Expr := do
  match res.pf? with
  | some pf => return pf
  | none =>
    let pf ← mkEqRefl res.rhs
    if res.lhs == res.rhs then
      return pf
    else
      mkExpectedTypeHint pf (← mkEq res.lhs res.rhs)

/-- Ensures `lhs` and `rhs` are defeq without proof irrelevance.
Turning off proof irrelevance means it can solve for proof metavariables. -/
def ensureDefeq (lhs rhs : Expr) : MetaM Unit := do
  unless ← withoutProofIrrelevance <| isDefEq lhs rhs do
    throwError "congr(...) failed, {""
      }left-hand side{indentD lhs}\nis not definitionally equal to{indentD rhs}"

/-- Checks that `lhs` and `rhs` are defeq, returning a `rfl` congruence. -/
def mkCongrOfDefeq (lhs rhs : Expr) : MetaM CongrResult := do
  ensureDefeq lhs rhs
  return {lhs, rhs, pf? := none}

/-- Throw an internal error. -/
def throwCongrEx (lhs rhs : Expr) (msg : MessageData) : MetaM Unit := do
  throwError "congr(...) failed with left-hand side{indentD lhs}\n{""
    }and right-hand side {indentD rhs}\n{msg}"

/-- If `lhs` or `rhs` is a  -/
def handleCongrCExpand? (lhs rhs : Expr) : MetaM (Option CongrResult) := do
  if let some (ty, x, y, h) := congrCExpand? lhs then
    if let some (ty', x', y', h') := congrCExpand? rhs then

/-- Walks along `lhs` and `rhs` simultaneously to create a congruence lemma between them.
Assumes all metavariables are instantiated.

The `lhs` can contain annotated `c_lhs` expressions and the `rhs` can contain annotated
`c_rhs` expressions. These must occur simultaneously. -/
def mkCongrOf (lhs rhs : Expr) : MetaM CongrResult := do
  if let some (ty, x, y, h) := congrCExpand? lhs then
    if let some (ty', x', y', h') := congrCExpand? rhs then
      failure
    else
      throwCongrEx lhs rhs "Right-hand side lost "
  match lhs, rhs with
  | .mvar .., _
  | _, _ => mkCongrOfDefeq lhs rhs

@[term_elab termCongr]
def elabTermCongr : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(congr($t)) =>
    let (expEq, expTy, _) ← mkEqForExpectedType expectedType?
    let lhs ← elaboratePattern t expTy true
    let rhs ← elaboratePattern t expTy false
    --Term.synthesizeSyntheticMVarsUsingDefault
    trace[Tactic.congr] "preLeft = {preLeft}"
    trace[Tactic.congr] "raw preLeft = {toString preLeft}"
    -- Unfold the `c_lhs` terms and remove annotations to get the true LHS
    let left := preLeft.replace (fun e =>
      if let some (_α, lhs, _rhs, _eq) := e.app4? ``c_lhs then lhs else none)
    let left := left.replace congrCExpand?
    trace[Tactic.congr] "left = {left}"
    -- Rewrite the `c_lhs` terms to get the RHS. `c_lhs` is reducible, which makes using
    -- a simp lemma not work reliably, so using a pre-transform instead.
    let simpCtx : Simp.Context :=
      { config := Simp.neutralConfig,
        simpTheorems := #[]
        congrTheorems := (← getSimpCongrTheorems) }
    let preTrans (e : Expr) : SimpM Simp.Step := do
      if let some (_α, _lhs, rhs, eq) := e.app4? ``c_lhs then
        return .visit {expr := rhs, proof? := eq}
      else
        return .visit {expr := e}
    let (res, _) ← Simp.main preLeft simpCtx (methods := { pre := preTrans })
    -- Remove the annotations
    let right := res.expr.replace congrCExpand?
    trace[Tactic.congr] "right = {right}"
    -- Make sure there are no `c_lhs` expressions remaining in the term
    if right.find? (·.isConstOf ``c_lhs) matches some .. then
      throwError m!"Could not rewrite all occurrences of c(..) holes. There are still `c_lhs`{
        ""} expressions in{indentExpr right}"
    -- Check the expected type
    let eq' ← mkEq left right
    unless ← Meta.isDefEq eq' expEq do
      throwError m!"Generated congruence {← Meta.mkHasTypeButIsExpectedMsg eq' expEq}"
    -- Create a type hint to lock in the `c_lhs`-free version of the equality.
    mkExpectedTypeHint (← res.getProof) eq'
  | _ => throwUnsupportedSyntax
