/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
import Mathlib.Lean.Meta.Simp

/-! # `congr(...)` term elaborator

This module defines a term elaborator for generating congruence lemmas according to a pattern.
Rather than using `congr_arg` or `congr_fun`, one can write `congr($hf $hx)` with
`hf : f = f'` and `hx : x = x'` to get `f x = f' x'`. This is also more general, since
`f` could have implicit arguments and complicated dependent types.
-/

namespace Mathlib.Tactic.TermCongr
open Lean Elab Meta

initialize registerTraceClass `Tactic.congr

/--
`congr(expr)` generates an congruence where `expr` is an expression containing
congruence holes of the form `$h`. In these congruence holes, `h : a = b` indicates
that, in the generated congruence, on the left-hand side `a` is substituted for `$h`
and on the right-hand side `b` is substituted for `$h`.

For example, if `h : a = b` then `congr(1 + $h) : 1 + a = 1 + b`.
-/
syntax (name := termCongr) "congr(" withoutForbidden(ppDedentIfGrouped(term)) ")" : term

#check Lean.Syntax.antiquotKind?

/-- Extracts the LHS of an equality while holding onto the equality for later use.
The antiquotations in `congr(...)` are replaced by this during elaboration of `congr(...)`. -/
@[reducible] def c_lhs {α : Sort _} {x y : α} (_ : x = y) : α := x

/-- Extracts the RHS of an equality while holding onto the equality for later use.
The antiquotations in `congr(...)` are replaced by this during elaboration of `congr(...)`. -/
@[reducible] def c_rhs {α : Sort _} {x y : α} (_ : x = y) : α := y

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

@[term_elab cLhsExpand, term_elab cRhsExpand]
def elabCongrCExpand : Term.TermElab := fun stx expectedType? => do
  let e ← match stx with
    | `(c_lhs% $e) => Term.elabTerm (← `(c_lhs (ensure_eq% $e))) expectedType?
    | `(c_rhs% $e) => Term.elabTerm (← `(c_rhs (ensure_eq% $e))) expectedType?
    | _ => throwUnsupportedSyntax
  return mkAnnotation decl_name% e

/-- Gives the un-annotated expression for expressions elaborated by `c_lhs%` or `c_rhs%`.
Returns `(α, x : α, y : α, h : x = y)` -/
def congrCExpand? (e : Expr) : Option (Expr × Expr × Expr × Expr) := do
  let e ← annotation? ``elabCongrCExpand e
  let .app (.app (.app (.app _ ty) x) y) h := e | failure
  return (ty, x, y, h)

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

/-- Create the LHS by replacing all antiquotes with `congr_c_expand%` expressions.

Use `c_lhs` to store the equalities in the terms. Makes sure to annotate the
terms to ensure that if `$h` is used as a function, we still sees `c_lhs`
as being a four-argument function. -/
def processAntiquot (t : Term) : Term.TermElabM Term := do
  let left ← t.raw.replaceM fun s => do
    if s.isAntiquots then
      let ks := s.antiquotKinds
      unless ks.any (fun (k, _) => k == `term) do
        throwErrorAt s "Expecting term"
      let h : Term := ⟨s.getCanonicalAntiquot.getAntiquotTerm⟩
      `(congr_c_expand% $h)
    else
      pure none
  return ⟨left⟩

def elaboratePattern (t : Term) (expectedType : Expr) : Term.TermElabM Term := do
  let left ← processAntiquot t
  let left' ← left.raw.replaceM fun
    | `(congr_c_expand% $h) => ``(eq_lhs% $h)
    | _ => pure none
  let right' ← left.raw.replaceM fun
    | `(congr_c_expand% $h) => ``(eq_rhs% $h)
    | _ => pure none

@[term_elab termCongr]
def elabTermCongr : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(congr($t)) =>
    let (expEq, expTy, _) ← mkEqForExpectedType expectedType?
    let left ← processAntiquot t
    let preLeft ← Term.withoutErrToSorry do
      try
        Term.elabTermEnsuringType left expTy
      catch ex =>
        -- Failed, so let's re-elaborate with LHS's to get a better error message.
        let left ← t.raw.replaceM fun
          | `(congr_c_expand% $h) => ``(eq_lhs% $h)
          | _ => pure none
        discard <| Term.elabTermEnsuringType left expTy
        -- That should fail, but if it didn't we at least can throw the original exception:
        throw ex
    Term.synthesizeSyntheticMVarsUsingDefault
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
