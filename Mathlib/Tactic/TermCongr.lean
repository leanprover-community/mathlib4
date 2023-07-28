/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
--import Mathlib.Lean.Expr.Traverse
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

private def congrPfKey : Name := decl_name%
private def congrLhsKey : Name := decl_name%
private def congrRhsKey : Name := decl_name%
private def congrIsLhsKey : Name := decl_name%

/-- Given a proposition, returns `(tyLhs, lhs, tyRhs, rhs)` if it's an eq, iff, or heq. -/
def sides? (ty : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let ty ← whnf ty
  if let some (lhs, rhs) := ty.iff? then
    return some (.sort .zero, lhs, .sort .zero, rhs)
  if let some (ty, lhs, rhs) := ty.eq? then
    return (ty, lhs, ty, rhs)
  else if let some (tyLhs, lhs, tyRhs, rhs) := ty.heq? then
    return (tyLhs, lhs, tyRhs, rhs)
  else
    return none

/-- Create the congruence hole. Used by `elabCHole`. -/
def mkCHole (forLhs : Bool) (lhs rhs pf : MVarId) : Expr :=
  let e := Expr.mvar (if forLhs then lhs else rhs)
  let d : MData := KVMap.empty
    |>.insert congrPfKey pf.name
    |>.insert congrLhsKey lhs.name
    |>.insert congrRhsKey rhs.name
    |>.insert congrIsLhsKey forLhs
  Expr.mdata d e

/-- Return a fresh metavariable that is immediately assigned to the value `val`. This is used to be
able to store expressions as metadata. -/
def mkPseudoMVar (val : Expr) (type? : Option Expr := none) : MetaM MVarId := do
  let type ← if let some type := type? then pure type else inferType val
  let mvar := (← Meta.mkFreshExprMVar type).mvarId!
  mvar.assign val
  return mvar

/-- Elaborates a congruence hole and returns either the left-hand side or the right-hand side,
annotated with information necessary to generate a congruence lemma. -/
def elabCHole (h : Syntax) (forLhs : Bool) : Term.TermElabM Expr := do
  let h' ← Term.elabTerm h none
  let pf ← mkPseudoMVar h'
  if let some (tyLhs, lhs, tyRhs, rhs) ← sides? (← pf.getType) then
    let lhs' ← mkPseudoMVar lhs tyLhs
    let rhs' ← mkPseudoMVar rhs tyRhs
    return mkCHole forLhs lhs' rhs' pf
  else
    let lhs := (← Meta.mkFreshExprMVar none).mvarId!
    let rhs := (← Meta.mkFreshExprMVar none).mvarId!
    return mkCHole forLhs lhs rhs pf

/-- If the expression is a congruence hole, returns `(forLhs, lhs, rhs, pf)`. -/
def cHole? (e : Expr) : Option (Bool × Expr × Expr × Expr) := do
  match e with
  | .mdata d _ =>
    let pf ← d.getName congrPfKey
    let lhs ← d.getName congrLhsKey
    let rhs ← d.getName congrRhsKey
    let forLhs ← d.getBool congrIsLhsKey
    return (forLhs, .mvar ⟨lhs⟩, .mvar ⟨rhs⟩, .mvar ⟨pf⟩)
  | _ => none

/-- If the expression is a recent congruence hole, returns `(forLhs, lhs, rhs, pf)`.
Does `cHole?` but then makes sure that the metavariable is recent.  -/
def cHole?' (ctx : MetavarContext) (mvarCounterSaved : Nat) (e : Expr) :
    Option (Bool × Expr × Expr × Expr) := do
  if let some r@(_, _, _, pf) := cHole? e then
    if mvarCounterSaved ≤ (ctx.getDecl pf.mvarId!).index then
      return r
  none

/-- Returns a subexpression that's a congruence hole that's recent.  -/
def hasCHole (mvarCounterSaved : Nat) (e : Expr) : MetaM (Option Expr) := do
  let mctx ← getMCtx
  return e.find? fun e' => (cHole?' mctx mvarCounterSaved e').isSome

/-- (Internal for `congr(...)`)
Elaborates to an expression satisfying `cHole?` that equals the LHS of `h`. -/
elab (name := cLhsExpand) "c_lhs% " h:term : term => elabCHole h true

/-- (Internal for `congr(...)`)
Elaborates to an expression satisfying `cHole?` that equals the LHS of `h`. -/
elab (name := cRhsExpand) "c_rhs% " h:term : term => elabCHole h false

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

/-- Given a `congr(...)` pattern `t`, elaborate it for the given side,
ensuring it's of the expected type. -/
def elaboratePattern (t : Term) (expectedType : Expr) (forLhs : Bool) : Term.TermElabM Expr :=
  Term.withoutErrToSorry do
    let t' ← processAntiquot t (fun h => if forLhs then `(c_lhs% $h) else `(c_rhs% $h))
    Term.elabTermEnsuringType t' expectedType

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

/-- A congruence lemma between two expressions. -/
structure CongrResult where
  (lhs rhs : Expr)
  /-- A proof somehow relates `lhs` to `rhs` (by `Iff`, `Eq`, or `HEq`).
  If `none`, then the proof is the appropriate notion of reflexivity. -/
  (pf? : Option Expr)

def CongrResult.assertLhsDefeq (res : CongrResult) (lhs pfTy : Expr) : MetaM Unit := do
  unless ← isDefEq res.lhs lhs do
    throwError "Left-hand side of congruence lemma is{indentD res.lhs}\n{""
      }and is not definitionally equal to left-hand side of congruence hole, which has type{""
      }{indentD pfTy}"

def CongrResult.assertRhsDefeq (res : CongrResult) (rhs pfTy : Expr) : MetaM Unit := do
  unless ← isDefEq res.rhs rhs do
    throwError "Right-hand side of congruence lemma is{indentD res.rhs}\n{""
      }and is not definitionally equal to right-hand side of congruence hole, which has type{""
      }{indentD pfTy}"

/-- Returns the proof that `lhs = rhs`.

If `pf? = none`, this returns the `rfl` proof. If `lhs` and `rhs` are not syntactically equal, then
uses `mkExpectedTypeHint`. -/
def CongrResult.eq (res : CongrResult) : MetaM Expr := do
  unless ← isDefEq (← inferType res.lhs) (← inferType res.rhs) do
    throwError "Expecting{indentD res.lhs}\nand{indentD res.rhs}\n{""
      }to have definitionally equal types."
  match res.pf? with
  | some pf =>
    -- TODO handle coercions
    let ty ← whnf (← inferType pf)
    if let some (_, lhs, _, rhs) ← sides? ty then
      res.assertLhsDefeq lhs ty
      res.assertRhsDefeq rhs ty
    if let some .. := ty.iff? then
      mkPropExt pf
    else if let some .. := ty.eq? then
      return pf
    else if let some (lhsTy, _, rhsTy, _) := ty.heq? then
      unless ← isDefEq lhsTy rhsTy do
        throwError "Cannot turn congruence hole into an equality. Has type{indentD ty}"
      mkAppM ``eq_of_heq #[pf]
    else
      return pf
  | none =>
    let pf ← mkEqRefl res.rhs
    if res.lhs == res.rhs then
      return pf
    else
      mkExpectedTypeHint pf (← mkEq res.lhs res.rhs)

/-- Force the lhs and rhs to be defeq. For `dsimp`-like congruence. -/
def CongrResult.defeq (res : CongrResult) : MetaM CongrResult := do
  unless ← isDefEq res.lhs res.rhs do
    throwError "congr(...) failed, {""
      }left-hand side{indentD res.lhs}\nis not definitionally equal to{indentD res.rhs}"
  return res

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
def throwCongrEx (lhs rhs : Expr) (msg : MessageData) : MetaM α := do
  throwError "congr(...) failed with left-hand side{indentD lhs}\n{""
    }and right-hand side {indentD rhs}\n{msg}"

/-- If `lhs` or `rhs` is a congruence hole, then process it.
Only process ones that are at least as new as `mvarCounterSaved` since there's nothing
preventing congruence holes from leaking into the context. -/
def mkCongrOfCHole? (mvarCounterSaved : Nat) (lhs rhs : Expr) : MetaM (Option CongrResult) := do
  match ← cHole?' mvarCounterSaved lhs, ← cHole?' mvarCounterSaved rhs with
  | some (_, lhs1, rhs1, pf1), some (_, lhs2, rhs2, pf2) =>
    -- Defeq checks to unify the lhs and rhs congruence holes.
    unless ← isDefEq lhs1 lhs2 do
      throwCongrEx lhs rhs "Elaborated left-hand sides of congruence holes are not defeq."
    unless ← isDefEq rhs1 rhs2 do
      throwCongrEx lhs rhs "Elaborated right-hand sides of congruence holes are not defeq."
    unless ← isDefEq (← inferType pf1) (← inferType pf2) do
      throwCongrEx lhs rhs "Elaborated types of congruence holes are not defeq."
    return some {lhs := lhs1, rhs := rhs1, pf? := pf1}
  | some .., none =>
    throwCongrEx lhs rhs "Right-hand side lost its congruence hole annotation."
  | none, some .. =>
    throwCongrEx lhs rhs "Left-hand side lost its congruence hole annotation."
  | none, none => return none

/-- Walks along `lhs` and `rhs` simultaneously to create a congruence lemma between them.
Assumes all metavariables are instantiated. -/
def mkCongrOf (mvarCounterSaved : Nat) (lhs rhs : Expr) : MetaM CongrResult := do
  if let some res ← mkCongrOfCHole? mvarCounterSaved lhs rhs then
    return res
  match lhs, rhs with
  | .app .., .app .. =>
    let arity := lhs.getAppNumArgs
    unless arity == rhs.getAppNumArgs do
      throwCongrEx lhs rhs "Each side has a different number of arguments."
    let f := lhs.getAppFn
    unless ← isDefEq (← inferType f) (← inferType rhs.getAppFn) do
      throwCongrEx lhs rhs "Functions in each application have non-defeq types."
    --let (f, args) := lhs.getAppNumArgs
    let arity := mkHCongrWithArity
    failure
  -- lam forallE letE
  | .mdata _ lhs', .mdata _ rhs' =>
    let res ← mkCongrOf mvarCounterSaved lhs' rhs'
    return {res with lhs := lhs, rhs := rhs}
  | .proj n1 i1 e1, .proj n2 i2 e2 =>
    unless n1 == n2 && i1 == i2 do
      throwCongrEx lhs rhs "Incompatible primitive projections"
    let res ← mkCongrOf mvarCounterSaved e1 e2
    res.defeq
    return {lhs := lhs, rhs := rhs, pf? := none}
  | _, _ => mkCongrOfDefeq lhs rhs

@[term_elab termCongr]
def elabTermCongr : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(congr($t)) =>
    -- Save the current mvarCounter so that we can tell which cHoles are for this congr quotation.
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let (expEq, expTy, expLhs, expRhs) ← mkEqForExpectedType expectedType?
    let lhs ← elaboratePattern t expTy true
    let rhs ← elaboratePattern t expTy false
    unless ← isDefEq expLhs lhs do
      throwError "Left-hand side{indentD lhs}\n{""
        }is not definitionally equal to left-hand side of{indentD expEq}"
    unless ← isDefEq expRhs rhs do
      throwError "Right-hand side{indentD rhs}\n{""
        }is not definitionally equal to right-hand side of{indentD expEq}"
    Term.synthesizeSyntheticMVars (mayPostpone := true)
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    let res ← mkCongrOf mvarCounterSaved lhs rhs
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
