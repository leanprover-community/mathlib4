/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
import Mathlib.Logic.Basic
--import Mathlib.Tactic.Congr!
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

/-- Return a fresh metavariable that is immediately assigned to the value `val`. This is for
being able to store expressions as metadata. -/
def mkPseudoMVar (val : Expr) (type? : Option Expr := none) : MetaM MVarId := do
  let type ← if let some type := type? then pure type else inferType val
  let mvar := (← mkFreshExprMVar type).mvarId!
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
    let lhs := (← mkFreshExprMVar none).mvarId!
    let rhs := (← mkFreshExprMVar none).mvarId!
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
Does `cHole?` but makes sure that the metavariable is recent.  -/
def cHole?' (ctx : MetavarContext) (mvarCounterSaved : Nat) (e : Expr) :
    Option (Bool × Expr × Expr × Expr) := do
  if let some r@(_, _, _, pf) := cHole? e then
    if mvarCounterSaved ≤ (ctx.getDecl pf.mvarId!).index then
      return r
  none

/-- Returns any subexpression that is a recent congruence hole.  -/
def hasCHole (mvarCounterSaved : Nat) (e : Expr) : MetaM (Option Expr) := do
  let mctx ← getMCtx
  return e.find? fun e' => (cHole?' mctx mvarCounterSaved e').isSome

/-- (Internal for `congr(...)`)
Elaborates to an expression satisfying `cHole?` that equals the LHS of `h`. -/
elab (name := cLhsExpand) "c_lhs% " h:term : term => elabCHole h true

/-- (Internal for `congr(...)`)
Elaborates to an expression satisfying `cHole?` that equals the LHS of `h`. -/
elab (name := cRhsExpand) "c_rhs% " h:term : term => elabCHole h false

/-- Replace all `term` antiquotations in a term using the given `expand` function. -/
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

/-- Ensures the expected type is an equality. Returns the equality.
This expression is suitable for `Lean.Expr.eq?`. -/
def mkEqForExpectedType (expectedType? : Option Expr) : MetaM Expr := do
  let ty ← mkFreshTypeMVar
  let a ← mkFreshExprMVar ty
  let b ← mkFreshExprMVar ty
  let eq ← mkEq a b
  if let some expectedType := expectedType? then
    unless ← isDefEq expectedType eq do
      throwError m!"Term {← mkHasTypeButIsExpectedMsg eq expectedType}"
  return eq

/-- Ensures the expected type is a HEq. Returns the HEq.
This expression is suitable for `Lean.Expr.heq?`. -/
def mkHEqForExpectedType (expectedType? : Option Expr) : MetaM Expr := do
  let a ← mkFreshExprMVar none
  let b ← mkFreshExprMVar none
  let heq ← mkHEq a b
  if let some expectedType := expectedType? then
    unless ← isDefEq expectedType heq do
      throwError m!"Term {← mkHasTypeButIsExpectedMsg heq expectedType}"
  return heq

-- /-- Ensures the expected type is an iff. Returns the iff along with the lhs and the rhs. -/
-- def mkIffForExpectedType (expectedType? : Option Expr) :
--     MetaM (Expr × Expr × Expr × Expr) := do
--   let a ← mkFreshExprMVar (Expr.sort .zero)
--   let b ← mkFreshExprMVar (Expr.sort .zero)
--   let iff := mkApp2 (.const ``Iff []) a b
--   if let some expectedType := expectedType? then
--     unless ← isDefEq expectedType iff do
--       throwError m!"Term {← mkHasTypeButIsExpectedMsg iff expectedType}"
--   return (eq, ty, a, b)

/-- A congruence lemma between two expressions.
The expressions can be related by `Iff`, `Eq`, or `HEq`.
The given proof can be a proof of any of these relations. -/
structure CongrResult where
  (lhs rhs : Expr)
  /-- A proof somehow relates `lhs` to `rhs` (by `Iff`, `Eq`, or `HEq`).
  If `none`, then the proof is the appropriate notion of reflexivity
  and `lhs` and `rhs` are defeq. -/
  (pf? : Option Expr)

def CongrResult.isRfl (res : CongrResult) : Bool := res.pf?.isNone

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

/-- Given a `pf` of an `Iff`, `Eq`, or `HEq`, return a proof of `Eq`.
If `pf` is not obviously any of these, unify its type with `Eq`, but if `prop` is true
then insert `propext` so that the goal is an `Iff`. -/
def toEqPf (pf : Expr) (prop : Bool) : MetaM Expr:= do
  let ty ← whnf (← inferType pf)
  if let some .. := ty.iff? then
    mkPropExt pf
  else if let some .. := ty.eq? then
    return pf
  else if let some (lhsTy, _, rhsTy, _) := ty.heq? then
    unless ← isDefEq lhsTy rhsTy do
      throwError "Cannot turn HEq proof into an equality. Has type{indentD ty}"
    mkAppM ``eq_of_heq #[pf]
  else
    let pf ← if prop then mkPropExt pf else pure pf
    let ty ← mkEqForExpectedType (← inferType pf)
    -- Ensure the type is obviously an equality.
    mkExpectedTypeHint pf ty

/-- Given a `pf` of an `Iff`, `Eq`, or `HEq`, return a proof of `HEq`.
If `pf` is not obviously any of these, unify its type with `HEq`, but try making
it be an `Eq` if possible, and in this case if `prop` is true insert a `propext` so
that the goal is an `Iff`. -/
def toHEqPf (pf : Expr) (tryEq : Bool) (prop : Bool) : MetaM Expr := do
  let ty ← whnf (← inferType pf)
  if let some .. := ty.iff? then
    mkAppM ``heq_of_eq #[← mkPropExt pf]
  else if let some .. := ty.eq? then
    mkAppM ``heq_of_eq #[pf]
  else if let some .. := ty.heq? then
    return pf
  else
    let pf ← if tryEq then mkAppM ``heq_of_eq #[← toEqPf pf prop] else pure pf
    let ty ← mkHEqForExpectedType (← inferType pf)
    -- Ensure the type is obviously a HEq.
    mkExpectedTypeHint pf ty

/-- Returns the proof that `lhs = rhs`. Fails if the `CongrResult` is inapplicable.

If `pf? = none`, this returns the `rfl` proof. If `lhs` and `rhs` are not syntactically equal, then
uses `mkExpectedTypeHint`. -/
def CongrResult.eq (res : CongrResult) : MetaM Expr := do
  unless ← isDefEq (← inferType res.lhs) (← inferType res.rhs) do
    throwError "Expecting{indentD res.lhs}\nand{indentD res.rhs}\n{""
      }to have definitionally equal types."
  match res.pf? with
  | some pf =>
    let pf ← toEqPf pf (prop := ← Meta.isProp res.lhs)
    let some (_, lhs, rhs) := (← whnf <| ← inferType pf).eq? | unreachable!
    -- TODO handle coercions when `res` is for an equality of types?
    res.assertLhsDefeq lhs (← inferType pf)
    res.assertRhsDefeq rhs (← inferType pf)
    return pf
  | none =>
    -- Then `isDefEq res.lhs res.rhs`
    let pf ← mkEqRefl res.lhs
    if res.lhs == res.rhs then
      return pf
    else
      mkExpectedTypeHint pf (← mkEq res.lhs res.rhs)

/-- Returns the proof that `HEq lhs rhs`. Fails if the `CongrResult` is inapplicable.

If `pf? = none`, this returns the `rfl` proof. If `lhs` and `rhs` are not syntactically equal, then
uses `mkExpectedTypeHint`. -/
def CongrResult.heq (res : CongrResult) : MetaM Expr := do
  match res.pf? with
  | some pf =>
    let pf ← toHEqPf pf
              (tryEq := ← withNewMCtxDepth <| isDefEq (← inferType res.lhs) (← inferType res.rhs))
              (prop := ← Meta.isProp res.lhs)
    let some (_, lhs, _, rhs) := (← whnf <| ← inferType pf).heq? | unreachable!
    res.assertLhsDefeq lhs (← inferType pf)
    res.assertRhsDefeq rhs (← inferType pf)
    return pf
  | none =>
    -- Then `isDefEq res.lhs res.rhs`
    let pf ← mkHEqRefl res.lhs
    if res.lhs == res.rhs then
      return pf
    else
      mkExpectedTypeHint pf (← mkHEq res.lhs res.rhs)

/-- Ensures `lhs` and `rhs` are defeq. -/
def ensureDefeq (lhs rhs : Expr) : MetaM Unit := do
  unless ← isDefEq lhs rhs do
    throwError "congr(...) failed, {""
      }left-hand side{indentD lhs}\nis not definitionally equal to{indentD rhs}"

/-- Checks that `lhs` and `rhs` are defeq, returning a `rfl` congruence.

If that fails, tries to synthesize a proof using `Subsingleton.elim`. -/
def mkCongrOfDefeq (lhs rhs : Expr) : MetaM CongrResult := do
  if ← isDefEq lhs rhs then
    return {lhs, rhs, pf? := none}
  let res? ← observing? do
    -- Note: `mkAppM` uses `withNewMCtxDepth`, which we depend on to prevent specialization.
    let pf ← mkAppM ``Subsingleton.elim #[lhs, rhs]
    return {lhs, rhs, pf? := pf}
  if let some res := res? then
    return res
  else
    throwError "congr(...) failed, {""
      }left-hand side{indentD lhs}\nis not definitionally equal to{indentD rhs}"

/-- Force the lhs and rhs to be defeq. For `dsimp`-like congruence. Clears the proof. -/
def CongrResult.defeq (res : CongrResult) : MetaM CongrResult := do
  if res.pf?.isSome then
    ensureDefeq res.lhs res.rhs
    -- Propagate types into proof that we're dropping:
    discard <| res.eq
  return {res with pf? := none}

/-- Throw an internal error. -/
def throwCongrEx (lhs rhs : Expr) (msg : MessageData) : MetaM α := do
  throwError "congr(...) failed with left-hand side{indentD lhs}\n{""
    }and right-hand side {indentD rhs}\n{msg}"

/-- If `lhs` or `rhs` is a congruence hole, then process it.
Only process ones that are at least as new as `mvarCounterSaved` since there's nothing
preventing congruence holes from leaking into the context. -/
def mkCongrOfCHole? (mvarCounterSaved : Nat) (lhs rhs : Expr) : MetaM (Option CongrResult) := do
  let mctx ← getMCtx
  match cHole?' mctx mvarCounterSaved lhs, cHole?' mctx mvarCounterSaved rhs with
  | some (_, lhs1, rhs1, pf1), some (_, lhs2, rhs2, pf2) =>
    trace[Tactic.congr] "mkCongrOfCHole, both holes"
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

/-- Walks along both `lhs` and `rhs` simultaneously to create a congruence lemma between them.
Assumes all metavariables are instantiated. -/
partial def mkCongrOf (depth : Nat) (mvarCounterSaved : Nat) (lhs rhs : Expr) :
    MetaM CongrResult := do
  trace[Tactic.congr] "mkCongrOf: {depth}, {lhs}, {rhs}, {(← mkFreshExprMVar none).mvarId!}"
  if depth > 100 then
    throwError "out of gas"
  if let some res ← mkCongrOfCHole? mvarCounterSaved lhs rhs then
    trace[Tactic.congr] "hole"
    return res
  match lhs, rhs with
  | .app .., .app .. =>
    trace[Tactic.congr] "app"
    let arity := lhs.getAppNumArgs
    unless arity == rhs.getAppNumArgs do
      throwCongrEx lhs rhs "Both sides have different numbers of arguments."
    let f := lhs.getAppFn
    let f' := rhs.getAppFn
    unless ← isDefEq (← inferType f) (← inferType f') do
      throwCongrEx lhs rhs "The functions in each application have non-defeq types."
    let fnRes ← mkCongrOf (depth + 1) mvarCounterSaved f f'
    trace[Tactic.congr] "mkCongrOf result {f}, {f'} has isRfl = {fnRes.isRfl}"
    let lhs := mkAppN fnRes.lhs lhs.getAppArgs
    let rhs := mkAppN fnRes.rhs rhs.getAppArgs
    -- If there's a nontrivial proof, then since mkHCongrWithArity doesn't rewrite the function
    -- we need to handle this ourselves.
    if !fnRes.isRfl then
      let mut pf ← fnRes.eq
      for arg in lhs.getAppArgs do
        pf ← mkCongrFun pf arg
      let res' ← mkCongrOf (depth + 1) mvarCounterSaved (mkAppN fnRes.rhs lhs.getAppArgs) rhs
      if res'.isRfl then
        return {lhs, rhs, pf? := pf}
      else
        -- Need to combine these results by transitivity. Slightly inefficient to switch to heq.
        let pf'' ← mkAppM ``HEq.trans #[← mkAppM ``heq_of_eq #[pf], ← res'.heq]
        return {lhs, rhs, pf? := pf''}
    let argRes ← (lhs.getAppArgs.zip rhs.getAppArgs).mapM fun (x, x') =>
                    mkCongrOf (depth + 1) mvarCounterSaved x x'
    if argRes.all fun res => res.isRfl then
      return {lhs, rhs, pf? := none}
    let thm ← mkHCongrWithArity fnRes.lhs arity
    let mut args := #[]
    for res in argRes, kind in thm.argKinds do
      match kind with
      | .eq =>
        let pf ← res.eq
        let some (_, lhs, rhs) := (← whnf <| ← inferType pf).eq? | unreachable!
        args := args |>.push lhs |>.push rhs |>.push pf
      | .heq =>
        let pf ← res.heq
        let some (_, lhs, _, rhs) := (← whnf <| ← inferType pf).heq? | unreachable!
        args := args |>.push lhs |>.push rhs |>.push pf
      | _ => panic! "unexpected hcongr argument kind"
    let pf := mkAppN thm.proof args
    return {lhs, rhs, pf? := pf}
  -- lam forallE letE
  | .lam .., .lam .. =>
    trace[Tactic.congr] "lam"
    let resDom ← mkCongrOf (depth + 1) mvarCounterSaved lhs.bindingDomain! rhs.bindingDomain!
    -- We do not yet support congruences in the binding domain for lambdas.
    discard <| resDom.defeq
    withLocalDecl lhs.bindingName! lhs.bindingInfo! resDom.lhs fun x => do
      let lhsb := lhs.bindingBody!.instantiate1 x
      let rhsb := rhs.bindingBody!.instantiate1 x
      let resBody ← mkCongrOf (depth + 1) mvarCounterSaved lhsb rhsb
      let lhs ← mkLambdaFVars #[x] resBody.lhs
      let rhs ← mkLambdaFVars #[x] resBody.rhs
      if resBody.isRfl then
        return {lhs, rhs, pf? := none}
      else
        let pf ← mkLambdaFVars #[x] (← resBody.eq)
        return {lhs, rhs, pf? := ← mkAppM ``funext #[pf]}
  | .forallE .., .forallE .. =>
    trace[Tactic.congr] "forallE"
    let resDom ← mkCongrOf (depth + 1) mvarCounterSaved lhs.bindingDomain! rhs.bindingDomain!
    if lhs.isArrow && rhs.isArrow then
      let resBody ← mkCongrOf (depth + 1) mvarCounterSaved lhs.bindingBody! rhs.bindingBody!
      let lhs := Expr.forallE lhs.bindingName! resDom.lhs resBody.lhs lhs.bindingInfo!
      let rhs := Expr.forallE rhs.bindingName! resDom.rhs resBody.rhs rhs.bindingInfo!
      if resDom.isRfl && resBody.isRfl then
        return {lhs, rhs, pf? := none}
      else
        return {lhs, rhs, pf? := ← mkImpCongr (← resDom.eq) (← resBody.eq)}
    else
      -- We do not yet support congruences in the binding domain for dependent pi types.
      discard <| resDom.defeq
      withLocalDecl lhs.bindingName! lhs.bindingInfo! resDom.lhs fun x => do
        let lhsb := lhs.bindingBody!.instantiate1 x
        let rhsb := rhs.bindingBody!.instantiate1 x
        let resBody ← mkCongrOf (depth + 1) mvarCounterSaved lhsb rhsb
        let lhs ← mkForallFVars #[x] resBody.lhs
        let rhs ← mkForallFVars #[x] resBody.rhs
        if resBody.isRfl then
          return {lhs, rhs, pf? := none}
        else
          let pf ← mkLambdaFVars #[x] (← resBody.eq)
          return {lhs, rhs, pf? := ← mkAppM ``pi_congr #[pf]}
  | .letE .., .letE .. =>
    trace[Tactic.congr] "letE"
    -- Zeta reduce for now. Could look at `Lean.Meta.Simp.simp.simpLet`
    let lhs := lhs.letBody!.instantiate1 lhs.letValue!
    let rhs := rhs.letBody!.instantiate1 rhs.letValue!
    let res ← mkCongrOf (depth + 1) mvarCounterSaved lhs rhs
    return {res with lhs, rhs}
  | .mdata _ lhs', .mdata _ rhs' =>
    trace[Tactic.congr] "mdata"
    let res ← mkCongrOf (depth + 1) mvarCounterSaved lhs' rhs'
    return {res with lhs := lhs.updateMData! res.lhs, rhs := rhs.updateMData! res.rhs}
  | .proj n1 i1 e1, .proj n2 i2 e2 =>
    trace[Tactic.congr] "proj"
    -- Only handles defeq at the moment.
    -- Recurses just to propagate type information for elaboration reasons.
    unless n1 == n2 && i1 == i2 do
      throwCongrEx lhs rhs "Incompatible primitive projections"
    let res ← mkCongrOf (depth + 1) mvarCounterSaved e1 e2
    discard <| res.defeq
    return {lhs := lhs.updateProj! res.lhs, rhs := rhs.updateProj! res.rhs, pf? := none}
  | _, _ =>
    trace[Tactic.congr] "base case"
    -- Shouldn't need to instantiate metavars, but it's to be sure we catch congruence holes
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    if let some h ← hasCHole mvarCounterSaved lhs then
      throwError "Left-hand side{indentD lhs}\nstill has a congruence hole{indentD h}"
    if let some h ← hasCHole mvarCounterSaved rhs then
      throwError "Right-hand side{indentD rhs}\nstill has a congruence hole{indentD h}"
    mkCongrOfDefeq lhs rhs

@[term_elab termCongr]
def elabTermCongr : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(congr($t)) =>
    -- Save the current mvarCounter so that we can tell which cHoles are for this congr quotation.
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let expEq ← mkEqForExpectedType expectedType?
    let some (expTy, expLhs, expRhs) := expEq.eq? | unreachable!
    let lhs ← elaboratePattern t expTy true
    let rhs ← elaboratePattern t expTy false
    unless ← isDefEq expLhs lhs do
      throwError "Left-hand side of elaborated pattern{indentD lhs}\n{""
        }is not definitionally equal to left-hand side of expected type{indentD expEq}"
    unless ← isDefEq expRhs rhs do
      throwError "Right-hand side of elaborated pattern{indentD rhs}\n{""
        }is not definitionally equal to right-hand side of expected type{indentD expEq}"
    Term.synthesizeSyntheticMVars (mayPostpone := true)
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    let res ← mkCongrOf 0 mvarCounterSaved lhs rhs
    let pf ← res.eq
    --logInfo m!"pf type = {toString (← inferType pf)}"
    return pf
  | _ => throwUnsupportedSyntax
