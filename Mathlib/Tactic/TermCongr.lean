/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
import Mathlib.Logic.Basic
import Mathlib.Tactic.Congr!

/-! # `congr(...)` congruence quotations

This module defines a term elaborator for generating congruence lemmas by writing patterns
using quotation-like syntax.
One can write `congr($hf $hx)` with `hf : f = f'` and `hx : x = x'` to get `f x = f' x'`.
While in simple cases it might be possible to use `congr_arg` or `congr_fun`,
congruence quotations are more general,
since for example `f` could have implicit arguments and complicated dependent types.

The implementation strategy is the following:

1. The pattern is elaborated twice, once with each hole replaced by the LHS
   and again with each hole replaced by the RHS. We do not force the hole to
   have any particular type while elaborating, but whenever we can figure out
   a LHS or a RHS we unify.
   We use `Mathlib.Tactic.TermCongr.cHole` with metadata for these replacements.
2. Once these are elaborated, we unify against the LHS and RHS of the target type.
3. Then we simultaneously walk along the elaborated LHS and RHS expressions
   to generate a congruence.
   When we reach `cHole`s, we make sure they elaborated in a compatible way.
   For applications we use a version of `Lean.Meta.mkHCongrWithArity` that tries
   to fill in some of the equality proofs using subsingleton lemmas.

The point of elaborating the expression twice is that we let the elaborator handle
activities like synthesizing instances.

During development there was a version using `simp` transformations, but there was
no way to inform `simp` about the expected RHS, which could cause `simp` to fail because
it eagerly wants to solve for instance arguments. The current version is able to use the
expected LHS and RHS to fill in arguments before solving for instance arguments.
-/

namespace Mathlib.Tactic.TermCongr
open Lean Elab Meta

initialize registerTraceClass `Tactic.congr

/--
`congr(expr)` generates an congruence from an expression containing
congruence holes of the form `$h` or `$(h)`.
In these congruence holes, `h : a = b` indicates that, in the generated congruence,
on the left-hand side `a` is substituted for `$h`
and on the right-hand side `b` is substituted for `$h`.

For example, if `h : a = b` then `congr(1 + $h) : 1 + a = 1 + b`.
-/
syntax (name := termCongr) "congr(" withoutForbidden(ppDedentIfGrouped(term)) ")" : term

/-- Key for congruence hole metadata.
For a `Bool` recording whether this hole is for the LHS elaboration. -/
private def congrHoleForLhsKey : Name := decl_name%
/-- Key for congruence hole metadata.
For a `Nat` recording how old this congruence hole is, to prevent reprocessing them
if they leak into the local context. -/
private def congrHoleIndex : Name := decl_name%

/-- Hold onto the hole's value along with the value of either the LHS or RHS of the hole. -/
@[reducible] def cHole {α : Sort u} (val : α) {p : Prop} (_ : p) : α := val

/-- For error reporting purposes, make the hole pretty print as its value.
We can still see it's a hole on mouseover in the info view. -/
@[app_unexpander cHole] def unexpandCHole : Lean.PrettyPrinter.Unexpander
  | `($_ $val $_) => pure val
  | _ => throw ()

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

/-- Create the congruence hole. Used by `elabCHole`.

Saves the current mvarCounter as a proxy for age. We use this to avoid
reprocessing old congruence holes that happened to leak into the local context. -/
def mkCHole (forLhs : Bool) (val pf : Expr) : MetaM Expr := do
  -- Create a metavariable to bump the mvarCounter.
  discard <| mkFreshTypeMVar
  let d : MData := KVMap.empty
    |>.insert congrHoleForLhsKey forLhs
    |>.insert congrHoleIndex (← getMCtx).mvarCounter
  return Expr.mdata d <| ← mkAppM ``cHole #[val, pf]

/-- Elaborates a congruence hole and returns either the left-hand side or the right-hand side,
annotated with information necessary to generate a congruence lemma. -/
def elabCHole (h : Syntax) (forLhs : Bool) : Term.TermElabM Expr := do
  let pf ← Term.elabTerm h none
  let pfTy ← inferType pf
  unless ← isDefEq (← inferType pfTy) (.sort .zero) do
    throwError "Hole has type{indentD pfTy}\nbut is expected to be a Prop"
  if let some (_, lhs, _, rhs) ← sides? pfTy then
    mkCHole forLhs (if forLhs then lhs else rhs) pf
  else
    mkCHole forLhs (← mkFreshExprMVar none) pf

/-- If the expression is a congruence hole, returns `(forLhs, mvarCounter, sideVal, pf)`. -/
def cHole? (e : Expr) : Option (Bool × Nat × Expr × Expr) := do
  match e with
  | .mdata d e' =>
    let forLhs : Bool ← d.get? congrHoleForLhsKey
    let mvarCounter : Nat ← d.get? congrHoleIndex
    let #[_, val, _, pf] := e'.getAppArgs | failure
    return (forLhs, mvarCounter, val, pf)
  | _ => none

/-- If the expression is a recent congruence hole, returns `(forLhs, sideVal, pf)`.
Does `cHole?` but makes sure that it's recent. -/
def cHole?' (mvarCounterSaved : Nat) (e : Expr) :
    Option (Bool × Expr × Expr) := do
  let some (forLhs, mvarCounter, sideVal, pf) := cHole? e | failure
  guard <| mvarCounterSaved ≤ mvarCounter
  return (forLhs, sideVal, pf)

/-- Returns any subexpression that is a recent congruence hole.  -/
def hasCHole (mvarCounterSaved : Nat) (e : Expr) : Option Expr :=
  e.find? fun e' => (cHole?' mvarCounterSaved e').isSome

/-- Eliminate all congruence holes from an expression. -/
def removeCHoles (e : Expr) : Expr :=
  e.replace fun e' => if let some (_, _, val, _) := cHole? e' then val else none

/-- (Internal for `congr(...)`)
Elaborates to an expression satisfying `cHole?` that equals the LHS of `h`. -/
elab (name := cLhsExpand) "c_lhs% " h:term : term => elabCHole h true

/-- (Internal for `congr(...)`)
Elaborates to an expression satisfying `cHole?` that equals the RHS of `h`. -/
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

/-- Ensures the expected type is an iff. Returns the iff.
This expression is suitable for `Lean.Expr.iff?`. -/
def mkIffForExpectedType (expectedType? : Option Expr) : MetaM Expr := do
  let a ← mkFreshExprMVar (Expr.sort .zero)
  let b ← mkFreshExprMVar (Expr.sort .zero)
  let iff := mkApp2 (Expr.const `Iff []) a b
  if let some expectedType := expectedType? then
    unless ← isDefEq expectedType iff do
      throwError m!"Term {← mkHasTypeButIsExpectedMsg iff expectedType}"
  return iff

/-- Make the expected type of `pf` be an iff. -/
def ensureIff (pf : Expr) : MetaM Expr := do
  discard <| mkIffForExpectedType (← inferType pf)
  return pf

/-- A congruence lemma between two expressions.
The expressions can be related by `Iff`, `Eq`, or `HEq`.
The given proof can be a proof of any of these relations.

This complexity is to support two features:

1. The user is free to supply Iff, Eq, and HEq lemmas in congurence holes,
   and we're able to transform them into whatever is appropriate for a
   given congruence lemma.
2. If the congrence hole is a metavariable, then we can specialize that
   hole to an Iff, Eq, or HEq depending on what's necessary at that site. -/
structure CongrResult where
  (lhs rhs : Expr)
  /-- A proof somehow relates `lhs` to `rhs` (by `Iff`, `Eq`, or `HEq`).
  If `none`, then the proof is the appropriate notion of reflexivity
  and `lhs` and `rhs` are defeq. -/
  (pf? : Option Expr)

/-- Returns whether the proof is by reflexivity.
Such congruence proofs are trivial. -/
def CongrResult.isRfl (res : CongrResult) : Bool := res.pf?.isNone

/-- Report an error if `res.lhs` is not defeq to `lhs`. -/
def CongrResult.assertLhsDefeq (res : CongrResult) (lhs pfTy : Expr) : MetaM Unit := do
  unless ← isDefEq res.lhs lhs do
    throwError "Left-hand side of congruence lemma is{indentD res.lhs}\n{""
      }and is not definitionally equal to left-hand side of congruence hole, which has type{""
      }{indentD pfTy}"

/-- Report an error if `res.rhs` is not defeq to `rhs`. -/
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
      throwError "Cannot turn HEq proof into an equality proof. Has type{indentD ty}"
    mkAppM ``eq_of_heq #[pf]
  else
    let pf ← if prop then do mkPropExt (← ensureIff pf) else pure pf
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
    res.assertLhsDefeq lhs (← inferType pf)
    res.assertRhsDefeq rhs (← inferType pf)
    return pf
  | none =>
    -- Then `isDefEq res.lhs res.rhs`
    mkEqRefl res.lhs

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
    mkHEqRefl res.lhs

/-- Ensures `lhs` and `rhs` are defeq. -/
def ensureDefeq (lhs rhs : Expr) : MetaM Unit := do
  unless ← isDefEq lhs rhs do
    throwError "congr(...) failed, {""
      }left-hand side{indentD lhs}\nis not definitionally equal to right-hand side{indentD rhs}"

/-- Checks that `lhs` and `rhs` are defeq, returning a trivial congruence.

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

/-- Variant of `Lean.Meta.mkHCongrWithArity` that tries to prove hypotheses using
subsingleton lemmas. These are recorded as `CongrArgKind.subsingletonInst`. -/
def mkHCongrWithArity' (f : Expr) (numArgs : Nat) : MetaM CongrTheorem := do
  let thm ← mkHCongrWithArity f numArgs
  process thm.proof thm.type thm.argKinds.toList #[] #[] #[]
where
  process (pf : Expr) (type : Expr) (argKinds : List CongrArgKind)
      (argKinds' : Array CongrArgKind) (params args : Array Expr) : MetaM CongrTheorem := do
    match argKinds with
    | [] =>
      let pf' ← mkLambdaFVars params (mkAppN pf args)
      return {proof := pf', type := ← inferType pf', argKinds := argKinds'}
    | argKind :: argKinds =>
      match argKind with
      | .eq | .heq =>
        forallBoundedTelescope type (some 3) fun params' type' => do
          let #[x, y, eq] := params' | unreachable!
          -- See if we can prove `eq` from previous parameters.
          let g := (← mkFreshExprMVar (← inferType eq)).mvarId!
          let g ← g.clear eq.fvarId!
          if (← observing? <| prove g).isSome then
            process pf type' argKinds (argKinds'.push .subsingletonInst)
              (params := params ++ #[x, y]) (args := args ++ #[x, y, .mvar g])
          else
            process pf type' argKinds (argKinds'.push argKind)
              (params := params ++ params') (args := args ++ params')
      | _ => panic! "Unexpected CongrArgKind"
  prove (g : MVarId) : MetaM Unit := do
    let g ← g.cleanup
    let g := (← g.substEqs).getD g
    try g.refl; return catch _ => pure ()
    try g.hrefl; return catch _ => pure ()
    if ← g.proofIrrelHeq then return
    -- Make the goal be an eq and then try `Subsingleton.elim`
    let g ← g.heqOfEq
    if ← g.subsingletonElim then return
    -- We have no more tricks.
    failure

/-- If `lhs` or `rhs` is a congruence hole, then process it.
Only process ones that are at least as new as `mvarCounterSaved` since there's nothing
preventing congruence holes from leaking into the local context. -/
def mkCongrOfCHole? (mvarCounterSaved : Nat) (lhs rhs : Expr) : MetaM (Option CongrResult) := do
  match cHole?' mvarCounterSaved lhs, cHole?' mvarCounterSaved rhs with
  | some (isLhs1, val1, pf1), some (isLhs2, val2, pf2) =>
    trace[Tactic.congr] "mkCongrOfCHole, both holes"
    unless isLhs1 == true do
      throwCongrEx lhs rhs "A RHS congruence hole leaked into the LHS"
    unless isLhs2 == false do
      throwCongrEx lhs rhs "A LHS congruence hole leaked into the RHS"
    -- Defeq checks to unify the lhs and rhs congruence holes.
    unless ← isDefEq (← inferType pf1) (← inferType pf2) do
      throwCongrEx lhs rhs "Elaborated types of congruence holes are not defeq."
    if let some (_, lhsVal, _, rhsVal) ← sides? (← inferType pf1) then
      unless ← isDefEq val1 lhsVal do
        throwError "Left-hand side of congruence hole is{indentD lhsVal}\n{""
          }but is expected to be{indentD val1}"
      unless ← isDefEq val2 rhsVal do
        throwError "Right-hand side of congruence hole is{indentD rhsVal}\n{""
          }but is expected to be{indentD val2}"
    return some {lhs := val1, rhs := val2, pf? := pf1}
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
  if depth > 1000 then
    throwError "out of gas"
  if let some res ← mkCongrOfCHole? mvarCounterSaved lhs rhs then
    trace[Tactic.congr] "hole processing succeeded"
    return res
  if (hasCHole mvarCounterSaved lhs).isNone && (hasCHole mvarCounterSaved rhs).isNone then
    -- Then it's safe to fastforward if these are defeq
    if ← isDefEq lhs rhs then
      return {lhs, rhs, pf? := none}
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
    let thm ← mkHCongrWithArity' fnRes.lhs arity
    let mut args := #[]
    let mut nontriv : Bool := false
    for lhs' in lhs.getAppArgs, rhs' in rhs.getAppArgs, kind in thm.argKinds do
      match kind with
      | .eq =>
        let pf ← (← mkCongrOf (depth + 1) mvarCounterSaved lhs' rhs').eq
        let some (_, lhs, rhs) := (← whnf <| ← inferType pf).eq? | unreachable!
        args := args |>.push lhs |>.push rhs |>.push pf
        nontriv := true
      | .heq =>
        let pf ← (← mkCongrOf (depth + 1) mvarCounterSaved lhs' rhs').heq
        let some (_, lhs, _, rhs) := (← whnf <| ← inferType pf).heq? | unreachable!
        args := args |>.push lhs |>.push rhs |>.push pf
        nontriv := true
      | .subsingletonInst =>
        -- Warning: we're not processing any congruence holes here.
        -- Users shouldn't be placing them in such arguments anyway.
        args := args |>.push (removeCHoles lhs') |>.push (removeCHoles rhs')
      | _ => panic! "unexpected hcongr argument kind"
    if nontriv then
      let pf := mkAppN thm.proof args
      return {lhs, rhs, pf? := pf}
    else
      return {lhs, rhs, pf? := none}
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
    -- Just zeta reduce for now. Could look at `Lean.Meta.Simp.simp.simpLet`
    let lhs := lhs.letBody!.instantiate1 lhs.letValue!
    let rhs := rhs.letBody!.instantiate1 rhs.letValue!
    mkCongrOf (depth + 1) mvarCounterSaved lhs rhs
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
    -- to throw the following errors.
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    if let some h := hasCHole mvarCounterSaved lhs then
      throwError "Left-hand side{indentD lhs}\nstill has a congruence hole{indentD h}"
    if let some h := hasCHole mvarCounterSaved rhs then
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
    -- Use the expected type `expEq` so that any type ascriptions stick
    mkExpectedTypeHint pf expEq
  | _ => throwUnsupportedSyntax
