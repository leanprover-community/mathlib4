/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public meta import Lean.Meta.Tactic.Delta
public import Batteries.Lean.NameMapAttribute
public import Mathlib.Init

/-!
# Modify proof terms so that they don't rely on unfolding certain constants

This file defines a procedure for inserting casts into (proof) terms in order to make them
well typed in a setting where certain constants aren't allowed to be unfolded.

We make use of `withCanUnfoldPred` in order to modify which constants can and cannot be unfolded.
This way, `whnf` and `isDefEq` do not unfold these constants.

So, the procedure is to check that an expression is well typed, analogous to `Meta.check`,
and at each type mismatch, we try to insert a cast.

There are two kinds of casts:
- Equality casts. This is for propositions and terms,
  where it is possible to prove that one is equal to the other. For example `Monotone`.
- Explicit casting functions, both for unfolding and refolding. This is for types, where we
  cannot express their equivalence with an equality. For example `DecidableLE`.
-/

meta section

namespace Mathlib.Tactic.UnfoldBoundary

open Lean Meta

/-- `UnfoldBoundaries` stores abstraction boundaries for definitions that shouldn't be unfolded. -/
public structure UnfoldBoundaries where
  /-- For propositions and terms of types, we store a rewrite theorem that unfolds it. -/
  unfolds : NameMap SimpTheorem := {}
  /-- For types, we store a cast for translating from and to the type respectively. -/
  casts : NameMap (Name × Name) := {}
  /-- The functions that we want to unfold again after the translation has happened. -/
  insertionFuns : NameSet := {}
  deriving Inhabited

/--
Set up the monadic context:
- Set the transparency to `.all`, just like is done in `Meta.check`.
- Use `withCanUnfoldPred` to not allow unfolding the constants for which we want to insert casts.
- Set up the `SimpM` context so that `Simp.simp` will unfold constants from `b.unfolds`.
-/
def run {α} (b : UnfoldBoundaries) (x : SimpM α) : MetaM α :=
  withCanUnfoldPred (fun _ i => return !b.unfolds.contains i.name && !b.casts.contains i.name) do
  withTransparency .all do
  let ctx ← Simp.mkContext Simp.neutralConfig
  x (Simp.Methods.toMethodsRef { pre }) ctx |>.run' {}
where
  pre (e : Expr) : SimpM Simp.Step := do
    let .const c _ ← whnf e.getAppFn | return .continue
    let some thm := b.unfolds.find? c | return .continue
    let some r ← Simp.tryTheorem? e thm | return .continue
    return .visit r

/-- Given a term `e`, add casts to it to unfold constants appearing in it. -/
partial def unfoldConsts (b : UnfoldBoundaries) (e : Expr) : SimpM Expr := do
  let eType ← inferType e
  let e ← do
    let { expr, proof? := some proof } ← Simp.simp eType | pure e
    trace[translate_detail] "unfoldConsts: added a cast from {eType} to {expr}"
    mkAppOptM ``Eq.mp #[eType, expr, proof, e]
  let eTypeWhnf ← whnf (← inferType e)
  if let .const c us := eTypeWhnf.getAppFn then
    if let some (cast, _) := b.casts.find? c then
      let e := .app (mkAppN (.const cast us) eTypeWhnf.getAppArgs) e
      trace[translate_detail] "unfoldConsts: created the cast {e} to unfold {.ofConstName c}"
      return ← unfoldConsts b e
  return e

/-- Given a term `e` which we want to get to have type `expectedType`, return a term of type
`expectedType` by adding cast to `e` that unfold constants in `expectedType`. -/
partial def refoldConsts (b : UnfoldBoundaries) (e expectedType : Expr) : SimpM Expr := do
  let goal ← mkFreshExprMVar expectedType
  go e goal.mvarId!
  instantiateMVars goal
where
  go (e : Expr) (goal : MVarId) : SimpM Unit := do
    let goal ← do
      let { expr, proof? := some proof } ← Simp.simp (← goal.getType) | pure goal
      trace[translate_detail] "refoldConsts: added a cast from {← goal.getType} to {expr}"
      goal.replaceTargetEq expr proof
    forallTelescope (← goal.getType) fun xs tgt => do
      let tgt ← whnf tgt
      if let .const c us := tgt.getAppFn then
        if let some (_, cast) := b.casts.find? c then
          let cast := mkAppN (.const cast us) tgt.getAppArgs
          trace[translate_detail] "refoldConsts: created the cast {cast} to unfold {.ofConstName c}"
          let .forallE _ α _ _ ← inferType cast | throwError "refoldConsts: not a function\n{cast}"
          let goal' ← mkFreshExprMVar α
          go (e.beta xs) goal'.mvarId!
          goal.assign <| ← mkLambdaFVars xs <| .app cast goal'
          return
      unless ← isDefEq (← goal.getType) (← inferType e) do
        throwError "{e} : {← inferType e} does not have type {← goal.getType}."
      goal.assign e

/-- Given an expression `e` with expected type `expectedType`, if `e` doesn't have that type,
use a cast to turn `e` into that type. -/
def mkCast (b : UnfoldBoundaries) (e expectedType : Expr) : SimpM Expr := do
  if ← isDefEq (← inferType e) expectedType then
    return e
  let e ← unfoldConsts b e
  refoldConsts b e expectedType

/-- Create the application `.app f a`, inserting some casts if necessary. -/
def mkAppWithCast (b : UnfoldBoundaries) (f a : Expr) : SimpM Expr :=
  try
    checkApp f a
    return f.app a
  catch _ =>
    let f ← unfoldConsts b f
    let .forallE _ d _ _ ← whnf (← inferType f) | throwFunctionExpected f
    return f.app (← mkCast b a d)

/-- Modify `e` so that it has type `expectedType` if the constants in `b` cannot be unfolded. -/
def UnfoldBoundaries.cast (b : UnfoldBoundaries) (e expectedType : Expr) (attr : Name) :
    MetaM Expr :=
  run b <|
  try
    mkCast b e expectedType
  catch ex =>
    throwError "@[{attr}] failed to insert a cast to make `{e}` \
      have type `{expectedType}`\n\n{ex.toMessageData}"

/-- Modify `e` so that it is well typed if the constants in `b` cannot be unfolded.

Note: it may be that `e` contains some constant whose type is not well typed in this setting.
We don't make an effort to replace such constants.
It seems that this approximation works well enough. -/
def UnfoldBoundaries.insertBoundaries (b : UnfoldBoundaries) (e : Expr) (attr : Name) :
    MetaM Expr :=
  run b <| Meta.transform e (post := fun e ↦ e.withApp fun f args =>
    try
      return .done <| ← args.foldlM (mkAppWithCast b) f
    catch ex =>
      throwError "@[{attr}] failed to insert a cast to make `{f}` applied to `{args.toList}` \
        well typed\n\n{ex.toMessageData}")

/-- Unfold all of the auxiliary functions that were inserted as unfold boundaries. -/
def UnfoldBoundaries.unfoldInsertions (e : Expr) (b : UnfoldBoundaries) : CoreM Expr :=
  -- This is the same as `Meta.deltaExpand`, but with an extra beta reduction.
  Core.transform e fun e => do
    if let some e ← delta? e b.insertionFuns.contains then
      return .visit (headBetaBody e)
    return .continue
where
  headBetaBody (e : Expr) : Expr :=
    match e with
    | .lam _ d b bi => e.updateLambda! bi d (headBetaBody b)
    | _ => e.headBeta

/-- An entry for the `UnfoldBoundaries` environment extension. -/
public inductive UnfoldEntry where
  | unfold (declName : Name) (unfold : Name)
  | cast (declName : Name) (unfold refold unfold' refold' : Name)

def UnfoldBoundaries.insert (b : UnfoldBoundaries) : UnfoldEntry → UnfoldBoundaries
  | .unfold declName unfold => { b with
    unfolds := b.unfolds.insert declName
      { origin := .decl unfold, proof := mkConst unfold, rfl := false } }
  | .cast declName unfold refold unfold' refold' => { b with
    casts := b.casts.insert declName (unfold, refold)
    insertionFuns := b.insertionFuns.insertMany [unfold, refold, unfold', refold'] }

/-- Extensions for handling abstraction boundaries for definitions that shouldn't be unfolded. -/
public abbrev UnfoldBoundaryExt := SimplePersistentEnvExtension UnfoldEntry UnfoldBoundaries

/-- Register a new `UnfoldBoundaryExt`. -/
public def registerUnfoldBoundaryExt : IO UnfoldBoundaryExt := do
  registerSimplePersistentEnvExtension {
    addEntryFn := UnfoldBoundaries.insert
    addImportedFn as := as.foldl (Array.foldl (·.insert ·)) {}
  }

@[inherit_doc UnfoldBoundaries.cast]
public def UnfoldBoundaryExt.cast (b : UnfoldBoundaryExt) (e expectedType : Expr) (attr : Name) :
    MetaM Expr := do
  (b.getState (← getEnv)).cast e expectedType attr

@[inherit_doc UnfoldBoundaries.insertBoundaries]
public def UnfoldBoundaryExt.insertBoundaries (b : UnfoldBoundaryExt) (e : Expr) (attr : Name) :
    MetaM Expr := do
  (b.getState (← getEnv)).insertBoundaries e attr

@[inherit_doc UnfoldBoundaries.unfoldInsertions]
public def UnfoldBoundaryExt.unfoldInsertions (e : Expr) (b : UnfoldBoundaryExt) : CoreM Expr := do
  (b.getState (← getEnv)).unfoldInsertions e


end Mathlib.Tactic.UnfoldBoundary
