/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Linarith
public meta import Mathlib.Tactic.Rify
public import Mathlib.Data.NNReal.Basic

/-!
# NNReal linarith preprocessing

This file contains a `linarith` preprocessor for converting (in)equalities in `ℝ≥0` to `ℝ`.

By overriding the behaviour of the placeholder preprocessor `nnrealToReal` (which does nothing
unless this file is imported) `linarith` can still be used without importing `NNReal`.
-/

public meta section

namespace Mathlib.Tactic.Linarith

open Lean Meta

/--
`isNNRealProp tp` is true iff `tp` is an inequality or equality between nonnegative real numbers
or the negation thereof.
-/
partial def isNNRealProp (e : Expr) : MetaM Bool := succeeds do
  let (_, _, .const ``NNReal _, _, _) ← e.ineqOrNotIneq? | failure

/-- If `e` is of the form `((x : ℝ≥0) : ℝ)`, `NNReal.toReal e` returns `x`. -/
def isNNRealtoReal (e : Expr) : Option Expr :=
  match e with
  | .app (.const ``NNReal.toReal _) n => some n
  | _ => none

/--
`getNNRealComparisons e` returns a list of all subexpressions of `e` of the form `(x : ℝ)`.
-/
partial def getNNRealCoes (e : Expr) : List Expr :=
  match isNNRealtoReal e with
  | some x => [x]
  | none => match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => getNNRealCoes a ++ getNNRealCoes b
    | (``HMul.hMul, #[_, _, _, _, a, b]) => getNNRealCoes a ++ getNNRealCoes b
    | (``HSub.hSub, #[_, _, _, _, a, b]) => getNNRealCoes a ++ getNNRealCoes b
    | (``HDiv.hDiv, #[_, _, _, _, a, _]) => getNNRealCoes a
    | (``Neg.neg, #[_, _, a]) => getNNRealCoes a
    | _ => []

/-- If `e : ℝ≥0`, returns a proof of `0 ≤ (e : ℝ)`. -/
def mk_toReal_nonneg_prf (e : Expr) : MetaM (Option Expr) :=
  try commitIfNoEx (mkAppM ``NNReal.coe_nonneg #[e])
  catch e => do
    trace[linarith] "Got exception when using `coe_nonneg` {e.toMessageData}"
    return none

initialize nnrealToRealTransform.set fun l => do
  let l ← l.mapM fun e => do
    let t ← whnfR (← instantiateMVars (← inferType e))
    if ← isNNRealProp t then
      return (← Rify.rifyProof e t).1
    else
      return e
  let atoms : List Expr ← withNewMCtxDepth <| AtomM.run .reducible do
    for e in l do
      let (_, _, a, b) ← (← inferType e).ineq?
      discard <| (getNNRealCoes a).mapM AtomM.addAtom
      discard <| (getNNRealCoes b).mapM AtomM.addAtom
    return (← get).atoms.toList
  let nonneg_pfs : List Expr ← atoms.filterMapM mk_toReal_nonneg_prf
  return nonneg_pfs ++ l

end  Mathlib.Tactic.Linarith
