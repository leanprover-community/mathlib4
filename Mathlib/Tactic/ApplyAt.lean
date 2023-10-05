/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Lean

/-!
# Apply at

A tactic for applying functions at hypotheses.
-/

open Lean Meta Elab Tactic Term

/--
This function is similar to `forallMetaTelescopeReducingUntilDefEq` except that
it will construct mvars until it reaches one whose type is defeq to the given
type `t`. It uses `forallMetaTelescopeReducing`.
-/
def Lean.Meta.forallMetaTelescopeReducingUntilDefEq
    (e t : Expr) (kind : MetavarKind := MetavarKind.natural) :
    MetaM (Array Expr × Array BinderInfo × Expr) := do
  let mut mvs : Array Expr := #[]
  let mut bis : Array BinderInfo := #[]
  let (ms, bs, tp) ← forallMetaTelescopeReducing e (some 1) kind
  unless ms.size == 1 do throwError "Error"
  mvs := ms
  bis := bs
  let mut out : Expr := tp
  while !(← isDefEq (← inferType mvs.toList.getLast!) t) do
    let (ms, bs, tp) ← forallMetaTelescopeReducing out (some 1) kind
    unless ms.size == 1 do throwError "Error"
    mvs := mvs ++ ms
    bis := bis ++ bs
    out := tp
  return (mvs, bis, out)

namespace Mathlib.Tactic

/--
`apply t at i` will apply a function `t` at `i`.
Explicitly, if `t : α₁ → ⋯ → αᵢ → ⋯ → αₙ` and `i` has type `αᵢ`, then this tactic will add
metavariables/goals for any terms of `αⱼ` for `j = 1, …, i-1`,
then replace the type of `i` with `αᵢ₊₁ → ⋯ → αₙ` by applying those metavariables and the
original `i`.
-/
elab "apply" t:term "at" i:ident : tactic => withMainContext do
  let f ← Term.elabTerm (← `(@$t)) none
  let some ldecl := (← getLCtx).findFromUserName? i.getId |
    throwError "Error"
  let (mvs, _, tp) ← forallMetaTelescopeReducingUntilDefEq (← inferType f) ldecl.type
  let mainGoal ← getMainGoal
  let mainGoal ← mainGoal.tryClear ldecl.fvarId
  let mainGoal ← mainGoal.assert ldecl.userName tp
    (← mkAppOptM' f (mvs.pop.push ldecl.toExpr |>.map fun e => some e))
  let (_, mainGoal) ← mainGoal.intro1P
  replaceMainGoal <| [mainGoal] ++ mvs.pop.toList.map fun e => e.mvarId!
