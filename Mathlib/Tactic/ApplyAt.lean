/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.Tactic
import Lean

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

elab "apply" t:term "at" i:ident : tactic => withMainContext do
  let f ← Term.elabTerm (← `(@$t)) none
  let ldecl ← (← getLCtx).findFromUserName? i.getId
  let (mvs, _, tp) ← forallMetaTelescopeReducingUntilDefEq (← inferType f) ldecl.type
  let mainGoal ← getMainGoal
  let mainGoal ← mainGoal.tryClear ldecl.fvarId
  let mainGoal ← mainGoal.assert ldecl.userName tp
    (← mkAppOptM' f (mvs.pop.push ldecl.toExpr |>.map fun e => some e))
  let (_, mainGoal) ← mainGoal.intro1P
  replaceMainGoal <| [mainGoal] ++ mvs.pop.toList.map fun e => e.mvarId!
