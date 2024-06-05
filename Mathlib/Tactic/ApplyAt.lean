/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Lean.Elab.Tactic.ElabTerm
import Mathlib.Lean.Meta.Basic

/-!
# Apply at

A tactic for applying functions at hypotheses.
-/

open Lean Meta Elab Tactic Term

namespace Mathlib.Tactic

/--
`apply t at i` will use forward reasoning with `t` at the hypothesis `i`.
Explicitly, if `t : α₁ → ⋯ → αᵢ → ⋯ → αₙ` and `i` has type `αᵢ`, then this tactic will add
metavariables/goals for any terms of `αⱼ` for `j = 1, …, i-1`,
then replace the type of `i` with `αᵢ₊₁ → ⋯ → αₙ` by applying those metavariables and the
original `i`.
-/
elab "apply" t:term "at" i:ident : tactic => withSynthesize <| withMainContext do
  let f ← elabTermForApply t
  let some ldecl := (← getLCtx).findFromUserName? i.getId
    | throwErrorAt i m!"Identifier {i} not found"
  let (mvs, bis, tp) ← forallMetaTelescopeReducingUntilDefEq (← inferType f) ldecl.type
  let mainGoal ← getMainGoal
  let mainGoal ← mainGoal.tryClear ldecl.fvarId
  for (m, b) in mvs.zip bis do
    if b.isInstImplicit && !(← m.mvarId!.isAssigned) then
      try m.mvarId!.inferInstance
      catch _ => continue
  let mainGoal ← mainGoal.assert ldecl.userName tp
    (← mkAppOptM' f (mvs.pop.push ldecl.toExpr |>.map fun e => some e))
  let (_, mainGoal) ← mainGoal.intro1P
  replaceMainGoal <| [mainGoal] ++ mvs.pop.toList.map fun e => e.mvarId!
