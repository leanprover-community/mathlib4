/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean.Meta.Tactic.Cleanup

/-! # Configurable cleanup meta tactic

This module defines `Lean.MVarId.cleanupExcept` as a configurable version of `Lean.MVarId.cleanup`.
-/

namespace Lean
open Meta

private partial def cleanupExceptCore (mvarId : MVarId)
    (fvarIds : Array FVarId) (props : Bool) : MetaM MVarId := do
  mvarId.withContext do
    mvarId.checkNotAssigned `cleanupExcept
    let target ← instantiateMVars (← mvarId.getType)
    let used ← collectUsed target |>.run' (false, {})
    let mut lctx ← getLCtx
    for localDecl in lctx do
      unless used.contains localDecl.fvarId do
        lctx := lctx.erase localDecl.fvarId
    let localInsts := (← getLocalInstances).filter fun inst => used.contains inst.fvar.fvarId!
    let mvarNew ← mkFreshExprMVarAt lctx localInsts target .syntheticOpaque (← mvarId.getTag)
    mvarId.assign mvarNew
    return mvarNew.mvarId!
where
  addUsedFVars (e : Expr) : StateRefT (Bool × FVarIdSet) MetaM Unit := do
    let (_, s) ← (← instantiateMVars e).collectFVars |>.run {}
    for fvarId in s.fvarSet do
      addUsedFVar fvarId

  addUsedFVar (fvarId : FVarId) : StateRefT (Bool × FVarIdSet) MetaM Unit := do
    unless (← get).2.contains fvarId do
      modify fun (_, s) => (true, s.insert fvarId)
      let localDecl ← fvarId.getDecl
      addUsedFVars localDecl.type
      if let some val := localDecl.value? then
        addUsedFVars val

  /-- We include `p` in the used-set, if `p` is a proposition
  that contains a `x` that is in the used-set. -/
  collectProps : StateRefT (Bool × FVarIdSet) MetaM Unit := do
    modify fun s => (false, s.2)
    let usedSet := (← get).2
    for localDecl in (← getLCtx) do
      if (← isProp localDecl.type) then
        if (← dependsOnPred localDecl.type usedSet.contains) then
          addUsedFVar localDecl.fvarId
    if (← get).1 then
      collectProps

  collectUsed (e : Expr) : StateRefT (Bool × FVarIdSet) MetaM FVarIdSet := do
    addUsedFVars e
    fvarIds.forM addUsedFVar
    if props then collectProps
    return (← get).2

/--
Like `Lean.MVarId.cleanup` but allows preserving the local variables referred to by the `fvarIds`
array and allows controlling whether to include propositions that reference preserved variables.

In more detail: it removes local variables that are not relevant.
We say a variable is *relevant* if
1. it occurs in `fvarIds`;
2. it occurs in the target type;
3. there is a relevant variable that depends on it; or
4. if `props` is true, then the variable is a proposition and it depends on a relevant variable.
-/
def MVarId.cleanupExcept (mvarId : MVarId)
    (fvarIds : Array FVarId) (props : Bool := false) : MetaM MVarId := do
  cleanupExceptCore mvarId fvarIds props

end Lean
