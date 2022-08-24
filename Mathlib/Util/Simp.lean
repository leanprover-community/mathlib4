/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/

import Lean
import Mathlib.Tactic.OpenPrivate

/-!
# Helper functions for the `norm_cast` tactic.

[TODO] Needs documentation, cleanup, and possibly reunification of `mkSimpContext'` with core.
-/

def Std.PHashSet.toList [BEq α] [Hashable α] (s : Std.PHashSet α) : List α :=
  s.1.toList.map (·.1)

namespace Lean

namespace Meta.DiscrTree

partial def Trie.getElements : Trie α → Array α
  | Trie.node vs children =>
    vs ++ children.concatMap fun (_, child) => child.getElements

def getElements (d : DiscrTree α) : Array α :=
  d.1.toList.toArray.concatMap fun (_, child) => child.getElements

end Meta.DiscrTree

namespace Meta.Simp
open Elab.Tactic

instance : ToFormat SimpTheorems where
  format s :=
f!"pre:
{s.pre.getElements.toList}
post:
{s.post.getElements.toList}
lemmaNames:
{s.lemmaNames.toList}
toUnfold: {s.toUnfold.toList}
erased: {s.erased.toList}
toUnfoldThms: {s.toUnfoldThms.toList}"

def mkEqSymm (e : Expr) (r : Simp.Result) : MetaM Simp.Result :=
  ({ expr := e, proof? := · }) <$>
  match r.proof? with
  | none => pure none
  | some p => some <$> Meta.mkEqSymm p

def mkCast (r : Simp.Result) (e : Expr) : MetaM Expr := do
  mkAppM ``cast #[← r.getProof, e]

/-- Return all propositions in the local context. -/
def getPropHyps : MetaM (Array FVarId) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isAuxDecl do
      if (← isProp localDecl.type) then
        result := result.push localDecl.fvarId
  return result

export private mkDischargeWrapper from Lean.Elab.Tactic.Simp

-- copied from core
/--
  If `ctx == false`, the config argument is assumed to have type `Meta.Simp.Config`, and `Meta.Simp.ConfigCtx` otherwise.
  If `ctx == false`, the `discharge` option must be none -/
def mkSimpContext' (simpTheorems : SimpTheorems) (stx : Syntax) (eraseLocal : Bool)
    (kind := SimpKind.simp) (ctx := false) (ignoreStarArg : Bool := false) :
    TacticM MkSimpContextResult := do
  if ctx && !stx[2].isNone then
    throwError "'simp_all' tactic does not support 'discharger' option"
  let dischargeWrapper ← mkDischargeWrapper stx[2]
  let simpOnly := !stx[3].isNone
  let simpTheorems ←
    if simpOnly then
      ({} : SimpTheorems).addConst ``eq_self
    else
      pure simpTheorems
  let congrTheorems ← Meta.getSimpCongrTheorems
  let r ← elabSimpArgs stx[4] (eraseLocal := eraseLocal) (kind := kind) {
    config       := (← elabSimpConfig stx[1] (kind := kind))
    simpTheorems := #[simpTheorems], congrTheorems
  }
  if !r.starArg || ignoreStarArg then
    return { r with fvarIdToLemmaId := {}, dischargeWrapper }
  else
    let ctx := r.ctx
    let mut simpTheorems := ctx.simpTheorems
    let hs ← getPropHyps
    let mut ctx := ctx
    let mut fvarIdToLemmaId := {}
    for h in hs do
      let localDecl ← h.getDecl
      unless simpTheorems.isErased localDecl.userName do
        let fvarId := localDecl.fvarId
        let proof  := localDecl.toExpr
        let id     ← mkFreshUserName `h
        fvarIdToLemmaId := fvarIdToLemmaId.insert fvarId id
        simpTheorems ← simpTheorems.addTheorem proof (name? := id)
        ctx := { ctx with simpTheorems }
    return { ctx, fvarIdToLemmaId, dischargeWrapper }
