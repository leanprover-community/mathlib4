/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.GSimp.Types

/-!
# HA
-/

public meta section

namespace Mathlib.Tactic.GSimp
open Lean Meta

set_option linter.style.longLine false

def synthesizeArgs (bis : Array BinderInfo) (xs : Array Expr) : GSimpM Bool := do
  for x in xs, bi in bis do
    if !(← x.mvarId!.isAssigned) then
      let type ← x.mvarId!.getType
      if bi.isInstImplicit then
        if let .some val ← trySynthInstance type then
          if ← withReducibleAndInstances (isDefEq x val) then
            continue
      if ← isProp type then
        if let some proof ← (← getMethods).discharge? type then
          if ← isDefEq x proof then
            continue
      return false
  return true




private def tryTheoremCore (lhs rhs : Expr) (xs : Array Expr) (bis : Array BinderInfo) (val : Expr) (type : Expr) (e : Expr) (thm : GSimpTheorem) : GSimpM (Option Result) := do
  let rec go (e : Expr) : GSimpM (Option Result) := do
    trace[Debug.Meta.Tactic.simp] "trying {← ppGSimpTheorem thm} to rewrite{indentExpr e}"
    if (← isDefEq lhs e) then
      unless ← synthesizeArgs bis xs do
        return none
      let proof ← instantiateMVars (mkAppN val xs)
      if (← hasAssignableMVar proof) then
        trace[Meta.Tactic.simp.rewrite] "{← ppGSimpTheorem thm}, has unassigned metavariables after unification"
        return none
      let rhs ← instantiateMVars rhs
      /-
      We used to use `e == rhs` in the following test.
      However, it include unnecessary proof steps when `e` and `rhs`
      are equal after metavariables are instantiated.
      We are hoping the following `instantiateMVars` should not be too expensive since
      we seldom have assigned metavariables in goals.
      -/
      if (← instantiateMVars e) == rhs then
        trace[Debug.Meta.Tactic.simp] "Not applying {← ppGSimpTheorem thm} with type\
          {indentExpr type}\nto{indentExpr e}\nas the result is structurally equal \
          to the original expression"
        return none
      if thm.perm then
        /-
        We use `.reduceSimpleOnly` because this is how we indexed the discrimination tree.
        See issue #1815
        -/
        if !(← acLt rhs e .reduceSimpleOnly) then
          trace[Meta.Tactic.simp.rewrite] "{← ppGSimpTheorem thm}, perm rejected {e} ==> {rhs}"
          return none
      trace[Meta.Tactic.simp.rewrite] "{← ppGSimpTheorem thm}:{indentExpr e}\n==>{indentExpr rhs}"
      let rhs ← if type.hasBinderNameHint then rhs.resolveBinderNameHint else pure rhs
      return some { expr := rhs, proof? := proof }
    else
      unless lhs.isMVar do
        -- We do not report unification failures when `lhs` is a metavariable
        -- Example: `x = ()`
        -- TODO: reconsider if we want thms such as `(x : Unit) → x = ()`
        trace[Meta.Tactic.simp.unify] "{← ppGSimpTheorem thm}, failed to unify{indentExpr lhs}\nwith{indentExpr e}"
      return none
  match (← go e) with
  | none => return none
  | some r =>
    if (← hasAssignableMVar r.expr) then
      trace[Meta.Tactic.simp.rewrite] "{← ppGSimpTheorem thm}, resulting expression has unassigned metavariables"
      return none
    return r

def tryTheorem? (e : Expr) (thm : GSimpTheorem) : GSimpM (Option Result) :=
  withNewMCtxDepth do
    let val  ← thm.getValue
    let type ← inferType val
    let (xs, bis, type) ← forallMetaTelescopeReducing type
    let type ← whnf (← instantiateMVars type)
    let lhs := type.appFn!.appArg!
    let rhs := type.appArg!
    let (lhs, rhs) := if thm.inv then (rhs, lhs) else (lhs, rhs)
    tryTheoremCore lhs rhs xs bis val type e thm

/--
Remark: the parameter tag is used for creating trace messages. It is irrelevant otherwise.
-/
def grewrite? (e : Expr) (s : DiscrTree GSimpTheorem) (erased : PHashSet Origin) (tag : String) : GSimpM (Option Result) := do
  if (← getConfig).index then
    rewriteUsingIndex?
  else
    rewriteNoIndex?
where
  /-- For `(← getConfig).index := true`, use discrimination tree structure when collecting `simp` theorem candidates. -/
  rewriteUsingIndex? : GSimpM (Option Result) := do
    let candidates ← s.getMatch e
    if candidates.isEmpty then
      trace[Debug.Meta.Tactic.simp] "no theorems found for {tag}-rewriting {e}"
      return none
    else
      let candidates := candidates.insertionSort fun e₁ e₂ => e₁.priority > e₂.priority
      for thm in candidates do
        if thm.inv != (← isInv) then continue
        if inErasedSet thm then continue
        if let some result ← tryTheorem? e thm then
          trace[Debug.Meta.Tactic.simp] "rewrite result {e} => {result.expr}"
          return some result
      return none

  /--
  For `(← getConfig).index := false`, Lean 3 style `simp` theorem retrieval.
  Only the root symbol is taken into account. Most of the structure of the discrimination tree is ignored.
  -/
  rewriteNoIndex? : GSimpM (Option Result) := do
    let (candidates, numArgs) ← s.getMatchLiberal e
    if candidates.isEmpty then
      trace[Debug.Meta.Tactic.simp] "no theorems found for {tag}-rewriting {e}"
      return none
    else
      let candidates := candidates.insertionSort fun e₁ e₂ => e₁.priority > e₂.priority
      for thm in candidates do
        unless thm.inv != (← isInv) || inErasedSet thm do
          let result? ← withNewMCtxDepth do
            let val  ← thm.getValue
            let type ← inferType val
            let (xs, bis, type) ← forallMetaTelescopeReducing type
            let type ← whnf (← instantiateMVars type)
            let lhs := type.appFn!.appArg!
            let rhs := type.appArg!
            let (lhs, rhs) := if thm.inv then (rhs, lhs) else (lhs, rhs)
            let lhsNumArgs := lhs.getAppNumArgs
            if lhsNumArgs == numArgs then
              tryTheoremCore lhs rhs xs bis val type e thm
            else
              pure none
          if let some result := result? then
            trace[Debug.Meta.Tactic.simp] "rewrite result {e} => {result.expr}"
            return some result
    return none

  inErasedSet (thm : GSimpTheorem) : Bool :=
    erased.contains thm.origin

def rewritePre : GSimproc := fun e => do
  let thms := (← getContext).gsimpTheorems
  if let some pre := thms.pre.find? (← getContext).relName then
    if let some r ← grewrite? e pre thms.erased (tag := "pre") then
      return .visit r
  return .continue

def rewritePost : GSimproc := fun e => do
  let thms := (← getContext).gsimpTheorems
  if let some post := thms.post.find? (← getContext).relName then
    if let some r ← grewrite? e post thms.erased (tag := "post") then
      return .visit r
  return .continue

abbrev Discharge := Expr → MetaM (Option Expr)

def mkMethods (discharge? : Discharge) : Methods := {
  pre        := rewritePre
  post       := rewritePost
  discharge?
}

end Mathlib.Tactic.GSimp
