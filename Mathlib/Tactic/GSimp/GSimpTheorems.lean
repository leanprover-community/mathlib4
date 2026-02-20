/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.GCongr.Core

meta import all Lean.Meta.Tactic.Simp.SimpTheorems

/-!
# generalized rewriting

This module implements the generalized rewriting similar to how `simp` is implemented,
hence this will be called the `gsimp` tactic.
-/

public meta section

namespace Mathlib.Tactic.GSimp
open Lean Meta

abbrev GSimpTheoremKey := DiscrTree.Key

/--
The fields `levelParams` and `proof` are used to encode the proof of the simp theorem.
If the `proof` is a global declaration `c`, we store `Expr.const c []` at `proof` without the
universe levels, and `levelParams` is set to `#[]`
When using the lemma, we create fresh universe metavariables.
Motivation: most simp theorems are global declarations,
and this approach is faster and saves memory.

The field `levelParams` is not empty only when we elaborate an expression provided by the user,
and it contains universe metavariables.
Then, we use `abstractMVars` to abstract the universe metavariables and create new fresh universe
parameters that are stored at the field `levelParams`.
-/
structure GSimpTheorem where
  relation : Name
  inv : Bool
  keys : Array GSimpTheoremKey := #[]
  /--
  It stores universe parameter names for universe polymorphic proofs.
  Recall that it is non-empty only when we elaborate an expression provided by the user.
  When `proof` is just a constant,
  we can use the universe parameter names stored in the declaration.
  -/
  levelParams : Array Name := #[]
  proof : Expr
  priority : Nat  := eval_prio default
  post : Bool := true
  /-- `perm` is true if lhs and rhs are identical modulo permutation of variables. -/
  perm : Bool := false
  /--
  `origin` is mainly relevant for producing trace messages.
  It is also viewed an `id` used to "erase" `gsimp` theorems from `GSimpTheorems`.
  -/
  origin : Origin
  deriving Inhabited

abbrev GSimpTheoremTree := NameMap (DiscrTree GSimpTheorem)

/--
The theorems in a gsimp set.
-/
structure GSimpTheorems where
  pre : GSimpTheoremTree := {}
  post : GSimpTheoremTree := {}
  lemmaNames : PHashSet Origin := {}
  /--
  Constants (and let-declaration `FVarId`) to unfold.
  When `zetaDelta := false`, the simplifier will expand a let-declaration if it is in this set.
  -/
  toUnfold : PHashSet Name := {}
  erased : PHashSet Origin := {}
  toUnfoldThms : PHashMap Name (Array Name) := {}
  deriving Inhabited

def ppGSimpTheorem {m} [Monad m] [MonadEnv m] [MonadError m] (s : GSimpTheorem) :
    m MessageData := do
  let perm := if s.perm then ":perm" else ""
  let name ← ppOrigin s.origin
  let prio := m!":{s.priority}"
  return name ++ prio ++ perm

instance : BEq GSimpTheorem where
  beq e₁ e₂ := e₁.proof == e₂.proof

private def mkGSimpTheoremKeys (type : Expr) (inv : Bool) (noIndexAtArgs : Bool) :
    MetaM (Name × Array GSimpTheoremKey × Bool) := do
  withNewMCtxDepth do
    let (_, _, type) ← forallMetaTelescopeReducing type
    let type := type.cleanupAnnotations
    match GCongr.getRel type with
    | some (relName, lhs, rhs) =>
      let (lhs, rhs) := if inv then (rhs, lhs) else (lhs, rhs)
      pure (relName, ← DiscrTree.mkPath lhs noIndexAtArgs, ← isPerm lhs rhs)
    | none => throwError "Unexpected kind of gsimp theorem{indentExpr type}"

private def mkGSimpTheoremCore (origin : Origin) (e : Expr) (levelParams : Array Name) (inv : Bool)
    (proof : Expr) (post : Bool) (prio : Nat) (noIndexAtArgs : Bool) : MetaM GSimpTheorem := do
  assert! origin != .fvar ⟨.anonymous⟩
  let type ← instantiateMVars (← inferType e)
  let (relation, keys, perm) ← mkGSimpTheoremKeys type inv noIndexAtArgs
  return { relation, inv, origin, keys, perm, post, levelParams, proof, priority := prio }

/-- Creates a `GSimpTheorem` from a global theorem. -/
def mkGSimpTheoremFromConst (declName : Name) (post := true) (inv := false)
    (prio : Nat := eval_prio default) : MetaM GSimpTheorem := do
  let cinfo ← getConstVal declName
  let us := cinfo.levelParams.map mkLevelParam
  let origin := .decl declName post inv
  withSimpGlobalConfig do withoutExporting do
    mkGSimpTheoremCore origin (mkConst declName us) #[] inv (mkConst declName)
      post prio (noIndexAtArgs := false)

def GSimpTheorem.getValue (gsimpThm : GSimpTheorem) : MetaM Expr := do
  if gsimpThm.proof.isConst && gsimpThm.levelParams.isEmpty then
    let info ← getConstVal gsimpThm.proof.constName!
    if info.levelParams.isEmpty then
      return gsimpThm.proof
    else
      return gsimpThm.proof.updateConst! (← info.levelParams.mapM fun _ => mkFreshLevelMVar)
  else
    let us ← gsimpThm.levelParams.mapM fun _ => mkFreshLevelMVar
    return gsimpThm.proof.instantiateLevelParamsArray gsimpThm.levelParams us

def mkGSimpTheoremFromExpr (id : Origin) (levelParams : Array Name) (proof : Expr) (inv := false)
    (post := true) (prio : Nat := eval_prio default) :
    MetaM GSimpTheorem := do
  if proof.isConst then
    -- Recall that we use `simpGlobalConfig` for processing global declarations.
    mkGSimpTheoremFromConst proof.constName! post inv prio
  else
    withSimpGlobalConfig do
      withReducible do
        mkGSimpTheoremCore id proof levelParams inv proof post prio (noIndexAtArgs := true)





partial def GSimpTheorems.eraseCore (d : GSimpTheorems) (thmId : Origin) : GSimpTheorems :=
  let d := { d with erased := d.erased.insert thmId, lemmaNames := d.lemmaNames.erase thmId }
  if let .decl declName .. := thmId then
    let d := { d with toUnfold := d.toUnfold.erase declName }
    if let some thms := d.toUnfoldThms.find? declName then
      let dummy := true
      thms.foldl (init := d) (eraseCore · <| .decl · dummy (inv := false))
    else
      d
  else
    d

private def eraseIfExists (d : GSimpTheorems) (thmId : Origin) : GSimpTheorems :=
  if d.lemmaNames.contains thmId then
    d.eraseCore thmId
  else
    d

/--
If `e` is a backwards theorem `← thm`, we must ensure the forward theorem is erased
from `d`. See issue #4290
-/
private def eraseFwdIfBwd (d : GSimpTheorems) (e : GSimpTheorem) : GSimpTheorems :=
  if let some converseOrigin := e.origin.converse then
    eraseIfExists d converseOrigin
  else
    d

def GSimpTheorems.unerase (d : GSimpTheorems) (thmId : Origin) : GSimpTheorems :=
  { d with erased := d.erased.erase thmId }

def GSimpTheorems.addGSimpTheorem (d : GSimpTheorems) (e : GSimpTheorem) :
    GSimpTheorems :=
  -- Erase the converse, if it exists
  let d := eraseFwdIfBwd d e
  if e.post then
    { d with
      post := d.post.modify e.relation (·.insertKeyValue e.keys e)
      lemmaNames := updateLemmaNames d.lemmaNames }
  else
    { d with
      pre := d.pre.modify e.relation (·.insertKeyValue e.keys e)
      lemmaNames := updateLemmaNames d.lemmaNames }
where
  updateLemmaNames (s : PHashSet Origin) : PHashSet Origin :=
    s.insert e.origin

end Mathlib.Tactic.GSimp
