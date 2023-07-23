/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import Lean.Elab.Tactic.Rewrite
import Lean.Elab.BuiltinTerm

/-!
# `nth_rewrite` tactic

The tactic `nth_rewrite` and `nth_rw` are variants of `rewrite` and `rw` that only performs the
`n`th possible rewrite.

-/
namespace Mathlib.Tactic

open Lean Elab Tactic Meta Parser.Tactic

/-- Variant of `rewriteTarget` that allows to use `Occurrences`.

This def should be in Core. -/
def rewriteTarget' (stx : Syntax) (symm : Bool) (occs : Occurrences := Occurrences.all)
    (config : Rewrite.Config := { : Rewrite.Config }) : TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let r ← (← getMainGoal).rewrite (← getMainTarget) e symm occs config
    let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (mvarId' :: r.mvarIds)

/-- Variant of `rewriteLocalDecl` that allows to use `Occurrences`.

This def should be in Core. -/
def rewriteLocalDecl' (stx : Syntax) (symm : Bool) (fvarId : FVarId)
    (occs : Occurrences := Occurrences.all) (config : Rewrite.Config := { : Rewrite.Config }) :
    TacticM Unit := do
  Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    let localDecl ← fvarId.getDecl
    let rwResult ← (← getMainGoal).rewrite localDecl.type e symm occs config
    let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
    replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

/-- `nth_rewrite` is a variant of `rewrite` that only changes the nth occurrence of the expression
to be rewritten.

Note: The occurrences are counted beginning with `1` and not `0`, this is different than in
mathlib3. The translation will be handled by mathport. -/
syntax (name := nthRewriteSeq) "nth_rewrite" (config)? ppSpace num rwRuleSeq (location)? : tactic

@[inherit_doc nthRewriteSeq, tactic nthRewriteSeq] def evalNthRewriteSeq : Tactic := fun stx => do
  match stx with
  | `(tactic| nth_rewrite $[$_cfg]? $n $_rules $[$_loc]?) =>
    -- [TODO] `stx` should not be used directly, but the corresponding functions do not yet exist
    -- in Lean 4 core
    let cfg ← elabRewriteConfig stx[1]
    let loc := expandOptLocation stx[4]
    let occ := Occurrences.pos [n.getNat]
    withRWRulesSeq stx[0] stx[3] fun symm term => do
      withLocation loc
        (rewriteLocalDecl' term symm · occ cfg)
        (rewriteTarget' term symm occ cfg)
        (throwTacticEx `nth_rewrite · "did not find instance of the pattern in the current goal")
  | _ => throwUnsupportedSyntax

/--
`nth_rw` is like `nth_rewrite`, but also tries to close the goal by trying `rfl` afterwards.
-/
macro (name := nthRwSeq) "nth_rw" c:(config)? ppSpace n:num s:rwRuleSeq l:(location)? : tactic =>
  -- Note: This is a direct copy of `nth_rw` from core.
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (nth_rewrite $(c)? $n [$rs,*] $(l)?; with_annotate_state $rbrak
      (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported
