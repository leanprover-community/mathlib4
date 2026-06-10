/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep
public meta import Lean.Meta.Tactic.Generalize
public meta import Lean.Elab.Tactic.Induction
public meta import Lean.Elab.Tactic.RCases
import all Lean.Elab.Tactic.RCases

/-!
# Overwritten core tactics

This file overwrites the `obtain` and `rcases` tactics in order to only unfold reducible constants
when matching. `obtain!` and `rcases!` are added for backwards compatability.
-/

meta section

open Lean Meta Elab Parser.Tactic
namespace Mathlib.Tactic

open Tactic.RCases in
/-- Version of `Lean.Elab.Tactic.RCases.rcases` that uses `withReducible`
when calling `rcasesContinue`.  -/
def rcases (tgts : Array (Option Ident × Syntax))
  (pat : RCasesPatt) (g : MVarId) : TermElabM (List MVarId) := Term.withSynthesize do
  let pats ← match tgts.size with
  | 0 => return [g]
  | 1 => pure [pat]
  | _ => pure (processConstructor pat.ref (tgts.map fun _ => {}) false 0 pat.asTuple.2).2
  let (pats, args) := Array.unzip <|← tgts.zipWithM (bs := pats.toArray) fun (hName?, tgt) pat => do
    let (pat, ty) ← match pat with
    | .typed ref pat ty => withRef ref do
      let ty ← Term.elabType ty
      pure (.typed ref pat (← Term.exprToSyntax ty), some ty)
    | _ => pure (pat, none)
    let expr ← Term.ensureHasType ty (← Term.elabTerm tgt ty)
    pure (pat, { expr, xName? := pat.name?, hName? := hName?.map (·.getId) : GeneralizeArg })
  let (vs, hs, g) ← generalizeExceptFVar g args
  let toTag := tgts.filterMap (·.1) |>.zip hs
  Term.synthesizeSyntheticMVarsNoPostponing
  let gs ← withReducible <|
    rcasesContinue g {} #[] #[] (pats.zip vs).toList (finish (toTag := toTag))
  pure gs.toList


@[inherit_doc rcases]
syntax (name := rcases!Stx) "rcases! " elimTarget,* (" with " rcasesPatLo)? : tactic

@[tactic rcases!Stx]
public def evalRCases! : Tactic.Tactic := Tactic.RCases.evalRCases

open Tactic RCases in
@[tactic rcases]
public def evalRCases : Tactic := fun stx => do
  match stx with
  | `(tactic| rcases%$tk $tgts,* $[with $pat?]?) =>
    let pat ← match pat? with
      | some pat => RCasesPatt.parse pat
      | none     => pure $ RCasesPatt.tuple tk []
    let tgts ← tgts.getElems.mapM fun tgt => do
      let view ← mkTargetView tgt
      pure (view.hIdent?, view.term)
    let g ← getMainGoal
    g.withContext do replaceMainGoal (← rcases tgts pat g)
  | _ => throwUnsupportedSyntax

@[inherit_doc obtain]
syntax (name := obtain!Stx)
  "obtain!" (ppSpace rcasesPatMed)? (" : " term)? (" := " term,+)? : tactic

@[tactic obtain!Stx]
public def evalObtain! : Tactic.Tactic := Tactic.RCases.evalObtain

open Tactic RCases in
@[tactic obtain]
public def evalObtain : Tactic := fun stx => do
  match stx with
  | `(tactic| obtain%$tk $[$pat?:rcasesPatMed]? $[: $ty?]? $[:= $val?,*]?) =>
    let pat? ← liftM <| pat?.mapM RCasesPatt.parse
    if let some val := val? then
      let pat  := pat?.getD (RCasesPatt.one tk `_)
      let pat  := pat.typed? tk ty?
      let tgts := val.getElems.map fun val => (none, val.raw)
      let g ← getMainGoal
      g.withContext do replaceMainGoal (← rcases tgts pat g)
    else if let some ty := ty? then
      let pat := pat?.getD (RCasesPatt.one tk `this)
      let g ← getMainGoal
      g.withContext do replaceMainGoal (← RCases.obtainNone pat ty g)
    else
      throwError "\
        `obtain` requires either an expected type or a value.\n\
        usage: `obtain ⟨patt⟩? : type (:= val)?` or `obtain ⟨patt⟩? (: type)? := val`"
  | _ => throwUnsupportedSyntax

end Mathlib.Tactic
