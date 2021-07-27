/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.Tactic.Split
import Mathlib.Tactic.NoMatch
import Mathlib.Tactic.Block
import Lean.Elab.Command

open Lean Parser.Tactic Elab Command Elab.Tactic Meta

syntax (name := «variables») "variables" (bracketedBinder)* : command

@[commandElab «variables»] def elabVariables : CommandElab
  | `(variables%$pos $binders*) => do
    logWarningAt pos "'variables' has been replaced by 'variable' in lean 4"
    elabVariable (← `(variable%$pos $binders*))
  | _ => throwUnsupportedSyntax

macro mods:declModifiers "lemma" n:declId sig:declSig val:declVal : command =>
  `($mods:declModifiers theorem $n $sig $val)

macro "exFalso" : tactic => `(apply False.elim)

macro "_" : tactic => `({})

macro_rules | `(tactic| rfl) => `(tactic| exact Iff.rfl)

macro_rules
  | `(tactic| change $e:term) => `(tactic| show $e)

macro "sorry" : tactic => `(tactic| admit)

syntax "rwa " rwRuleSeq (location)? : tactic

macro_rules
  | `(tactic| rwa $rws:rwRuleSeq $[$loc:location]?) =>
    `(tactic| rw $rws:rwRuleSeq $[$loc:location]?; assumption)

macro "byCases " h:ident ":" e:term : tactic =>
  `(cases Decidable.em $e with | inl $h => ?pos | inr $h => ?neg)

set_option hygiene false in
macro "byCases " e:term : tactic =>
  `(cases Decidable.em $e with | inl h => ?pos | inr h => ?neg)

syntax "transitivity" (colGt term)? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| transitivity) => `(tactic| apply Nat.le_trans)
  | `(tactic| transitivity $e) => `(tactic| apply Nat.le_trans (m := $e))
set_option hygiene false in
macro_rules
  | `(tactic| transitivity) => `(tactic| apply Nat.lt_trans)
  | `(tactic| transitivity $e) => `(tactic| apply Nat.lt_trans (m := $e))

syntax (name := byContra) "byContra " (colGt ident)? : tactic
macro_rules
  | `(tactic| byContra) => `(tactic| (apply Decidable.byContradiction; intro))
  | `(tactic| byContra $e) => `(tactic| (apply Decidable.byContradiction; intro $e))
macro_rules
  | `(tactic| byContra) => `(tactic| (apply Classical.byContradiction; intro))
  | `(tactic| byContra $e) => `(tactic| (apply Classical.byContradiction; intro $e))

syntax (name := guardExprEq) "guardExprEq " term " := " term : tactic
@[tactic guardExprEq] def evalGuardExprEq : Lean.Elab.Tactic.Tactic := fun stx => do
  let r ← elabTerm stx[1] none
  let p ← elabTerm stx[3] none
  if not (r == p) then throwError m!"failed"

syntax (name := guardTarget) "guardTarget" term : tactic
@[tactic guardTarget] def evalGuardTarget : Lean.Elab.Tactic.Tactic := fun stx => do
  let r ← elabTerm stx[1] none
  let t ← getMainTarget
  if not (r == t) then throwError m!"target of main goal is {t}"

syntax (name := guardHyp) "guardHyp " ident (" : " term)? (" := " term)? : tactic
@[tactic guardHyp] unsafe def evalGuardHyp : Lean.Elab.Tactic.Tactic := fun stx =>
  match stx with
  | `(tactic| guardHyp $h $[: $ty]? $[:= $val]?) => do
    withMainContext do
      let fvarid ← getFVarId h
      let lDecl ←
        match (← getLCtx).find? fvarid with
        | none => throwError m!"hypothesis {h} not found"
        | some lDecl => lDecl
      match ty with
      | none    => ()
      | some p  =>
        let e ← elabTerm p none
        let hty ← instantiateMVars lDecl.type
        if not (e == hty) then throwError m!"hypothesis {h} has type {lDecl.type.ctorName} not {e.ctorName}"
      match lDecl.value?, val with
      | none, some _        => throwError m!"{h} is not a let binding"
      | some _, none        => throwError m!"{h} is a let binding"
      | some hval, some val =>
          let e ← elabTerm val none
          let hval ← instantiateMVars hval
          if not (e == hval) then throwError m!"hypothesis {h} has value {hval} not {e} {e == hval}"
      | none, none          => ()
  | _ => throwUnsupportedSyntax
