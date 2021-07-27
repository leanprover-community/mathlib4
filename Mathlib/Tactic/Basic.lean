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

syntax (name := introv) "introv " (colGt ident)* : tactic
@[tactic introv] partial def evalIntrov : Tactic := fun stx => do
  match stx with
  | `(tactic| introv)                    => introsDep
  | `(tactic| introv $h:ident $hs:ident*) => evalTactic (← `(tactic| introv; intro $h:ident; introv $hs:ident*))
  | _ => throwUnsupportedSyntax
where
  introsDep : TacticM Unit := do
    let t ← getMainTarget
    match t with
    | Expr.forallE _ _ e _ =>
      if e.hasLooseBVars then
        intro1PStep
        introsDep
    | _ => ()
  intro1PStep : TacticM Unit :=
    liftMetaTactic fun mvarId => do
      let (_, mvarId) ← Meta.intro1P mvarId
      pure [mvarId]

syntax (name := byContra) "byContra " (colGt ident)? : tactic
macro_rules
  | `(tactic| byContra) => `(tactic| (apply Decidable.byContradiction; intro))
  | `(tactic| byContra $e) => `(tactic| (apply Decidable.byContradiction; intro $e))
macro_rules
  | `(tactic| byContra) => `(tactic| (apply Classical.byContradiction; intro))
  | `(tactic| byContra $e) => `(tactic| (apply Classical.byContradiction; intro $e))

elab "guardExprEq " r:term " := " p:term : tactic => do
  let r ← elabTerm r none
  let p ← elabTerm p none
  if not (r == p) then throwError "failed: {r} != {p}"

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
      if let some p ← ty then
        let e ← elabTerm p none
        let hty ← instantiateMVars lDecl.type
        if not (e == hty) then throwError m!"hypothesis {h} has type {lDecl.type}"
      match lDecl.value?, val with
      | none, some _        => throwError m!"{h} is not a let binding"
      | some _, none        => throwError m!"{h} is a let binding"
      | some hval, some val =>
          let e ← elabTerm val none
          let hval ← instantiateMVars hval
          if not (e == hval) then throwError m!"hypothesis {h} has value {hval}"
      | none, none          => ()
  | _ => throwUnsupportedSyntax
