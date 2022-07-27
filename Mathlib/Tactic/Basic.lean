/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NoMatch
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

macro "exfalso" : tactic => `(apply False.elim)

macro "_" : tactic => `({})

/-- We allow the `rfl` tactic to also use `Iff.rfl`. -/
-- `rfl` was defined earlier in Lean4, at src/lean/init/tactics.lean
-- Later we want to allow `rfl` to use all relations marked with an attribute.
macro_rules | `(tactic| rfl) => `(tactic| exact Iff.rfl)

/-- `change` is a synonym for `show`,
and can be used to replace a goal with a definitionally equal one. -/
macro_rules
  | `(tactic| change $e:term) => `(tactic| show $e)

/-- `rwa` calls `rw`, then closes any remaining goals using `assumption`. -/
syntax "rwa " rwRuleSeq (location)? : tactic

macro_rules
  | `(tactic| rwa $rws:rwRuleSeq $[$loc:location]?) =>
    `(tactic| rw $rws:rwRuleSeq $[$loc:location]?; assumption)

/--
`by_cases h : p` makes a case distinction on `p`,
resulting in two subgoals `h : p ⊢` and `h : ¬ p ⊢`.
-/
macro "by_cases " h:ident ":" e:term : tactic =>
  `(cases Decidable.em $e with | inl $h => ?pos | inr $h => ?neg)

/--
`by_cases p` makes a case distinction on `p`,
resulting in two subgoals `h : p ⊢` and `h : ¬ p ⊢`.
-/
macro "by_cases " e:term : tactic =>
  `(by_cases $(mkIdent `h) : $e)

macro (name := classical) "classical" : tactic =>
  `(have em := Classical.propDecidable)

syntax "transitivity" (colGt term)? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| transitivity) => `(tactic| apply Nat.le_trans)
  | `(tactic| transitivity $e) => `(tactic| apply Nat.le_trans (m := $e))
set_option hygiene false in
macro_rules
  | `(tactic| transitivity) => `(tactic| apply Nat.lt_trans)
  | `(tactic| transitivity $e) => `(tactic| apply Nat.lt_trans (m := $e))

/--
The tactic `introv` allows the user to automatically introduce the variables of a theorem and
explicitly name the non-dependent hypotheses.
Any dependent hypotheses are assigned their default names.

Examples:
```
example : ∀ a b : Nat, a = b → b = a := by
  introv h,
  exact h.symm
```
The state after `introv h` is
```
a b : ℕ,
h : a = b
⊢ b = a
```

```
example : ∀ a b : Nat, a = b → ∀ c, b = c → a = c := by
  introv h₁ h₂,
  exact h₁.trans h₂
```
The state after `introv h₁ h₂` is
```
a b : ℕ,
h₁ : a = b,
c : ℕ,
h₂ : b = c
⊢ a = c
```
-/
syntax (name := introv) "introv " (colGt binderIdent)* : tactic
@[tactic introv] partial def evalIntrov : Tactic := fun stx => do
  match stx with
  | `(tactic| introv)                     => introsDep
  | `(tactic| introv $h:ident $hs:binderIdent*) =>
    evalTactic (← `(tactic| introv; intro $h:ident; introv $hs:binderIdent*))
  | `(tactic| introv _%$tk $hs:binderIdent*) =>
    evalTactic (← `(tactic| introv; intro _%$tk; introv $hs:binderIdent*))
  | _ => throwUnsupportedSyntax
where
  introsDep : TacticM Unit := do
    let t ← getMainTarget
    match t with
    | Expr.forallE _ _ e _ =>
      if e.hasLooseBVars then
        intro1PStep
        introsDep
    | _ => pure ()
  intro1PStep : TacticM Unit :=
    liftMetaTactic fun mvarId => do
      let (_, mvarId) ← mvarId.intro1P
      pure [mvarId]

/-- Try calling `assumption` on all goals; succeeds if it closes at least one goal. -/
macro "assumption'" : tactic => `(any_goals assumption)

/--
Like `exact`, but takes a list of terms and checks that all goals are discharged after the tactic.
-/
elab (name := exacts) "exacts" "[" hs:term,* "]" : tactic => do
  for stx in hs.getElems do
    evalTactic (← `(tactic| exact $stx))
  evalTactic (← `(tactic| done))

/-- Check syntactic equality of two expressions.
See also `guardExprEq` and `guardExprEq'` for testing
up to alpha equality and definitional equality. -/
elab (name := guardExprStrict) "guard_expr " r:term:51 " == " p:term : tactic => withMainContext do
  let r ← elabTerm r none
  let p ← elabTerm p none
  if not (r == p) then throwError "failed: {r} != {p}"

/-- Check the target agrees (syntactically) with a given expression.
See also `guardTarget` and `guardTarget'` for testing
up to alpha equality and definitional equality. -/
elab (name := guardTargetStrict) "guard_target" " == " r:term : tactic => withMainContext do
  let r ← elabTerm r none
  let t ← getMainTarget
  let t := t.consumeMData
  if not (r == t) then throwError m!"target of main goal is {t}, not {r}"

syntax (name := guardHyp) "guard_hyp " ident
  ((" : " <|> " :ₐ ") term)? ((" := " <|> " :=ₐ ") term)? : tactic

/-- Check that a named hypothesis has a given type and/or value.

`guardHyp h : t` checks the type up to syntactic equality,
while `guardHyp h :ₐ t` checks the type up to alpha equality.
`guardHyp h := v` checks value up to syntactic equality,
while `guardHyp h :=ₐ v` checks the value up to alpha equality. -/
-- TODO implement checking type or value up to alpha equality.
@[tactic guardHyp] def evalGuardHyp : Lean.Elab.Tactic.Tactic := fun stx =>
  match stx with
  | `(tactic| guard_hyp $h $[: $ty]? $[:= $val]?) => do
    withMainContext do
      let fvarid ← getFVarId h
      let lDecl ←
        match (← getLCtx).find? fvarid with
        | none => throwError m!"hypothesis {h} not found"
        | some lDecl => pure lDecl
      if let some p := ty then
        let e ← elabTerm p none
        let hty ← instantiateMVars lDecl.type
        let hty := hty.consumeMData
        if not (e == hty) then throwError m!"hypothesis {h} has type {hty}"
      match lDecl.value?, val with
      | none, some _        => throwError m!"{h} is not a let binding"
      | some _, none        => throwError m!"{h} is a let binding"
      | some hval, some val =>
          let e ← elabTerm val none
          let hval ← instantiateMVars hval
          let hval := hval.consumeMData
          if not (e == hval) then throwError m!"hypothesis {h} has value {hval}"
      | none, none          => pure ()
  | _ => throwUnsupportedSyntax

elab "match_target" t:term : tactic  => do
  withMainContext do
    let (val) ← elabTerm t (← inferType (← getMainTarget))
    if not (← isDefEq val (← getMainTarget)) then
      throwError "failed"

syntax (name := byContra) "by_contra" (ppSpace colGt ident)? : tactic
macro_rules
  | `(tactic| by_contra) => `(tactic| (match_target Not _; intro))
  | `(tactic| by_contra $e) => `(tactic| (match_target Not _; intro $e:ident))
macro_rules
  | `(tactic| by_contra) => `(tactic| (apply Decidable.byContradiction; intro))
  | `(tactic| by_contra $e) => `(tactic| (apply Decidable.byContradiction; intro $e:ident))
macro_rules
  | `(tactic| by_contra) => `(tactic| (apply Classical.byContradiction; intro))
  | `(tactic| by_contra $e) => `(tactic| (apply Classical.byContradiction; intro $e:ident))

/--
`iterate n tac` runs `tac` exactly `n` times.
`iterate tac` runs `tac` repeatedly until failure.

To run multiple tactics, one can do `iterate (tac₁; tac₂; ⋯)` or
```lean
iterate
  tac₁
  tac₂
  ⋯
```
-/
syntax "iterate" (ppSpace num)? ppSpace tacticSeq : tactic
macro_rules
  | `(tactic|iterate $seq:tacticSeq) =>
    `(tactic|try ($seq:tacticSeq); iterate $seq:tacticSeq)
  | `(tactic|iterate $n $seq:tacticSeq) =>
    match n.1.toNat with
    | 0 => `(tactic| skip)
    | n+1 => `(tactic|($seq:tacticSeq); iterate $(quote n) $seq:tacticSeq)

partial def repeat'Aux (seq : Syntax) : List MVarId → TacticM Unit
| []    => pure ()
| g::gs => do
    try
      let subgs ← evalTacticAt seq g
      appendGoals subgs
      repeat'Aux seq (subgs ++ gs)
    catch _ =>
      repeat'Aux seq gs

elab "repeat' " seq:tacticSeq : tactic => do
  let gs ← getGoals
  repeat'Aux seq gs

elab "any_goals " seq:tacticSeq : tactic => do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  let mut anySuccess := false
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        evalTactic seq
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
        anySuccess := true
      catch _ =>
        mvarIdsNew := mvarIdsNew.push mvarId
  if not anySuccess then
    throwError "failed on all goals"
  setGoals mvarIdsNew.toList

elab "fapply " e:term : tactic =>
  evalApplyLikeTactic (MVarId.apply (cfg := {newGoals := ApplyNewGoals.all})) e

elab "eapply " e:term : tactic =>
  evalApplyLikeTactic (MVarId.apply (cfg := {newGoals := ApplyNewGoals.nonDependentOnly})) e

/--
Tries to solve the goal using a canonical proof of `True`, or the `rfl` tactic.
Unlike `trivial` or `trivial'`, does not use the `contradiction` tactic.
-/
macro (name := triv) "triv" : tactic =>
  `(tactic| first | exact trivial | rfl | fail "triv tactic failed")

/-- This tactic clears all auxiliary declarations from the context. -/
elab (name := clearAuxDecl) "clear_aux_decl" : tactic => withMainContext do
  let mut g ← getMainGoal
  for ldec in ← getLCtx do
    if ldec.isAuxDecl then
      g ← g.tryClear ldec.fvarId
  replaceMainGoal [g]
