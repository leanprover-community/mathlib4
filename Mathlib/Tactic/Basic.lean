/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
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

macro "by_cases " h:ident ":" e:term : tactic =>
  `(cases Decidable.em $e with | inl $h => ?pos | inr $h => ?neg)

set_option hygiene false in
macro "by_cases " e:term : tactic =>
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
syntax (name := introv) "introv " (colGt ident)* : tactic
@[tactic introv] partial def evalIntrov : Tactic := fun stx => do
  match stx with
  | `(tactic| introv)                     => introsDep
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
elab (name := guardExprStrict) "guardExpr " r:term:51 " == " p:term : tactic => withMainContext do
  let r ← elabTerm r none
  let p ← elabTerm p none
  if not (r == p) then throwError "failed: {r} != {p}"

/-- Check the target agrees (syntactically) with a given expression.
See also `guardTarget` and `guardTarget'` for testing
up to alpha equality and definitional equality. -/
elab (name := guardTargetStrict) "guardTarget" " == " r:term : tactic => withMainContext do
  let r ← elabTerm r none
  let t ← getMainTarget
  let t ← t.consumeMData
  if not (r == t) then throwError m!"target of main goal is {t}, not {r}"

syntax (name := guardHyp) "guardHyp " ident
  ((" : " <|> " :ₐ ") term)? ((" := " <|> " :=ₐ ") term)? : tactic

/-- Check that a named hypothesis has a given type and/or value.

`guardHyp h : t` checks the type up to syntactic equality,
while `guardHyp h :ₐ t` checks the type up to alpha equality.
`guardHyp h := v` checks value up to syntactic equality,
while `guardHyp h :=ₐ v` checks the value up to alpha equality. -/
-- TODO implement checking type or value up to alpha equality.
@[tactic guardHyp] def evalGuardHyp : Lean.Elab.Tactic.Tactic := fun stx =>
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
        let hty ← hty.consumeMData
        if not (e == hty) then throwError m!"hypothesis {h} has type {hty}"
      match lDecl.value?, val with
      | none, some _        => throwError m!"{h} is not a let binding"
      | some _, none        => throwError m!"{h} is a let binding"
      | some hval, some val =>
          let e ← elabTerm val none
          let hval ← instantiateMVars hval
          let hval ← hval.consumeMData
          if not (e == hval) then throwError m!"hypothesis {h} has value {hval}"
      | none, none          => ()
  | _ => throwUnsupportedSyntax

elab "matchTarget" t:term : tactic  => do
  withMainContext do
    let (val) ← elabTerm t (← inferType (← getMainTarget))
    if not (← isDefEq val (← getMainTarget)) then
      throwError "failed"

syntax (name := byContra) "byContra " (colGt ident)? : tactic
macro_rules
  | `(tactic| byContra) => `(tactic| (matchTarget Not _; intro))
  | `(tactic| byContra $e) => `(tactic| (matchTarget Not _; intro $e))
macro_rules
  | `(tactic| byContra) => `(tactic| (apply Decidable.byContradiction; intro))
  | `(tactic| byContra $e) => `(tactic| (apply Decidable.byContradiction; intro $e))
macro_rules
  | `(tactic| byContra) => `(tactic| (apply Classical.byContradiction; intro))
  | `(tactic| byContra $e) => `(tactic| (apply Classical.byContradiction; intro $e))

macro (name := «sorry») "sorry" : tactic => `(exact sorry)

section iterate

variable [Monad m] [MonadExcept e m]

/--
`iterate_at_most n t` runs the tactic `t` at most `n` times, or until failure,
whichever comes first.
Always succeeds, and returns at list of the succesful results.
-/
def iterate_at_most : Nat → m α → m (List α)
| 0,       t => []
| (n + 1), t => do
  try
    (←t) :: (←iterate_at_most n t)
  catch _ =>
    []

/--
`iterate_at_most' n t` runs the tactic `t` at most `n` times, or until failure,
whichever comes first, and always succeeds.
-/
def iterate_at_most' (n : Nat) (t : m α) : m Unit := do
  _ ← iterate_at_most n t

/--
`iterate_exactly n t` runs the tactic `t` at exactly `n` times.
Fails if any iteration fails, and otherwise returns a list of the `n` successful results.
-/
def iterate_exactly : Nat → m α → m (List α)
| 0, t     => []
| (n+1), t => do (←t) :: (←iterate_exactly n t)

/--
`iterate_exactly n t` runs the tactic `t` at exactly `n` times.
Fails if any iteration fails.
-/
def iterate_exactly' (n : Nat) (t : m α) : m Unit := do
  _ ← iterate_exactly n t

/--
`iterate n { ... }` runs the tactic block exactly `n` times.
`iterate { ... }` runs the tactic block repeatedly until failure.
-/
syntax (name := iterate) "iterate" (num)? ppSpace tacticSeq : tactic

elab_rules : tactic
| `(tactic| iterate $seq:tacticSeq) =>
   iterate_at_most' 10000 (evalTactic seq)
| `(tactic| iterate $n $seq:tacticSeq) =>
   iterate_exactly' n.toNat (evalTactic seq)


/-!
We could alternatively implement `iterate` as
```
syntax "iterate " (num)? ppSpace tacticSeq : tactic
macro_rules
  | `(tactic|iterate $seq:tacticSeq) =>
    `(tactic|try ($seq:tacticSeq); iterate $seq:tacticSeq)
  | `(tactic|iterate $n $seq:tacticSeq) =>
    match n.toNat with
    | 0 => `(tactic| skip)
    | n+1 => `(tactic|($seq:tacticSeq); iterate $(quote n) $seq:tacticSeq)
```
and some may find this more idiomatic.

However an implementation like this does not provide the "plumbing" tactics
(i.e. for `iterate`, the tactics that collect the list of results of the underlying tactic).
Thus for now we prefer to first implement the plumbing, then connect the porcelain to the plumbing.

For now, this note serves to preserve an example of the "porcelain-only" style,
which is useful for writing one-off tactics.
-/

end iterate

partial def repeat'Aux (seq : Syntax) : List MVarId → TacticM Unit
| []    => ()
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

elab "anyGoals " seq:tacticSeq : tactic => do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  let mut anySuccess := false
  for mvarId in mvarIds do
    unless (← isExprMVarAssigned mvarId) do
      setGoals [mvarId]
      try
        evalTactic seq
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
        anySuccess := true
      catch ex =>
        mvarIdsNew := mvarIdsNew.push mvarId
  if not anySuccess then
    throwError "failed on all goals"
  setGoals mvarIdsNew.toList

/--
`workOnGoal n { tac }` creates a block scope for the `n`-th goal (indexed from zero),
but does not require that the goal be solved at the end of the block
(any resulting subgoals are inserted back into the list of goals, replacing the `n`-th goal).
-/
elab (name := workOnGoal) "workOnGoal " n:num ppSpace seq:tacticSeq : tactic => do
  let goals ← getGoals
  let n := n.toNat
  if h : n < goals.length then
    setGoals [goals.get n h]
    evalTactic seq
    setGoals (goals.take n ++ (← getUnsolvedGoals) ++ goals.drop (n+1))
  else
    throwError "not enough goals"
