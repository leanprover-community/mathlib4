/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean
import Std
import Mathlib.Tactic.Cases

namespace Mathlib.Tactic
open Lean Parser.Tactic Elab Command Elab.Tactic Meta

syntax (name := «variables») "variables" (bracketedBinder)* : command

@[command_elab «variables»] def elabVariables : CommandElab
  | `(variables%$pos $binders*) => do
    logWarningAt pos "'variables' has been replaced by 'variable' in lean 4"
    elabVariable (← `(variable%$pos $binders*))
  | _ => throwUnsupportedSyntax

/-- `lemma` means the same as `theorem`. It is used to denote "less important" theorems -/
syntax (name := lemma)
  declModifiers group("lemma" declId declSig declVal Parser.Command.terminationSuffix) : command

/-- Implementation of the `lemma` command, by macro expansion to `theorem`. -/
@[macro «lemma»] def expandLemma : Macro := fun stx =>
  -- FIXME: this should be a macro match, but terminationSuffix is not easy to bind correctly.
  -- This implementation ensures that any future changes to `theorem` are reflected in `lemma`
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration

/-- `change` can be used to replace the main goal or its local
variables with definitionally equal ones.

For example, if `n : ℕ` and the current goal is `⊢ n + 2 = 2`, then
```lean
change _ + 1 = _
```
changes the goal to `⊢ n + 1 + 1 = 2`. The tactic also applies to the local context.
If `h : n + 2 = 2` and `h' : n + 3 = 4` are in the local context, then
```lean
change _ + 1 = _ at h h'
```
changes their types to be `h : n + 1 + 1 = 2` and `h' : n + 2 + 1 = 4`.

If the tactic `show e` applies to the main goal, then it is interchangeable with `change e`. -/
elab_rules : tactic
  | `(tactic| change $newType:term $[$loc:location]?) => do
    withLocation (expandOptLocation (Lean.mkOptionalNode loc))
      (atLocal := fun h ↦ do
        let hTy ← h.getType
        let (e, gs) ← elabTermWithHoles newType none (← getMainTag) (allowNaturalHoles := true)
        liftMetaTactic fun mvarId ↦ do
          unless ← withAssignableSyntheticOpaque (isDefEq e hTy) do
            let h' ← h.getUserName
            throwTacticEx `change mvarId
              m!"given type{indentExpr e}\nis not definitionally equal at {h'} to{indentExpr hTy}"
          return (← mvarId.changeLocalDecl h e) :: gs)
      (atTarget := withMainContext do
        let tgt ← getMainTarget
        let (e, gs) ← elabTermWithHoles newType none (← getMainTag) (allowNaturalHoles := true)
        liftMetaTactic fun mvarId ↦ do
          unless ← withAssignableSyntheticOpaque (isDefEq e tgt) do
            throwTacticEx `change mvarId
              m!"given type{indentExpr e}\nis not definitionally equal to{indentExpr tgt}"
          return (← mvarId.change e) :: gs)
      (failed := fun _ ↦ throwError "change tactic failed")

/--
`by_cases p` makes a case distinction on `p`,
resulting in two subgoals `h : p ⊢` and `h : ¬ p ⊢`.
-/
macro "by_cases " e:term : tactic =>
  `(tactic| by_cases $(mkIdent `h) : $e)

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
@[tactic introv] partial def evalIntrov : Tactic := fun stx ↦ do
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
    liftMetaTactic fun goal ↦ do
      let (_, goal) ← goal.intro1P
      pure [goal]

/-- Try calling `assumption` on all goals; succeeds if it closes at least one goal. -/
macro "assumption'" : tactic => `(tactic| any_goals assumption)

elab "match_target" t:term : tactic  => do
  withMainContext do
    let (val) ← elabTerm t (← inferType (← getMainTarget))
    if not (← isDefEq val (← getMainTarget)) then
      throwError "failed"

/-- This tactic clears all auxiliary declarations from the context. -/
elab (name := clearAuxDecl) "clear_aux_decl" : tactic => withMainContext do
  let mut g ← getMainGoal
  for ldec in ← getLCtx do
    if ldec.isAuxDecl then
      g ← g.tryClear ldec.fvarId
  replaceMainGoal [g]
