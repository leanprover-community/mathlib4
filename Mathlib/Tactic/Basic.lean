/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
import Lean
import Std
import Mathlib.Tactic.PPWithUniv
import Mathlib.Tactic.ExtendDoc
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

set_option autoImplicit true

namespace Mathlib.Tactic
open Lean Parser.Tactic Elab Command Elab.Tactic Meta

syntax (name := «variables») "variables" (ppSpace bracketedBinder)* : command

@[command_elab «variables»] def elabVariables : CommandElab
  | `(variables%$pos $binders*) => do
    logWarningAt pos "'variables' has been replaced by 'variable' in lean 4"
    elabVariable (← `(variable%$pos $binders*))
  | _ => throwUnsupportedSyntax

/-- Given two arrays of `FVarId`s, one from an old local context and the other from a new local
context, pushes `FVarAliasInfo`s into the info tree for corresponding pairs of `FVarId`s.
Recall that variables linked this way should be considered to be semantically identical.

The effect of this is, for example, the unused variable linter will see that variables
from the first array are used if corresponding variables in the second array are used. -/
def pushFVarAliasInfo [Monad m] [MonadInfoTree m]
    (oldFVars newFVars : Array FVarId) (newLCtx : LocalContext) : m Unit := do
  for old in oldFVars, new in newFVars do
    if old != new then
      let decl := newLCtx.get! new
      pushInfoLeaf (.ofFVarAliasInfo { id := new, baseId := old, userName := decl.userName })

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
syntax (name := introv) "introv " (ppSpace colGt binderIdent)* : tactic
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

elab "match_target " t:term : tactic => do
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

/-- Clears the value of the local definition `fvarId`. Ensures that the resulting goal state
is still type correct. Throws an error if it is a local hypothesis without a value. -/
def _root_.Lean.MVarId.clearValue (mvarId : MVarId) (fvarId : FVarId) : MetaM MVarId := do
  mvarId.checkNotAssigned `clear_value
  let tag ← mvarId.getTag
  let (_, mvarId) ← mvarId.withReverted #[fvarId] fun mvarId' fvars => mvarId'.withContext do
    let tgt ← mvarId'.getType
    unless tgt.isLet do
      mvarId.withContext <|
        throwTacticEx `clear_value mvarId m!"{Expr.fvar fvarId} is not a local definition"
    let tgt' := Expr.forallE tgt.letName! tgt.letType! tgt.letBody! .default
    unless ← isTypeCorrect tgt' do
      mvarId.withContext <|
        throwTacticEx `clear_value mvarId
          m!"cannot clear {Expr.fvar fvarId}, the resulting context is not type correct"
    let mvarId'' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
    mvarId'.assign <| .app mvarId'' tgt.letValue!
    return ((), fvars.map .some, mvarId''.mvarId!)
  return mvarId

/-- `clear_value n₁ n₂ ...` clears the bodies of the local definitions `n₁, n₂ ...`, changing them
into regular hypotheses. A hypothesis `n : α := t` is changed to `n : α`.

The order of `n₁ n₂ ...` does not matter, and values will be cleared in reverse order of
where they appear in the context. -/
elab (name := clearValue) "clear_value" hs:(ppSpace colGt term:max)+ : tactic => do
  let fvarIds ← getFVarIds hs
  let fvarIds ← withMainContext <| sortFVarIds fvarIds
  for fvarId in fvarIds.reverse do
    withMainContext do
      let mvarId ← (← getMainGoal).clearValue fvarId
      replaceMainGoal [mvarId]

attribute [pp_with_univ] ULift PUnit PEmpty
