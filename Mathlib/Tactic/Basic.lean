/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
import Lean
import Std
import Mathlib.Tactic.Cases

namespace Mathlib.Tactic
open Lean Parser.Tactic Elab Command Elab.Tactic Meta

syntax (name := «variables») "variables" (ppSpace bracketedBinder)* : command

@[command_elab «variables»] def elabVariables : CommandElab
  | `(variables%$pos $binders*) => do
    logWarningAt pos "'variables' has been replaced by 'variable' in lean 4"
    elabVariable (← `(variable%$pos $binders*))
  | _ => throwUnsupportedSyntax

/-- `lemma` means the same as `theorem`. It is used to denote "less important" theorems -/
syntax (name := lemma) declModifiers
  group("lemma " declId ppIndent(declSig) declVal Parser.Command.terminationSuffix) : command

/-- Implementation of the `lemma` command, by macro expansion to `theorem`. -/
@[macro «lemma»] def expandLemma : Macro := fun stx =>
  -- FIXME: this should be a macro match, but terminationSuffix is not easy to bind correctly.
  -- This implementation ensures that any future changes to `theorem` are reflected in `lemma`
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration

/-- The syntax `variable (X Y ... Z : Sort*)` creates a new distinct implicit universe variable
for each variable in the sequence. -/
elab "Sort*" : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  Elab.Term.levelMVarToParam (.sort u)

/-- The syntax `variable (X Y ... Z : Type*)` creates a new distinct implicit universe variable
`> 0` for each variable in the sequence. -/
elab "Type*" : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  Elab.Term.levelMVarToParam (.sort (.succ u))

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

/-- Function to help do the revert/intro pattern, running some code inside a context
where certain variables have been reverted before re-introing them.
It will push `FVarId` alias information into info trees for you according to a simple protocol.

- `fvarIds` is an array of `fvarIds` to revert. These are passed to
  `Lean.MVarId.revert` with `preserveOrder := true`, hence the function
  raises an error if they cannot be reverted in the provided order.
- `k` is given the goal with all the variables reverted and
  the array of reverted `FVarId`s, with the requested `FVarId`s at the beginning.
  It must return a tuple of a value, an array describing which `FVarIds` to link,
  and a mutated `MVarId`.

The `a : Array (Option FVarId)` array returned by `k` is interpreted in the following way.
The function will intro `a.size` variables, and then for each non-`none` entry we
create an FVar alias between it and the corresponding `intro`ed variable.
For example, having `k` return `fvars.map .some` causes all reverted variables to be
`intro`ed and linked.

Returns the value returned by `k` along with the resulting goal.
 -/
def _root_.Lean.MVarId.withReverted (mvarId : MVarId) (fvarIds : Array FVarId)
    (k : MVarId → Array FVarId → MetaM (α × Array (Option FVarId) × MVarId))
    (clearAuxDeclsInsteadOfRevert := false) : MetaM (α × MVarId) := do
  let (xs, mvarId) ← mvarId.revert fvarIds true clearAuxDeclsInsteadOfRevert
  let (r, xs', mvarId) ← k mvarId xs
  let (ys, mvarId) ← mvarId.introNP xs'.size
  mvarId.withContext do
    for x? in xs', y in ys do
      if let some x := x? then
        pushInfoLeaf (.ofFVarAliasInfo { id := y, baseId := x, userName := ← y.getUserName })
  return (r, mvarId)

/--
Replace the type of the free variable `fvarId` with `typeNew`.

If `checkDefEq = true` then throws an error if `typeNew` is not definitionally
equal to the type of `fvarId`. Otherwise this function assumes `typeNew` and the type
of `fvarId` are definitionally equal.

This function is the same as `Lean.MVarId.changeLocalDecl` but makes sure to push substitution
information into the infotree.
-/
def _root_.Lean.MVarId.changeLocalDecl' (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr)
    (checkDefEq := true) : MetaM MVarId := do
  mvarId.checkNotAssigned `changeLocalDecl
  let (_, mvarId) ← mvarId.withReverted #[fvarId] fun mvarId fvars => mvarId.withContext do
    let check (typeOld : Expr) : MetaM Unit := do
      if checkDefEq then
        unless ← isDefEq typeNew typeOld do
          throwTacticEx `changeLocalDecl mvarId
            m!"given type{indentExpr typeNew}\nis not definitionally equal to{indentExpr typeOld}"
    let finalize (targetNew : Expr) := do
      return ((), fvars.map .some, ← mvarId.replaceTargetDefEq targetNew)
    match ← mvarId.getType with
    | .forallE n d b bi => do check d; finalize (.forallE n typeNew b bi)
    | .letE n t v b ndep => do check t; finalize (.letE n typeNew v b ndep)
    | _ => throwTacticEx `changeLocalDecl mvarId "unexpected auxiliary target"
  return mvarId

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

Change is like `refine` in that every placeholder needs to be solved for by unification,
but you can use named placeholders and `?_` where you want `change` to create new goals.

The tactic `show e` is interchangeable with `change e`, where the pattern `e` is applied to
the main goal. -/
elab_rules : tactic
  | `(tactic| change $newType:term $[$loc:location]?) => do
    withLocation (expandOptLocation (Lean.mkOptionalNode loc))
      (atLocal := fun h ↦ do
        let hTy ← h.getType
        -- This is a hack to get the new type to elaborate in the same sort of way that
        -- it would for a `show` expression for the goal.
        let mvar ← mkFreshExprMVar none
        let (_, mvars) ← elabTermWithHoles
                          (← `(term | show $newType from $(← Term.exprToSyntax mvar))) hTy `change
        liftMetaTactic fun mvarId ↦ do
          return (← mvarId.changeLocalDecl' h (← inferType mvar)) :: mvars)
      (atTarget := evalTactic <| ← `(tactic| refine_lift show $newType from ?_))
      (failed := fun _ ↦ throwError "change tactic failed")

/--
`by_cases p` makes a case distinction on `p`,
resulting in two subgoals `h : p ⊢` and `h : ¬ p ⊢`.
-/
macro "by_cases " e:term : tactic =>
  `(tactic| by_cases $(mkIdent `h) : $e)

syntax "transitivity" (ppSpace colGt term)? : tactic
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
