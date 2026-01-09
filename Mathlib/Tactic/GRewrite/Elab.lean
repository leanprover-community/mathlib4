/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer, Mario Carneiro, Heather Macbeth, Jovan Gerbscheid
-/
module

public meta import Mathlib.Tactic.GRewrite.Core
public import Mathlib.Tactic.GRewrite.Core

/-!

# The generalized rewriting tactic

This file defines the tactics that use the backend defined in `Mathlib.Tactic.GRewrite.Core`:
- `grewrite`
- `grw`
- `apply_rw`
- `nth_grewrite`
- `nth_grw`

-/

public meta section

namespace Mathlib.Tactic

open Lean Meta Elab Parser Tactic

/-- Apply the `grewrite` tactic to the current goal. -/
def grewriteTarget (stx : Syntax) (symm : Bool) (config : GRewrite.Config) : TacticM Unit := do
  let goal ← getMainGoal
  Term.withSynthesize <| goal.withContext do
    let e ← elabTerm stx none true
    if e.hasSyntheticSorry then
      throwAbortTactic
    let goal ← getMainGoal
    let target ← goal.getType
    let r ← goal.grewrite target e (forwardImp := false) (symm := symm) (config := config)
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar r.eNew (← goal.getTag)
    goal.assign (mkApp r.impProof mvarNew)
    replaceMainGoal (mvarNew.mvarId! :: r.mvarIds)

/-- Apply the `grewrite` tactic to a local hypothesis. -/
def grewriteLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId) (config : GRewrite.Config) :
    TacticM Unit := withMainContext do
  -- Note: we cannot execute `replace` inside `Term.withSynthesize`.
  -- See issues https://github.com/leanprover-community/mathlib4/issues/2711 and https://github.com/leanprover-community/mathlib4/issues/2727.
  let goal ← getMainGoal
  let r ← Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    if e.hasSyntheticSorry then
      throwAbortTactic
    let localDecl ← fvarId.getDecl
    goal.grewrite localDecl.type e (forwardImp := true) (symm := symm) (config := config)
  let proof := .app (r.impProof) (.fvar fvarId)
  let { mvarId, .. } ← goal.replace fvarId proof r.eNew
  replaceMainGoal (mvarId :: r.mvarIds)

/-- Function elaborating `GRewrite.Config`. -/
declare_config_elab elabGRewriteConfig GRewrite.Config

/--
`grewrite [e]` is like `grw [e]`, but it doesn't try to close the goal with `rfl`.
This is analogous to `rw` and `rewrite`, where `rewrite` doesn't try to close the goal with `rfl`.
-/
syntax (name := grewriteSeq) "grewrite" optConfig rwRuleSeq (location)? : tactic

@[tactic grewriteSeq, inherit_doc grewriteSeq] def evalGRewriteSeq : Tactic := fun stx => do
  let cfg ← elabGRewriteConfig stx[1]
  let loc := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (grewriteLocalDecl term symm · cfg)
      (grewriteTarget term symm cfg)
      (throwTacticEx `grewrite · "did not find instance of the pattern in the current goal")

/--
`grw [e]` works just like `rw [e]`, but `e` can be a relation other than `=` or `↔`.

For example:

```lean
variable {a b c d n : ℤ}

example (h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  grw [h₁, h₂]

example (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  grw [h]

example (h₁ : a ∣ b) (h₂ : b ∣ a ^ 2 * c) : a ∣ b ^ 2 * c := by
  grw [h₁] at *
  exact h₂
```

To replace the RHS with the LHS of the given relation, use the `←` notation (just like in `rw`):

```
example (h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  grw [← h₂, ← h₁]
```

The strict inequality `a < b` is turned into the non-strict inequality `a ≤ b` to rewrite with it.
A future version of `grw` may get special support for making better use of strict inequalities.

To rewrite only in the `n`-th position, use `nth_grw n`.
This is useful when `grw` tries to rewrite in a position that is not valid for the given relation.

To be able to use `grw`, the relevant lemmas need to be tagged with `@[gcongr]`.
To rewrite inside a transitive relation, you can also give it an `IsTrans` instance.

To let `grw` unfold more aggressively, as in `erw`, use `grw (transparency := default)`.
-/
macro (name := grwSeq) "grw " c:optConfig s:rwRuleSeq l:(location)? : tactic =>
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (grewrite $c [$rs,*] $(l)?; with_annotate_state $rbrak (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported


/-- `apply_rewrite [rules]` is a shorthand for `grewrite +implicationHyp [rules]`. -/
macro "apply_rewrite" c:optConfig s:rwRuleSeq loc:(location)? : tactic => do
  `(tactic| grewrite $[$(getConfigItems c)]* +implicationHyp $s:rwRuleSeq $(loc)?)

/-- `apply_rw [rules]` is a shorthand for `grw +implicationHyp [rules]`. -/
macro (name := applyRwSeq) "apply_rw " c:optConfig s:rwRuleSeq loc:(location)? : tactic => do
  `(tactic| grw $[$(getConfigItems c)]* +implicationHyp $s:rwRuleSeq $(loc)?)

/-- `nth_grewrite` is just like `nth_rewrite`, but for `grewrite`. -/
macro "nth_grewrite" c:optConfig ppSpace nums:(num)+ s:rwRuleSeq loc:(location)? : tactic => do
  `(tactic| grewrite $[$(getConfigItems c)]* (occs := .pos [$[$nums],*]) $s:rwRuleSeq $(loc)?)

/-- `nth_grw` is just like `nth_rw`, but for `grw`. -/
macro "nth_grw" c:optConfig ppSpace nums:(num)+ s:rwRuleSeq loc:(location)? : tactic => do
  `(tactic| grw $[$(getConfigItems c)]* (occs := .pos [$[$nums],*]) $s:rwRuleSeq $(loc)?)

end Mathlib.Tactic
