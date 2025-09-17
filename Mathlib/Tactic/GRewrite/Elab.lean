/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer, Mario Carneiro, Heather Macbeth, Jovan Gerbscheid
-/
import Mathlib.Tactic.GRewrite.Core

/-!

# The generalized rewriting tactic

This file defines the tactics that use the backend defined in `Mathlib.Tactic.GRewrite.Core`:
- `grewrite`
- `grw`
- `apply_rw`
- `nth_grewrite`
- `nth_grw`

-/

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
`grewrite [e]` works just like `rewrite [e]`, but `e` can be a relation other than `=` or `↔`.

For example,
```lean
variable {a b c d n : ℤ}

example (h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  grewrite [h₁, h₂]; rfl

example (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  grewrite [h]; rfl

example (h₁ : a ∣ b) (h₂ : b ∣ a ^ 2 * c) : a ∣ b ^ 2 * c := by
  grewrite [h₁] at *
  exact h₂
```
To be able to use `grewrite`, the relevant lemmas need to be tagged with `@[gcongr]`.
To rewrite inside a transitive relation, you can also give it an `IsTrans` instance.
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

For example,
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
To be able to use `grw`, the relevant lemmas need to be tagged with `@[gcongr]`.
To rewrite inside a transitive relation, you can also give it an `IsTrans` instance.
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
