/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer, Mario Carneiro, Heather Macbeth, Jovan Gerbscheid
-/
import Mathlib.Tactic.GRewrite.Core
import Mathlib.Tactic.GCongr

/-!

# The generalized rewriting tactic

The `grw`/`grewrite` tactic is a generalization of the `rewrite` tactic that works with relations
other than equality.

-/

namespace Mathlib.Tactic

open Lean Meta Elab Parser Tactic

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

def grewriteLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId) (config : GRewrite.Config) :
    TacticM Unit := withMainContext do
  -- Note: we cannot execute `replace` inside `Term.withSynthesize`.
  -- See issues #2711 and #2727.
  let goal ← getMainGoal
  let r ← Term.withSynthesize <| withMainContext do
    let e ← elabTerm stx none true
    if e.hasSyntheticSorry then
      throwAbortTactic
    let localDecl ← fvarId.getDecl
    goal.grewrite localDecl.type e (forwardImp := true) (symm := symm) (config := config)
  let proof := .app (r.impProof) (.mvar goal)
  let { mvarId, .. } ← goal.replace fvarId proof r.eNew
  replaceMainGoal (mvarId :: r.mvarIds)

declare_config_elab elabGRewriteConfig GRewrite.Config

/--
`grewrite [e]` works just like `rewerite [e]`, but `e` can be a relation other than `=` or `↔`.

For example,
```lean
example (h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  grewrite [h₁, h₂]; rfl

example (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  grewrite [h]; rfl

example : (h₁ : a ∣ b) (h₂ : c ∣ a * d) : a ∣ b * d := by
  grewrite [h₁]
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
example (h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  grw [h₁, h₂]

example (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  grw [h]

example : (h₁ : a ∣ b) (h₂ : c ∣ a * d) : a ∣ b * d := by
  grw [h₁]
  exact h₂

```
To be able to use `grw`, the relevant lemmas need to be tagged with `@[gcongr]`.
To rewrite inside a transitive relation, you can also give it an `IsTrans` instance.
-/
macro (name := rwSeq) "grw " c:optConfig s:rwRuleSeq l:(location)? : tactic =>
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (grewrite $c [$rs,*] $(l)?; with_annotate_state $rbrak (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported


/-- `apply_rw [rules]` is a shorthand for `grw +implicationHyp [rules]`.
This does rewriting up to unfolding of regular definitions (by comparison to regular `rw`
which only unfolds `@[reducible]` definitions). -/
macro "apply_rw" c:optConfig s:rwRuleSeq loc:(location)? : tactic => do
  `(tactic| grw $[$(getConfigItems c)]* +implicationHyp $s:rwRuleSeq $(loc)?)


/-- `nth_grewrite` is just like `nth_rewrite`, but for `grewrite`. -/
syntax (name := nthGRewriteSeq) "nth_grewrite" optConfig ppSpace num+ rwRuleSeq (location)? : tactic

@[inherit_doc nthGRewriteSeq, tactic nthGRewriteSeq]
def evalNthGRewriteSeq : Tactic := fun stx => do
  match stx with
  | `(tactic| nth_grewrite $cfg:optConfig $[$n]* $_rules:rwRuleSeq $[$loc]?) =>
    let cfg ← elabGRewriteConfig cfg
    let loc := expandOptLocation (mkOptionalNode loc)
    let occ := Occurrences.pos (n.map TSyntax.getNat).toList
    let cfg := { cfg with occs := occ }
    withRWRulesSeq stx[0] stx[3] fun symm term => do
      withLocation loc
        (grewriteLocalDecl term symm · cfg)
        (grewriteTarget term symm cfg)
        (throwTacticEx `nth_grewrite · "did not find instance of the pattern in the current goal")
  | _ => throwUnsupportedSyntax

/-- `nth_grw` is just like `nth_rw`, but for `grw`. -/
macro (name := nthGRwSeq) "nth_grw" c:optConfig ppSpace n:num+ s:rwRuleSeq l:(location)? : tactic =>
  -- Note: This is a direct copy of `nth_rw` from core.
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (nth_grewrite $c:optConfig $[$n]* [$rs,*] $(l)?; with_annotate_state $rbrak
      (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported


end Mathlib.Tactic
