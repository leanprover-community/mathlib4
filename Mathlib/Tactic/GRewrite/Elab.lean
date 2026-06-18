/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Sebastian Zimmer, Mario Carneiro, Heather Macbeth
-/
module

public meta import Lean.Elab.Tactic.Rewrite
public meta import Lean.Elab.ConfigEval
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

meta section

namespace Mathlib.Tactic.GRewrite

open Lean Meta Elab Parser Tactic

/-- Return the union of `lctx₁` and `lctx₂`. -/
def mergeLCtx (lctx₁ lctx₂ : LocalContext) : LocalContext :=
  lctx₂.foldl (init := lctx₁) fun lctx decl ↦
    if lctx.contains decl.fvarId then
      lctx
    else
      lctx.addDecl decl

/-- Merge `lctx` into the local contexts in `tree`.
This is used to let `tree` know about bound variables that the term has been unified with. -/
partial def updateInfoTree (lctx : LocalContext) (tree : InfoTree) : InfoTree :=
  match tree with
  | .context i tree => .context i (updateInfoTree lctx tree)
  | .node i children =>
    let i := match i with
      | .ofTermInfo i => .ofTermInfo { i with lctx := mergeLCtx lctx i.lctx }
      | .ofFieldInfo i => .ofFieldInfo { i with lctx := mergeLCtx lctx i.lctx }
      | .ofMacroExpansionInfo i => .ofMacroExpansionInfo { i with lctx := mergeLCtx lctx i.lctx }
      | _ => i
    .node i (children.map (updateInfoTree lctx))
  | _ => tree

/-- Analogous to `finishElabRewrite`. -/
def finishElabGRewrite (r : GRewriteResult) : MetaM GRewriteResult := do
  let mvarIds ← r.mvarIds.filterM (not <$> ·.isAssigned)
  mvarIds.forM fun newMVarId => newMVarId.withContext do
    if ← Meta.isProp (← newMVarId.getType) then
      newMVarId.setKind .syntheticOpaque
  return { r with mvarIds }

/-- Mostly analogous to `elabRewrite`. -/
def elabGRewrite (mvarId : MVarId) (e : Expr) (stx : Syntax) (forwardImp symm : Bool)
    (config : GRewrite.Config) : TacticM GRewriteResult := do
  let treesSaved ← getResetInfoTrees
  let r ← Term.withSynthesize do
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let thm ← elabTerm stx none true
    if thm.hasSyntheticSorry then
      throwAbortTactic
    unless ← occursCheck mvarId thm do
      throwErrorAt stx
        "Occurs check failed: Expression{indentExpr thm}\ncontains the goal {Expr.mvar mvarId}"
    let mvarIds ← getMVarsNoDelayed thm
    let mctx ← getMCtx
    let mvarIds := mvarIds.filter fun mvarId ↦ mvarCounterSaved ≤ (mctx.getDecl mvarId).index
    let lctx ← getLCtx
    let mvarIds ← mvarIds.mapM fun mvarId ↦ do
      let mut fvarIds := #[]
      for decl in (← mvarId.getDecl).lctx do
        unless lctx.contains decl.fvarId do
          fvarIds := fvarIds.push decl
      return (mvarId, fvarIds)
    let r ← mvarId.grewrite e thm mvarIds
      (forwardImp := forwardImp) (symm := symm) (config := config)
    let mctx ← getMCtx
    let mvarIds := r.mvarIds.filter fun mvarId => mvarCounterSaved ≤ (mctx.getDecl mvarId).index
    return { r with mvarIds }
  let s ← getInfoState
  let trees := s.trees.map (·.substitute s.assignment)
  let trees := match r.lctx? with
    | some lctx => trees.map (updateInfoTree lctx)
    | none => trees
  modifyInfoState fun s => { s with trees := treesSaved ++ trees }
  finishElabGRewrite r

/-- Apply the `grewrite` tactic to the current goal. -/
def grewriteTarget (stx : Syntax) (symm : Bool) (config : GRewrite.Config) : TacticM Unit := do
  let goal ← getMainGoal
  let r ← goal.withContext do
    elabGRewrite goal (← goal.getType) stx (forwardImp := false) (symm := symm) (config := config)
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar r.eNew (← goal.getTag)
  goal.assign (r.impProof.app mvarNew)
  replaceMainGoal (mvarNew.mvarId! :: r.mvarIds)

/-- Apply the `grewrite` tactic to a local hypothesis. -/
def grewriteLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId) (config : GRewrite.Config) :
    TacticM Unit := withMainContext do
  -- Note: we cannot execute `replace` inside `Term.withSynthesize`.
  -- See issues https://github.com/leanprover-community/mathlib4/issues/2711 and https://github.com/leanprover-community/mathlib4/issues/2727.
  let goal ← getMainGoal
  let r ← withMainContext do
    elabGRewrite (← getMainGoal) (← fvarId.getType) stx symm (forwardImp := true) (config := config)
  let proof := r.impProof.app (.fvar fvarId)
  let { mvarId, .. } ← goal.replace fvarId proof r.eNew
  replaceMainGoal (mvarId :: r.mvarIds)

/-- Function elaborating `GRewrite.Config`. -/
declare_config_elab elabGRewriteConfig GRewrite.Config

/--
`grewrite [e₁, ..., eₙ]` uses each expression `eᵢ : Rᵢ aᵢ bᵢ` (where `Rᵢ` is any two-argument
relation) as a generalized rewrite rule on the main goal, replacing occurrences of `aᵢ` with `bᵢ`.
Use `grewrite [← eᵢ]` to rewrite in the other direction, replacing occurrences of `bᵢ` with `aᵢ`.

If an expression `e` is a defined constant, then the equational theorems associated with `e` are
used. This provides a convenient way to unfold `e`. If `e` has parameters, the tactic will try to
fill these in by unification with the matching part of the target. Parameters are only filled in
once per rule, restricting which later rewrites can be found. Parameters that are not filled in
after unification will create side goals.

To be able to use `grewrite`, the relevant lemmas need to be tagged with `@[gcongr]`.
To rewrite inside a transitive relation, you can also give it an `IsTrans` instance.

Rewriting with a strict inequality `a < b` may change a constant in the goal,
such as changing `<` to `≤`. If this is not possible, then `a < b` is treated the same as `a ≤ b`.

`grw` is like `grewrite` but tries to close the goal afterwards by "cheap" (reducible) `rfl`.
To rewrite only in the `n`-th position, use `nth_grewrite n`.
`apply_rewrite [e₁, ..., eₙ]` is a shorthand for `grewrite +implicationHyp [e₁, ..., eₙ]`: it
interprets `· → ·` as a relation instead of adding the hypothesis as a side condition.

* `grewrite [← e]` applies the rewrite rule `e : R a b` in the reverse direction, replacing
  occurrences of `b` with `a`.
* `grewrite (config := cfg) [e₁, ..., eₙ]` uses `cfg` as configuration. See `GRewrite.Config` for
  details.
  * To let `grewrite` unfold more aggressively, as in `erw`, use
    `grewrite (transparency := default) [e₁, ..., eₙ]`.
  * `grewrite +implicationHyp [e₁, ..., eₙ]` interprets `· → ·` as a relation (see `apply_rewrite`).
* `grewrite [e₁, ..., eₙ] at l` rewrites at the location(s) `l`.
-/
syntax (name := grewriteSeq) "grewrite" optConfig rwRuleSeq (location)? : tactic

@[tactic grewriteSeq, inherit_doc grewriteSeq]
public def evalGRewriteSeq : Tactic := fun stx => do
  let cfg ← elabGRewriteConfig stx[1]
  let loc := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (grewriteLocalDecl term symm · cfg)
      (grewriteTarget term symm cfg)
      (throwTacticEx `grewrite · "did not find instance of the pattern in the current goal")

/--
`grw [e₁, ..., eₙ]` uses each expression `eᵢ : Rᵢ aᵢ bᵢ` (where `Rᵢ` is any two-argument
relation) as a generalized rewrite rule on the main goal, replacing occurrences of `aᵢ` with `bᵢ`,
then tries to close the main goal by "cheap" (reducible) `rfl`.
Use `grw [← eᵢ]` to rewrite in the other direction, replacing occurrences of `bᵢ` with `aᵢ`.

If an expression `e` is a defined constant, then the equational theorems associated with `e` are
used. This provides a convenient way to unfold `e`. If `e` has parameters, the tactic will try to
fill these in by unification with the matching part of the target. Parameters are only filled in
once per rule, restricting which later rewrites can be found. Parameters that are not filled in
after unification will create side goals.

To be able to use `grw`, the relevant lemmas need to be tagged with `@[gcongr]`.
To rewrite inside a transitive relation, you can also give it an `IsTrans` instance.

Rewriting with a strict inequality `a < b` may change the goal, such as changing `<` to `≤`.
If this is not possible, then `a < b` is treated the same as `a ≤ b`.

`grewrite` is like `grw` but does not try to apply `rfl` afterwards.
To rewrite only in the `n`-th position, use `nth_grw n`.
`apply_rw [e₁, ..., eₙ]` is a shorthand for `grw +implicationHyp [e₁, ..., eₙ]`: it interprets
`· → ·` as a relation instead of adding the hypothesis as a side condition.

* `grw [← e]` applies the rewrite rule `e : R a b` in the reverse direction, replacing occurrences
  of `b` with `a`.
* `grw (config := cfg) [e₁, ..., eₙ]` uses `cfg` as configuration. See `GRewrite.Config` for
  details.
  * To let `grw` unfold more aggressively, as in `erw`, use
    `grw (transparency := default) [e₁, ..., eₙ]`.
  * `grw +implicationHyp [e₁, ..., eₙ]` interprets `· → ·` as a relation (see `apply_rw`).
* `grw [e₁, ..., eₙ] at l` rewrites at the location(s) `l`.

Examples:

```lean
variable {a b c d n : ℤ}

example (h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  grw [h₁, h₂]

example (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  grw [h]

example (h₁ : a ∣ b) (h₂ : b ∣ a ^ 2 * c) : a ∣ b ^ 2 * c := by
  grw [h₁] at *
  exact h₂

-- To replace the RHS with the LHS of the given relation, use the `←` notation (just like in `rw`):
example (h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  grw [← h₂, ← h₁]
```
-/
macro (name := grwSeq) "grw " c:optConfig s:rwRuleSeq l:(location)? : tactic =>
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (grewrite $c [$rs,*] $(l)?; with_annotate_state $rbrak (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported

/--
`apply_rewrite [e₁, ..., eₙ]` uses the expressions `e₁`, ..., `eₙ` as generalized rewrite rules, of
type `pᵢ → qᵢ`, on the main goal, replacing occurrences of `pᵢ` with `qᵢ`. The difference with
`grewrite` is that `grewrite` would turn `pᵢ` into a side goal and expect `qᵢ` to be a relation.

If an expression `e` is a defined constant, then the equational theorems associated with `e` are
used. This provides a convenient way to unfold `e`.

* `apply_rewrite [← e]` applies the rewrite rule `e : p → q` in the reverse direction, replacing
  occurrences of `q` with `p`.
* `apply_rewrite (config := cfg) [e₁, ..., eₙ]` uses `cfg` as configuration. See `GRewrite.Config`
  for details.
  To let `apply_rewrite` unfold more aggressively, as in `erw`, use
  `apply_rewrite (transparency := default) [e₁, ..., eₙ]`.
* `apply_rewrite [e₁, ..., eₙ] at l` rewrites at the location(s) `l`.
-/
macro "apply_rewrite" c:optConfig s:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| grewrite $[$(getConfigItems c)]* +implicationHyp $s:rwRuleSeq $(loc)?)

/--
`apply_rw [e₁, ..., eₙ]` uses the expressions `e₁`, ..., `eₙ` as generalized rewrite rules, of type
`pᵢ → qᵢ`, on the main goal, replacing occurrences of `pᵢ` with `qᵢ`. The difference with `grw` is
that `grw` would turn `pᵢ` into a side goal and expect `qᵢ` to be a relation.

If an expression `e` is a defined constant, then the equational theorems associated with `e` are
used. This provides a convenient way to unfold `e`.

* `apply_rw [← e]` applies the rewrite rule `e : p → q` in the reverse direction, replacing
  occurrences of `q` with `p`.
* `apply_rw (config := cfg) [e₁, ..., eₙ]` uses `cfg` as configuration. See `GRewrite.Config`
  for details.
  To let `apply_rw` unfold more aggressively, as in `erw`, use
  `apply_rw (transparency := default) [e₁, ..., eₙ]`.
* `apply_rw [e₁, ..., eₙ] at l` rewrites at the location(s) `l`.
-/
macro (name := applyRwSeq) "apply_rw " c:optConfig s:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| grw $[$(getConfigItems c)]* +implicationHyp $s:rwRuleSeq $(loc)?)

/--
`nth_grewrite n₁ ... nₖ [e₁, ..., eₙ]` is a variant of `grewrite` that for each expression
`eᵢ : R aᵢ bᵢ` only replaces the `n₁, ..., nₖ`th occurrence of `aᵢ` with `bᵢ`.
Use `nth_grewrite n₁ ... nₖ [← eᵢ]` to rewrite in the other direction, replacing occurrences of `bᵢ`
with `aᵢ`.

If an expression `e` is a defined constant, then the equational theorems associated with `e` are
used. This provides a convenient way to unfold `e`. If `e` has parameters, the tactic will try to
fill these in by unification with the matching part of the target. Parameters are only filled in
once per rule, restricting which later rewrites can be found. Parameters that are not filled in
after unification will create side goals.

To be able to use `nth_grewrite`, the relevant lemmas need to be tagged with `@[gcongr]`.
To rewrite inside a transitive relation, you can also give it an `IsTrans` instance.
Rewriting with a strict inequality `a < b` may change the strictness of the goal,
replacing a goal `_ < _` by `_ ≤ _`. If this is not possible, then `a < b` is treated as `a ≤ b`.

* `nth_grewrite n₁ ... nₖ [← e]` applies the rewrite rule `e : R a b` in the reverse direction,
  replacing the `n₁, ..., nₖ`th occurrences of `b` with `a`.
* `nth_grewrite (config := cfg) n₁ ... nₖ [e₁, ..., eₙ]` uses `cfg` as configuration. See
  `GRewrite.Config` for details.
  * To let `nth_grewrite` unfold more aggressively, as in `erw`, use
    `nth_grewrite (transparency := default) n₁ ... nₖ [e₁, ..., eₙ]`.
  * `nth_grewrite +implicationHyp n₁ ... nₖ [e₁, ..., eₙ]` interprets `· → ·` as a relation.
* `nth_grewrite n₁ ... nₖ [e₁, ..., eₙ] at l` rewrites at the location(s) `l`.
-/
macro "nth_grewrite" c:optConfig ppSpace nums:(num)+ s:rwRuleSeq loc:(location)? : tactic =>
  `(tactic|
    grewrite $[$(getConfigItems c)]* +useKAbstract (occs := .pos [$[$nums],*]) $s:rwRuleSeq $(loc)?)

/--
`nth_grw n₁ ... nₖ [e₁, ..., eₙ]` is a variant of `grw` that for each expression `eᵢ : R aᵢ bᵢ` only
replaces the `n₁, ..., nₖ`th occurrence of `aᵢ` with `bᵢ`. Use `nth_grw n₁ ... nₖ [← eᵢ]` to rewrite
in the other direction, replacing occurrences of `bᵢ` with `aᵢ`.

If an expression `e` is a defined constant, then the equational theorems associated with `e` are
used. This provides a convenient way to unfold `e`. If `e` has parameters, the tactic will try to
fill these in by unification with the matching part of the target. Parameters are only filled in
once per rule, restricting which later rewrites can be found. Parameters that are not filled in
after unification will create side goals.

To be able to use `nth_grw`, the relevant lemmas need to be tagged with `@[gcongr]`.
To rewrite inside a transitive relation, you can also give it an `IsTrans` instance.
Rewriting with a strict inequality `a < b` may change the strictness of the goal,
replacing a goal `_ < _` by `_ ≤ _`. If this is not possible, then `a < b` is treated as `a ≤ b`.

* `nth_grw n₁ ... nₖ [← e]` applies the rewrite rule `e : R a b` in the reverse direction, replacing
  the `n₁, ..., nₖ`th occurrences of `b` with `a`.
* `nth_grw (config := cfg) n₁ ... nₖ [e₁, ..., eₙ]` uses `cfg` as configuration. See
  `GRewrite.Config` for details.
  * To let `nth_grw` unfold more aggressively, as in `erw`, use
    `nth_grw (transparency := default) n₁ ... nₖ [e₁, ..., eₙ]`.
  * `nth_grw +implicationHyp n₁ ... nₖ [e₁, ..., eₙ]` interprets `· → ·` as a relation.
* `nth_grw n₁ ... nₖ [e₁, ..., eₙ] at l` rewrites at the location(s) `l`.
-/
macro "nth_grw" c:optConfig ppSpace nums:(num)+ s:rwRuleSeq loc:(location)? : tactic =>
  `(tactic|
    grw $[$(getConfigItems c)]* +useKAbstract (occs := .pos [$[$nums],*]) $s:rwRuleSeq $(loc)?)

end Mathlib.Tactic.GRewrite
