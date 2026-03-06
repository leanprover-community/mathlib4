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
`grewrite [e₁, ..., eₙ]` uses the expressions `e₁`, ..., `eₙ` as generalized rewrite rules on the
main goal. In addition to equalities, `grewrite` supports any two-argument relation for the types of
`e₁`, ..., `eₙ` and the main goal.

If an expression `e` is a defined constant, then the equational theorems associated with `e` are
used. This provides a convenient way to unfold `e`. If `e` has parameters, the tactic will try to
fill these in by unification with the matching part of the target. Parameters are only filled in
once per rule, restricting which later rewrites can be found. Parameters that are not filled in
after unification will create side goals.

To be able to use `grewrite`, the relevant lemmas need to be tagged with `@[gcongr]`.
To rewrite inside a transitive relation, you can also give it an `IsTrans` instance.
The strict inequality `a < b` is turned into the non-strict inequality `a ≤ b` to rewrite with it.
A future version of `grewrite` may get special support for making better use of strict inequalities.

`grw` is like `grewrite` but tries to close the goal afterwards by "cheap" (reducible) `rfl`.
To rewrite only in the `n`-th position, use `nth_grewrite n`.
This is useful when `grewrite` tries to rewrite in a position that is not valid for the given
relation.
`apply_rewrite [e₁, ..., eₙ]` is a shorthand for `grewrite +implicationHyp [e₁, ..., eₙ]`: it
interprets `· → ·` as a relation instead of adding side conditions.

* `grewrite (config := cfg) [e₁, ..., eₙ]` uses `cfg` as configuration. See `GRewrite.Config` for
  details.
  * To let `grewrite` unfold more aggressively, as in `erw`, use
    `grewrite (transparency := default) [e₁, ..., eₙ]`.
  * `grewrite +implicationHyp [e₁, ..., eₙ]` interprets `· → ·` as a relation (see `apply_rewrite`).
* `grewrite [e₁, ..., eₙ] at l` rewrites at the location(s) `l`.
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
`grw [e₁, ..., eₙ]` uses the expressions `e₁`, ..., `eₙ` as generalized rewrite rules on the
main goal, then tries to close the goal by "cheap" (reducible) `rfl`. In addition to equalities,
`grw` supports any two-argument relation for the types of `e₁`, ..., `eₙ` and the main goal.

If an expression `e` is a defined constant, then the equational theorems associated with `e` are
used. This provides a convenient way to unfold `e`. If `e` has parameters, the tactic will try to
fill these in by unification with the matching part of the target. Parameters are only filled in
once per rule, restricting which later rewrites can be found. Parameters that are not filled in
after unification will create side goals.

To be able to use `grw`, the relevant lemmas need to be tagged with `@[gcongr]`.
To rewrite inside a transitive relation, you can also give it an `IsTrans` instance.
The strict inequality `a < b` is turned into the non-strict inequality `a ≤ b` to rewrite with it.
A future version of `grw` may get special support for making better use of strict inequalities.

`grewrite` is like `grw` but does not try to apply `rfl` afterwards.
To rewrite only in the `n`-th position, use `nth_grw n`.
This is useful when `grw` tries to rewrite in a position that is not valid for the given relation.
`apply_rw [rules]` is a shorthand for `grw +implicationHyp [rules]`: it interprets `· → ·` as a
relation instead of adding side conditions.

* `grw (config := cfg) [e₁, ..., eₙ]` uses `cfg` as configuration. See `GRewrite.Config` for
  details.
  * To let `grw` unfold more aggressively, as in `erw`, use
    `grw (transparency := default) [e₁, ..., eₙ]`.
  * `grw +implicationHyp [e₁, ..., e\_n]` interprets `· → ·` as a relation (see `apply_rw`).
* `grw [← e]` applies the rewrite rule in the reverse direction.
* `grw [e₁, ..., e\_n] at l` rewrites at the location(s) `l`.

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
`apply_rewrite [e₁, ..., eₙ]` uses the expressions `e₁`, ..., `eₙ` as generalized rewrite rules on
the main goal. In addition to equalities, `apply_rewrite` supports implications and any two-argument
relation for the types of `e₁`, ..., `eₙ` and the main goal.
`apply_rewrite [e₁, ..., eₙ]` is a shorthand for `grewrite +implicationHyp [e₁, ..., eₙ]`: it
interprets `· → ·` as a relation instead of adding side conditions.

If an expression `e` is a defined constant, then the equational theorems associated with `e` are
used. This provides a convenient way to unfold `e`.

* `apply_rewrite (config := cfg) [e₁, ..., eₙ]` uses `cfg` as configuration. See `GRewrite.Config`
  for details.
  To let `apply_rewrite` unfold more aggressively, as in `erw`, use
  `apply_rewrite (transparency := default) [e₁, ..., eₙ]`.
* `apply_rewrite [e₁, ..., eₙ] at l` rewrites at the location(s) `l`.
-/
macro "apply_rewrite" c:optConfig s:rwRuleSeq loc:(location)? : tactic => do
  `(tactic| grewrite $[$(getConfigItems c)]* +implicationHyp $s:rwRuleSeq $(loc)?)

/--
`apply_rw [e₁, ..., eₙ]` uses the expressions `e₁`, ..., `eₙ` as generalized rewrite rules on the
main goal, then tries to close the goal by "cheap" (reducible) `rfl`. In addition to equalities,
`apply_rw` supports implications and any two-argument relation for the types of `e₁`, ..., `eₙ` and
the main goal. `apply_rw [e₁, ..., eₙ]` is a shorthand for `grw +implicationHyp [e₁, ..., eₙ]`: it
interprets `· → ·` as a relation instead of adding side conditions.

If an expression `e` is a defined constant, then the equational theorems associated with `e` are
used. This provides a convenient way to unfold `e`.

* `apply_rw (config := cfg) [e₁, ..., eₙ]` uses `cfg` as configuration. See `GRewrite.Config`
  for details.
  To let `apply_rw` unfold more aggressively, as in `erw`, use
  `apply_rw (transparency := default) [e₁, ..., eₙ]`.
* `apply_rw [e₁, ..., eₙ] at l` rewrites at the location(s) `l`.
-/
macro (name := applyRwSeq) "apply_rw " c:optConfig s:rwRuleSeq loc:(location)? : tactic => do
  `(tactic| grw $[$(getConfigItems c)]* +implicationHyp $s:rwRuleSeq $(loc)?)

/--
`nth_grewrite n₁ ... nₖ [e₁, ..., eₙ]` is a variant of `grewrite` that only changes the `n₁, ...,
nₖ`th occurrence of each expression to be rewritten. It uses the expressions `e₁`, ..., `eₙ` as
generalized rewrite rules on the main goal, and for each `eᵢ`, each specified occurrence will be
rewritten. In addition to equalities, `nth_grewrite` supports any two-argument relation
for the types of `e₁`, ..., `eₙ` and the main goal.

If an expression `e` is a defined constant, then the equational theorems associated with `e` are
used. This provides a convenient way to unfold `e`. If `e` has parameters, the tactic will try to
fill these in by unification with the matching part of the target. Parameters are only filled in
once per rule, restricting which later rewrites can be found. Parameters that are not filled in
after unification will create side goals.

To be able to use `nth_grewrite`, the relevant lemmas need to be tagged with `@[gcongr]`.
To rewrite inside a transitive relation, you can also give it an `IsTrans` instance.
The strict inequality `a < b` is turned into the non-strict inequality `a ≤ b` to rewrite with it.
A future version of `nth_grewrite` may get special support for making better use of strict
inequalities.

* `nth_grewrite (config := cfg) n₁ ... nₖ [e₁, ..., eₙ]` uses `cfg` as configuration. See
  `GRewrite.Config` for details.
  * To let `nth_grewrite` unfold more aggressively, as in `erw`, use
    `nth_grewrite (transparency := default) n₁ ... nₖ [e₁, ..., eₙ]`.
  * `nth_grewrite +implicationHyp n₁ ... nₖ [e₁, ..., eₙ]` interprets `· → ·` as a relation.
* `nth_grewrite n₁ ... nₖ [e₁, ..., eₙ] at l` rewrites at the location(s) `l`.
-/
macro "nth_grewrite" c:optConfig ppSpace nums:(num)+ s:rwRuleSeq loc:(location)? : tactic => do
  `(tactic| grewrite $[$(getConfigItems c)]* (occs := .pos [$[$nums],*]) $s:rwRuleSeq $(loc)?)

/--
`nth_grw n₁ ... nₖ [e₁, ..., eₙ]` is a variant of `grw` that only changes the `n₁, ..., nₖ`th
occurrence of each expression to be rewritten. It uses the expressions `e₁`, ..., `eₙ` as
generalized rewrite rules on the main goal, and for each `eᵢ`, each specified occurrence will be
rewritten. In addition to equalities, `nth_grw` supports any two-argument relation for the types of
`e₁`, ..., `eₙ` and the main goal.

If an expression `e` is a defined constant, then the equational theorems associated with `e` are
used. This provides a convenient way to unfold `e`. If `e` has parameters, the tactic will try to
fill these in by unification with the matching part of the target. Parameters are only filled in
once per rule, restricting which later rewrites can be found. Parameters that are not filled in
after unification will create side goals.

To be able to use `nth_grw`, the relevant lemmas need to be tagged with `@[gcongr]`.
To rewrite inside a transitive relation, you can also give it an `IsTrans` instance.
The strict inequality `a < b` is turned into the non-strict inequality `a ≤ b` to rewrite with it.
A future version of `nth_grw` may get special support for making better use of strict
inequalities.

* `nth_grw (config := cfg) n₁ ... nₖ [e₁, ..., eₙ]` uses `cfg` as configuration. See
  `GRewrite.Config` for details.
  * To let `nth_grw` unfold more aggressively, as in `erw`, use
    `nth_grw (transparency := default) n₁ ... nₖ [e₁, ..., eₙ]`.
  * `nth_grw +implicationHyp n₁ ... nₖ [e₁, ..., eₙ]` interprets `· → ·` as a relation.
* `nth_grw n₁ ... nₖ [e₁, ..., eₙ] at l` rewrites at the location(s) `l`.
-/
macro "nth_grw" c:optConfig ppSpace nums:(num)+ s:rwRuleSeq loc:(location)? : tactic => do
  `(tactic| grw $[$(getConfigItems c)]* (occs := .pos [$[$nums],*]) $s:rwRuleSeq $(loc)?)

end Mathlib.Tactic
