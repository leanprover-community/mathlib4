/-
Copyright (c) 2023 Moritz Doll, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Gabriel Ebner, Damiano Testa
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.TermCongr
import Mathlib.Tactic.Convert
import Mathlib.Logic.Basic

/-!
# The `congrm` tactic

The `congrm` tactic is a convenient frontend for the `congr%` term elaborator.
Roughly, `congrm e` is `refine congr% e'`, where `e'` is `e` with every `?m` placeholder
replaced by `c(?m)`.
-/

namespace Mathlib.Tactic
open Lean Parser Tactic Elab Tactic Meta

initialize registerTraceClass `Tactic.congrm

/--
`congrm e` is a tactic for proving goals of the form `lhs = rhs`, `lhs ↔ rhs`, or `R lhs rhs` when
`R` is a reflexive relation. The expression `e` is a pattern containing placeholders `?_` that
is matched against `lhs` and `rhs`, and these placeholders generate new goals that state
the corresponding subexpressions in `lhs` and `rhs` are equal.
If the placeholders have names, such as `?m`, then the new goals are given tags with those names.

Examples:
```lean
example {a b c d : ℕ} :
    Nat.pred a.succ * (d + (c + a.pred)) = Nat.pred b.succ * (b + (c + d.pred)) := by
  congrm Nat.pred (Nat.succ ?h1) * (?h2 + ?h3)
  /-  Goals left:
  case h1 ⊢ a = b
  case h2 ⊢ d = b
  case h3 ⊢ c + a.pred = c + d.pred
  -/
  sorry
  sorry
  sorry

example {a b : ℕ} (h : a = b) : (λ y : ℕ => ∀ z, a + a = z) = (λ x => ∀ z, b + a = z) := by
  congrm λ x => ∀ w, ?_ + a = w
  -- ⊢ a = b
  exact h
```

The `congrm` command is a convenient frontend to the `congr%` term elaborator.
If the goal is an equality, `congrm e` is equivalent to `refine congr% e'` where `e'` is
from replacing each placeholder `?m` with `c(?m)`.
The pattern `e` is allowed to contain `c(..)` expressions to immediately substitute
equality proofs into the congruence.
-/
syntax (name := congrM) "congrm " term : tactic

elab_rules : tactic
  | `(tactic| congrm $expr:term) => do
    -- Wrap all synthetic holes `?m` as `c(?m)` to form `congr%` pattern
    let pattern ← expr.raw.replaceM fun stx =>
      if stx.isOfKind ``Parser.Term.syntheticHole then
        `(c($(⟨stx⟩)))
      else if stx.isOfKind ``Mathlib.Tactic.termCongrEq then
        -- Don't look into `c(..)` expressions
        pure stx
      else
        pure none
    trace[Tactic.congrm] "pattern: {pattern}"
    -- Chain together transformations as needed to convert the goal to an Eq
    liftMetaTactic fun g => do
      return [← (← g.iffOfEq).liftReflToEq]
    withMainContext do
      let gStx ← Term.exprToSyntax (← getMainTarget)
      -- Use `refine` to apply the congruence, which gives `congrm` the power to unfold definitions
      evalTactic <| ← `(tactic| refine (congr% $(⟨pattern⟩) : $gStx))
