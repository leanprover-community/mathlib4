/-
Copyright (c) 2026 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Lean.Elab.Tactic.ElabTerm
public import Mathlib.Init

/-!
# The `assume` tactic
-/

/-- The `assume` tactic introduces hypotheses to the context, without giving them a user-facing
name.
* Example: `assume f x = f y, 0 < g y`
* The arguments should be comma-separated, and are required to be propositions that are
  definitionally equal to the hypothesis (or domain of a dependent function) in the goal.
* The introduced hypothesis will have the exact statement the user wrote.
* `assume h₁, h₂, h₃` is equivalent to `intro (_ : h₁) (_ : h₂) (_ : h₃)` if they are hypotheses.
-/
syntax (name := assume) &"assume " (ppSpace colGt term),* : tactic

open Lean Meta Elab Tactic
elab_rules : tactic
  | `(tactic| assume $[$ts:term],*) => do
    if ts.isEmpty then throwError "Tactic 'assume' failed: No hypotheses given."
    for t in ts do withMainContext do
      let e ← elabTerm t (some (.sort .zero))
      let eType ← inferType e
      let .true ← isDefEq eType (.sort .zero) |
        throwErrorAt t "Tactic 'assume' failed: Given type{indentExpr e}\nis not a proposition."
      let tgt ← getMainTarget
      let .forallE _ b _ _ ← whnf tgt |
        throwErrorAt t "Tactic 'assume' failed: Goal{indentExpr tgt}\nis not an implication."
      let .true ← isDefEq b e |
        throwErrorAt t "Tactic 'assume' failed: Given type{indentExpr e}\ndoes not match the \
        type{indentExpr b}\nof the hypothesis in the goal."
      evalTactic (← `(tactic | intro (_ : $t)))
