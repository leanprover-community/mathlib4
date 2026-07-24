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

/-- `assume e` introduces a new (unnamed) hypothesis of type `e`.
It is equivalent to `intro (_ : e)`.

The argument `e` is required to be a proposition, definitionally equal to the hypothesis
(or domain of a dependent function) in the goal. The introduced hypothesis will have
the exact form the user wrote.

Example:

```lean
example {α} (f : α → α) (h : Function.Injective f) : ∀ x y, f x = f y → x = y := by
  intro x y
  assume f x = f y
  apply h
  assumption
```
-/
syntax (name := assume) &"assume " (ppSpace colGt term)? : tactic

open Lean Meta Elab Tactic
elab_rules : tactic
  | `(tactic| assume $[$t?:term]?) => do
    let some t := t?
      | throwError "Tactic 'assume' failed: No hypotheses given."
    withMainContext do
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
