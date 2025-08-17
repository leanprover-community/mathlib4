/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Init

/-!
# The `@[push]` attribute for the `push` and `push_neg` tactics

This file defines the `@[push]` attribute, so that it can be used without importing
the tactic itself.
-/

namespace Mathlib.Tactic.Push

open Lean Meta

/-- The `push` simp attribute. -/
initialize pushExt : SimpExtension ← mkSimpExt

/--
The `push` attribute is used to tag lemmas that "push" a constant into an expression.

For example:
```lean
@[push] theorem not_not (p : Prop) : ¬¬p ↔ p

@[push] theorem not_imp (p q : Prop) : ¬(p → q) ↔ p ∧ ¬q

@[push] theorem not_iff (p q : Prop) : ¬(p ↔ q) ↔ (p ∧ ¬q) ∨ (¬p ∧ q)
```
-/
syntax (name := pushAttr) "push" (" ←" <|> " <-")? (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  name := `pushAttr
  descr := "attribute for push"
  add := fun decl stx kind => MetaM.run' do
    let inv := !stx[1].isNone
    let prio ← getAttrParamOptPrio stx[2]
    addSimpTheorem pushExt decl (post := false) (inv := inv) kind prio
}

end Mathlib.Tactic.Push
