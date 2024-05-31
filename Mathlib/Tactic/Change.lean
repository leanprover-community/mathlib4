/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Tactic.Basic
/-!

# Tactic `change? term`

This tactic is used to suggest a replacement of the goal by a definitionally equal term.
`term` is intended to contain holes which get unified with the main goal and filled in explicitly
in the suggestion.

`term` can also be omitted, in which case `change?` simply suggests `change` with the main goal.
This is helpful after tactics like `dsimp`, which can then be deleted.
-/

/-- `change? term` unifies `term` with the current goal, then suggests explicit `change` syntax
that uses the resulting unified term.

If `term` is not present, `change?` suggests the current goal itself. This is useful after tactics
which transform the goal while maintaining definitional equality, such as `dsimp`; those preceding
tactic calls can then be deleted.
```lean
example : (fun x : Nat => x) 0 = 1 := by
  change? 0 = _  -- `Try this: change 0 = 1`
```
-/
syntax (name := change?) "change?" (ppSpace colGt term)? : tactic

open Lean Meta Elab.Tactic Meta.Tactic.TryThis in
elab_rules : tactic
| `(tactic|change?%$tk $[$sop:term]?) => withMainContext do
  let stx ← getRef
  let expr ← match sop with
    | none => getMainTarget
    | some sop => do
      let tgt ← getMainTarget
      let ex ← withRef sop <| elabTermEnsuringType sop (← inferType tgt)
      if !(← isDefEq ex tgt) then throwErrorAt sop "\
        The term{indentD ex}\n\
        is not defeq to the goal:{indentD tgt}"
      instantiateMVars ex
  let dstx ← delabToRefinableSyntax expr
  addSuggestion tk (← `(tactic| change $dstx)) (origSpan? := stx)
