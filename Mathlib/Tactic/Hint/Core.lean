/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.SolveByElim

/-!
# Hint tactic
-/

namespace Mathlib.Tactic.Hint

open Lean

initialize hintExtension : SimplePersistentEnvExtension Syntax.Tactic (Array Syntax.Tactic) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := Array.foldl Array.append #[]
  }

/-- `add_hint_tactic t` runs the tactic `t` whenever `hint` is invoked.
The typical use case is `add_hint_tactic "foo"` for some interactive tactic `foo`.
-/
elab "add_hint_tactic" tac:tactic : command => do
  modifyEnv fun env => hintExtension.addEntry env tac

/-
add_hint_tactic infer_param

add_hint_tactic dsimp at *

add_hint_tactic simp at *

-- TODO hook up to squeeze_simp?
add_hint_tactic fconstructor

add_hint_tactic injections

add_hint_tactic solve_by_elim

add_hint_tactic unfold_coes

add_hint_tactic unfold_aux

end Hint

/-- Report a list of tactics that can make progress against the current goal,
and for each such tactic, the number of remaining goals afterwards.
-/
unsafe def hint : tactic (List (String × ℕ)) := do
  let names ← attribute.get_instances `hint_tactic
  focus1 <| try_all_sorted (names name_to_tactic)
#align tactic.hint tactic.hint

namespace Interactive

/-- Report a list of tactics that can make progress against the current goal.
-/
unsafe def hint : tactic Unit := do
  let hints ← tactic.hint
  if hints = 0 then fail "no hints available"
    else do
      let t ← hints 0
      if t.2 = 0 then do
          trace "the following tactics solve the goal:\n----"
          (hints fun p : String × ℕ => p.2 = 0).mapM' fun p => tactic.trace f! "Try this: {p.1}"
        else do
          trace "the following tactics make progress:\n----"
          hints fun p => tactic.trace f! "Try this: {p.1}"
#align tactic.interactive.hint tactic.interactive.hint

/--
`hint` lists possible tactics which will make progress (that is, not fail) against the current goal.

```lean
example {P Q : Prop} (p : P) (h : P → Q) : Q :=
begin
  hint,
  /- the following tactics make progress:
     ----
     Try this: solve_by_elim
     Try this: finish
     Try this: tauto
  -/
  solve_by_elim,
end
```

You can add a tactic to the list that `hint` tries by either using
1. `attribute [hint_tactic] my_tactic`, if `my_tactic` is already of type `tactic string`
(`tactic unit` is allowed too, in which case the printed string will be the name of the
tactic), or
2. `add_hint_tactic "my_tactic"`, specifying a string which works as an interactive tactic.
-/
add_tactic_doc
  { Name := "hint"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.hint]
    tags := ["search", "Try this"] }
-/
end Mathlib.Tactic.Hint
