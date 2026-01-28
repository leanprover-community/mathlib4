/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init
public meta import Lean.Meta.Tactic.TryThis
public meta import Qq.Match
public meta import Mathlib.Lean.Elab.InfoTree
public import Batteries.Linter.UnreachableTactic
public import Mathlib.Tactic.Basic
public meta import Mathlib.Util.ParseCommand

/-!
# The `says` tactic combinator.

If you write `X says`, where `X` is a tactic that produces a "Try this: Y" message,
then you will get a message "Try this: X says Y".
Once you've clicked to replace `X says` with `X says Y`,
afterwards `X says Y` will only run `Y`.

The typical usage case is:
```
simp? [X] says simp only [X, Y, Z]
```

If you use `set_option says.verify true` (set automatically during CI) then `X says Y`
runs `X` and verifies that it still prints "Try this: Y".
-/

public meta section

open Lean Elab Tactic
open Lean.Meta.Tactic.TryThis

namespace Mathlib.Tactic.Says

/-- If this option is `true`, verify for `X says Y` that `X says` outputs `Y`. -/
register_option says.verify : Bool :=
  { defValue := false
    descr := "Verify the output" }

/-- This option is only used in CI to negate `says.verify`. -/
register_option says.no_verify_in_CI : Bool :=
  { defValue := false
    descr := "Disable reverification, even if the `CI` environment variable is set." }

open Parser Tactic

/--
Run `evalTactic`, capturing a "Try this:" message and converting it back to syntax.
-/
def evalTacticCapturingTryThis (tac : TSyntax `tactic) : TacticM (TSyntax ``tacticSeq) := do
  let { trees, ..} ← withResetServerInfo <| evalTactic tac
  let suggestions := collectTryThisSuggestions trees
  let some s := suggestions[0]?
    | throwError m!"Tactic `{tac}` did not produce a 'Try this:' suggestion."
  let suggestion ← do
    if let some msg := s.messageData? then
      pure <| SuggestionText.string <| ← msg.toString
    else
      pure <| s.suggestion
  match suggestion with
  | .tsyntax (kind := ``tacticSeq) stx =>
    return stx
  | .tsyntax (kind := `tactic) stx =>
    return ← `(tacticSeq| $stx:tactic)
  | .tsyntax stx =>
    throwError m!"Tactic `{tac}` produced a 'Try this:' suggestion with a non-tactic syntax: {stx}"
  | .string s =>
    match Mathlib.GuardExceptions.parseAsTacticSeq (← getEnv) s with
    | .ok stx => return stx
    | .error err => throwError m!"Failed to parse 'Try this:' suggestion: {s}\n{err}"

/--
If you write `X says`, where `X` is a tactic that produces a "Try this: Y" message,
then you will get a message "Try this: X says Y".
Once you've clicked to replace `X says` with `X says Y`,
afterwards `X says Y` will only run `Y`.

The typical usage case is:
```
simp? [X] says simp only [X, Y, Z]
```

If you use `set_option says.verify true` (set automatically during CI) then `X says Y`
runs `X` and verifies that it still prints "Try this: Y".
-/
syntax (name := says) tactic " says" (colGt tacticSeq)? : tactic

elab_rules : tactic
  | `(tactic| $tac:tactic says%$tk $[$result:tacticSeq]?) => do
  let verify := says.verify.get (← getOptions) ||
    !says.no_verify_in_CI.get (← getOptions) && (← IO.getEnv "CI").isSome
  match result, verify with
  | some _, true
  | none, _ =>
    let stx ← evalTacticCapturingTryThis tac
    match result with
    | some r =>
        let stx' := (← Lean.PrettyPrinter.ppTactic ⟨Syntax.stripPos stx⟩).pretty
        let r' := (← Lean.PrettyPrinter.ppTactic ⟨Syntax.stripPos r⟩).pretty
        if stx' != r' then
          throwError m!"Tactic `{tac}` produced `{stx'}`,\nbut was expecting it to produce `{r'}`!"
            ++ m!"\n\nYou can reproduce this error locally using `set_option says.verify true`."
    | none =>
    addSuggestion tk (← `(tactic| $tac says $stx)) (origSpan? := (← `(tactic| $tac says)))
  | some result, false =>
    evalTactic result

initialize Batteries.Linter.UnreachableTactic.addIgnoreTacticKind `Mathlib.Tactic.Says.says

end Says

end Mathlib.Tactic
