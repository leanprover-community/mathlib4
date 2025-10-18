/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Init
import Lean.Meta.Tactic.TryThis
import Batteries.Linter.UnreachableTactic
import Qq.Match
import Mathlib.Lean.Elab.InfoTree
import Mathlib.Tactic.Basic

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

open Lean Elab Tactic
open Lean.Meta.Tactic.TryThis

namespace Mathlib.Tactic.Says

/-- If this option is `true`, verify for `X says Y` that `X says` outputs `Y`. -/
register_option says.verify : Bool :=
  { defValue := false
    group := "says"
    descr := "Verify the output" }

/-- This option is only used in CI to negate `says.verify`. -/
register_option says.no_verify_in_CI : Bool :=
  { defValue := false
    group := "says"
    descr := "Disable reverification, even if the `CI` environment variable is set." }

open Parser Tactic

/-- This is a slight modification of `Parser.runParserCategory`. -/
def parseAsTacticSeq (env : Environment) (input : String) (fileName := "<input>") :
    Except String (TSyntax ``tacticSeq) :=
  let p := andthenFn whitespace Tactic.tacticSeq.fn
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if s.hasError then
    Except.error (s.toErrorMsg ictx)
  else if s.pos.atEnd input then
    Except.ok ⟨s.stxStack.back⟩
  else
    Except.error ((s.mkError "end of input").toErrorMsg ictx)

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
    match parseAsTacticSeq (← getEnv) s with
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
