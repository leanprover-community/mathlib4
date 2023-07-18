/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger
-/
import Std.Data.String.Basic
import Std.Tactic.GuardMsgs

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
-/

open Lean Elab Tactic
open Std.Tactic.TryThis

namespace Mathlib.Tactic.Says

register_option says.verify : Bool :=
  { defValue := false
    group := "says"
    descr := "For every appearance of the `X says Y` combinator," ++
      " re-verify that running `X` produces `Try this: Y`." }

/-- Run `evalTactic`, capturing any new messages.-/
def evalTacticCapturingMessages (tac : TSyntax `tactic) : TacticM MessageLog := do
  let initMsgs ← modifyGetThe Core.State fun st => (st.messages, { st with messages := {} })
  evalTactic tac
  let msgs := (← getThe Core.State).messages
  modifyThe Core.State fun st => { st with messages := initMsgs }
  return msgs

open Parser Tactic

/-- This is a slight modification of `Parser.runParserCategory`. -/
def parseAsTacticSeq (env : Environment) (input : String) (fileName := "<input>") :
    Except String (TSyntax ``tacticSeq) :=
  let p := andthenFn whitespace Tactic.tacticSeq.fn
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if s.hasError then
    Except.error (s.toErrorMsg ictx)
  else if input.atEnd s.pos then
    Except.ok ⟨s.stxStack.back⟩
  else
    Except.error ((s.mkError "end of input").toErrorMsg ictx)

syntax (name := says) tactic " says" (tacticSeq)? : tactic

elab_rules : tactic
  | `(tactic| $tac:tactic says%$tk $[$result:tacticSeq]?) => do
  let verify := says.verify.get (← getOptions)
  match result, verify with
  | some _, true
  | none, _ =>
    let msgs ← evalTacticCapturingMessages tac
    let S ← match msgs.toList with
    | [] => throwError m!"Tactic `{tac}` did not produce any message."
    | [S] => S.toString
    | _ => throwError m!"Tactic `{tac}` produced multiple messages."
    let S ← match S.dropPrefix? "Try this: " with
    | none => throwError m!"Tactic output did not begin with 'Try this:': {S}"
    | some S => pure S.toString
    let stx ← match parseAsTacticSeq (← getEnv) S with
    | .ok stx => pure stx
    | .error msg => throwError m!"Failed to parse tactic output: {S}\n{msg}"
    match result with
    | some r =>
        let stx' := (← Lean.PrettyPrinter.ppTactic ⟨stx⟩).pretty
        let r' := (← Lean.PrettyPrinter.ppTactic ⟨r⟩).pretty
        if stx' != r' then
          throwError m!"Tactic `{tac}` produced `{stx'}`, but was expecting it to produce `{r'}`!"
    | none =>
    let stx : TSyntax ``tacticSeq := ⟨stx⟩
    addSuggestion tk (← `(tactic| $tac says $stx)) (origSpan? := (← `(tactic| $tac says)))
  | some result, false =>
    evalTactic result

initialize Std.Linter.UnreachableTactic.addIgnoreTacticKind `Mathlib.Tactic.Says.says
