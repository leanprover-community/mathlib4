/-
Copyright (c) 2024 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard, Damiano Testa
-/

import Lean.Elab.Command

/-!
# `#guard_exceptions` -- an analogue of `#guard_msgs` for parsers
-/

namespace Mathlib.GuardExceptions

open Lean Parser Elab Command
/-- `captureException env s input` uses the given `Environment` `env` to parse the `String` `input`
using the `ParserFn` `s`. -/
def captureException (env : Environment) (s : ParserFn) (input : String) : Except String Syntax :=
  let ictx := mkInputContext input "<input>"
  let s := s.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if !s.allErrors.isEmpty then
    .error (s.toErrorMsg ictx)
  else if ictx.input.atEnd s.pos then
    .ok s.stxStack.back
  else
    .error ((s.mkError "end of input").toErrorMsg ictx)

/-- `#guard_exceptions in` is based on `#guard_msgs in`, except that it captures parsing exceptions.

Typing `#guard_exceptions in parserFn input` uses `parserFn` to parse `input` and reports
either an error or

You can use it as follows
```lean
/-- error: <input>:1:3: Stacks tags must be exactly 4 characters -/
#guard_exceptions in Mathlib.Stacks.stacksTagFn "A05"
```
-/
syntax (name := guardExceptionsCmd)
  (docComment)? "#guard_exceptions" (ppSpace guardMsgsSpec)? " in" ppLine
  ident ppSpace str : command

@[inherit_doc guardExceptionsCmd]
elab_rules : command
  | `(command| $[$d:docComment]? #guard_exceptions $[$spec]? in $parser $str) => do
    elabCommand <| ← `(command|
      $[$d:docComment]? #guard_msgs $[$spec]? in
      run_cmd do
        let exc ← Lean.ofExcept <| captureException (← getEnv) $parser $str
        logInfo $str)

end Mathlib.GuardExceptions
