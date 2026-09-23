import Mathlib.Tactic.StacksAttribute
import Mathlib.Util.ParseCommand

/-- info: No tags found. -/
#guard_msgs in
#stacks_tags

namespace X

@[stacks A04Q "A comment", kerodon B15R "Also a comment"]
theorem tagged : True := .intro

end X

/--
info: some ([Stacks Tag A04Q](https://stacks.math.columbia.edu/tag/A04Q) (A comment)

[Kerodon Tag B15R](https://kerodon.net/tag/B15R) (Also a comment))
-/
#guard_msgs in
run_cmd
  Lean.logInfo m!"{← Lean.findDocString? (← Lean.getEnv) `X.tagged}"

#guard_msgs in
@[stacks 0BR2, kerodon 0X12]
example : True := .intro

@[stacks 0BR2, stacks 0X14 "I can also have a comment"]
example : True := .intro

@[stacks 0X14 "I can also have a comment"]
example : True := .intro

@[stacks 0BR2, stacks 0X14 "I can also have a comment"]
example : True := .intro

@[stacks 0X14 "I can also have a comment"]
example : True := .intro

/-- error: <input>:1:3: Stacks tags must be exactly 4 characters -/
#guard_msgs in #parse Mathlib.StacksTag.stacksTagFn => "A05"

/-- error: <input>:1:4: Stacks tags must consist only of digits and uppercase letters. -/
#guard_msgs in #parse Mathlib.StacksTag.stacksTagFn => "A05b"

/-- info: 0BD5 -/
#guard_msgs in #parse Mathlib.StacksTag.stacksTagFn => "0BD5"

/--
info:
[Stacks Tag A04Q](https://stacks.math.columbia.edu/tag/A04Q) corresponds to declaration 'X.tagged'. (A comment)
-/
#guard_msgs in
#stacks_tags

/--
info:
[Stacks Tag A04Q](https://stacks.math.columbia.edu/tag/A04Q) corresponds to declaration 'X.tagged'. (A comment)
True
-/
#guard_msgs in
#stacks_tags!

/--
info:
[Stacks Tag B15R](https://kerodon.net/tag/B15R) corresponds to declaration 'X.tagged'. (Also a comment)
True
-/
#guard_msgs in
#kerodon_tags!

section errors

open Lean Parser Mathlib.StacksTag

def captureException (env : Environment) (s : ParserFn) (input : String) : Except String Syntax :=
  let ictx := mkInputContext input "<input>"
  let s := s.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if !s.allErrors.isEmpty then
    .error (s.toErrorMsg ictx)
  else if ictx.atEnd s.pos then
    .ok s.stxStack.back
  else
    .error ((s.mkError "end of input").toErrorMsg ictx)

/-- error: <input>:1:3: Stacks tags must be exactly 4 characters -/
#guard_msgs in
run_cmd do
  let _ ← Lean.ofExcept <| captureException (← getEnv) stacksTagFn "A05"

/-- error: <input>:1:4: Stacks tags must consist only of digits and uppercase letters. -/
#guard_msgs in
run_cmd do
  let _ ← Lean.ofExcept <| captureException (← getEnv) stacksTagFn "aaaa"

/-- error: <input>:1:0: expected stacks tag -/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let _ ← Lean.ofExcept <| captureException env stacksTagFn "\"A04Q\""

end errors
