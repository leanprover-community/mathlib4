/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Linter.Util
import Mathlib.Util.AssertExists
import Mathlib.adomaniLeanUtils.inspect_syntax

/-!
#  The "header" linter

The "header" style linter checks that a file starts with
```
/-
Copyright ...
Apache ...
Authors ...
-/

import*
module doc-string*
rest
```
It emits a warning if the first non-`import` command is not a module doc-string.
-/

open Lean Elab Command

namespace Mathlib.Linter

/-- `onlyImportsModDocsAsserts stx` checks whether `stx` is the syntax for a module that
only consists of
* any number of `import` statements (possibly none) followed by
* any number of doc-module strings (possibly none) followed by
* any number of `assert_not_exists` commands (possibly none),

and nothing else.
-/
def onlyImportsModDocsAsserts : Syntax → Bool
  | .node _ ``Lean.Parser.Module.module #[_header, .node _ `null args] =>
    let args := args.toList.dropWhile (·.isOfKind ``Lean.Parser.Command.section)
    let first := args.getD 0 default

    dbg_trace first.getKind
    first.isOfKind ``Lean.Parser.Command.moduleDoc
    --let dropDocs := args.toList.dropWhile (·.isOfKind ``Lean.Parser.Command.moduleDoc)
    --let dropAssertNotExists := dropDocs.dropWhile (·.isOfKind ``commandAssert_not_exists_)
    --dropAssertNotExists.isEmpty
  | _=> false

/-- `parseUpToHere stx post` takes as input a `Syntax` `stx` and a `String` `post`.
It parses the file containing `stx` up to and excluding `stx`, appending `post` at the end.

The option of appending a final string to the text gives more control to avoid syntax errors,
for instance in the presence of `#guard_msgs in` or `set_option ... in`.
-/
def parseUpToHere (stx : Syntax) (post : String := "") : CommandElabM Syntax := do
  let fm ← getFileMap
  let startPos := stx.getTailPos?.getD default
  let upToHere : Substring:= { str := fm.source, startPos := ⟨0⟩, stopPos := startPos}
  -- append a further string after the `upToHere` content
  Parser.testParseModule (← getEnv) "linter.header" (upToHere.toString ++ post)

/--
The "header" style linter checks that a file starts with
```
import*
/-! doc-module -/*
assert_not_exists*
[no more `assert_not_exists`]
```
It emits a warning on each `assert_not_exists` that is not preceded by
* possibly some `import` statements,
* possibly some doc-module strings, and
* possibly some `assert_not_exists` commands

in this order.
-/
register_option linter.style.header : Bool := {
  defValue := true
  descr := "enable the header linter"
}

initialize firstCommand : IO.Ref (Option String.Pos) ← IO.mkRef none


namespace Style.AssertNotExists

/-- Gets the value of the `linter.header` option. -/
def getLinterAssertNotExists (o : Options) : Bool :=
  Linter.getLinterValue linter.style.header o
#check Syntax.getTrailingSize
@[inherit_doc Mathlib.Linter.linter.style.header]
def headerLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterAssertNotExists (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  --unless stx.isOfKind ``commandAssert_not_exists_ do return
  --dbg_trace "Starting position of syntax: {stx.getPos?}"
  let mut firstPos ← firstCommand.get
  --dbg_trace "Current value of ref: {firstPos}"
  let offset : String.Pos := ⟨3⟩
  if firstPos.isNone then
    let upToStx ← parseUpToHere stx <|> return Syntax.missing
    --dbg_trace "trailingSize: {upToStx.getTrailingSize}"
    Meta.inspect upToStx

    firstCommand.set upToStx.getTailPos?
    --dbg_trace "New value of ref: {upToStx.getTailPos?}"
    firstPos := upToStx.getTailPos?
  if stx.getPos?.getD 0 ≤ firstPos.getD 0 + offset then
    firstCommand.set stx.getPos?
    let upToStx ← parseUpToHere stx <|> return Syntax.missing
    if ! onlyImportsModDocsAsserts upToStx then
      Linter.logLint linter.style.header stx
        m!"`{stx}` appears too late: it can only be preceded by `import` statements \
        doc-module strings and other `assert_not_exists` statements."
    else return
--  else


initialize addLinter headerLinter

end Style.AssertNotExists

end Mathlib.Linter
