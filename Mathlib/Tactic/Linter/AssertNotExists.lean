/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Util.AssertExists
import Lean.Linter.Util

/-!
#  The "assertNotExists" linter

The "assertNotExists" linter checks that a file starts with
```
import*
doc-module*
assert_not_exists*
[no more assert_not_exists]
```
It emits a warning on each `assert_not_exists` that is not preceded by
* possibly some import statements,
* possibly some doc-module strings, and
* possibly some `assert_not_exists` commands

in this order.
-/

open Lean Elab Command

namespace Mathlib.Linter

def onlyImportsOneModDocAsserts : Syntax → Bool
  | .node _ ``Lean.Parser.Module.module #[_header, .node _ `null args] =>
    let dropDocs := args.toList.dropWhile (·.isOfKind ``Lean.Parser.Command.moduleDoc)
    let dropAssertNotExists := dropDocs.dropWhile (·.isOfKind ``commandAssert_not_exists_)
    dropAssertNotExists.isEmpty
  | _=> false

def parseUpToHere (stx : Syntax) : CommandElabM Syntax := do
  let fm ← getFileMap
  let startPos := stx.getPos?.getD default
  let before : Substring:= { str := fm.source, startPos := ⟨0⟩, stopPos := startPos}
  Parser.testParseModule (← getEnv) "linter.assertNotExists"
    -- add a "fake" `assert_not_exists XXX` so that `#guard_msgs in` can be used to test
    (before.toString ++ "\nassert_not_exists XXX")

/--
The "assertNotExists" linter checks that a file starts with
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
register_option linter.assertNotExists : Bool := {
  defValue := true
  descr := "enable the assertNotExists linter"
}

namespace AssertNotExists

/-- Gets the value of the `linter.assertNotExists` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.assertNotExists o

@[inherit_doc Mathlib.Linter.linter.assertNotExists]
def assertNotExistsLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    unless stx.isOfKind ``commandAssert_not_exists_ do return
    let upToStx ← parseUpToHere stx <|> return Syntax.missing
    if ! onlyImportsOneModDocAsserts upToStx then
      Linter.logLint linter.assertNotExists stx
        m!"`{stx}` appears too late: it can only be preceded by `import` statements \
        doc-module strings and other `assert_not_exists` statements."

initialize addLinter assertNotExistsLinter

end AssertNotExists

end Mathlib.Linter
