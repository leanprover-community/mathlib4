/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Linter.Util
import Mathlib.Util.AssertExists

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

/-- `onlyImportsOneModDocAsserts stx` checks whether `stx` is the syntax for a module that
only consists of
* any number of `import` statements (possibly none) followed by
* any number of doc-module strings (possibly none) followed by
* any number of `assert_not_exists` commands (possibly none),

and nothing else.
-/
def onlyImportsModDocsAsserts : Syntax → Bool
  | .node _ ``Lean.Parser.Module.module #[_header, .node _ `null args] =>
    let dropDocs := args.toList.dropWhile (·.isOfKind ``Lean.Parser.Command.moduleDoc)
    let dropAssertNotExists := dropDocs.dropWhile (·.isOfKind ``commandAssert_not_exists_)
    dropAssertNotExists.isEmpty
  | _=> false

/-- `onlyImportsOneModDoc stx` checks whether `stx` is the syntax for a module that
only consists of
* any number of `import` statements (possibly none) followed by
* at least one doc-module strings.
-/
def onlyImportsOneModDoc : Syntax → Bool
  | .node _ ``Lean.Parser.Module.module #[_header, .node _ `null args] =>
    (args.getD 0 default).isOfKind ``Lean.Parser.Command.moduleDoc
  | _=> false

/-- `parseUpToHere stx post` takes as input a `Syntax` `stx` and a `String` `post`.
It parses the file containing `stx` up to and excluding `stx`, appending `post` at the end.

The option of appending a final string to the text gives more control to avoid syntax errors,
for instance in the presence of `#guard_msgs in` or `set_option ... in`.
-/
def parseUpToHere (stx : Syntax) (post : String := "") : CommandElabM Syntax := do
  let fm ← getFileMap
  let startPos := stx.getPos?.getD default
  let upToHere : Substring:= { str := fm.source, startPos := ⟨0⟩, stopPos := startPos}
  -- append a further string after the `upToHere` content
  Parser.testParseModule (← getEnv) "linter.assertNotExists" (upToHere.toString ++ post)

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

namespace Style.AssertNotExists

/-- Gets the value of the `linter.assertNotExists` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.assertNotExists o

@[inherit_doc Mathlib.Linter.linter.assertNotExists]
def assertNotExistsLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterHash (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  unless stx.isOfKind ``commandAssert_not_exists_ do return
  let upToStx ← parseUpToHere stx "\nassert_not_exists XXX" <|> return Syntax.missing
  if ! onlyImportsModDocsAsserts upToStx then
    Linter.logLint linter.assertNotExists stx
      m!"`{stx}` appears too late: it can only be preceded by `import` statements \
      doc-module strings and other `assert_not_exists` statements."

initialize addLinter assertNotExistsLinter

end Style.AssertNotExists

/--
The "docModuleString" linter checks that a file starts with
```
import*
/-! doc-module -/
```
It emits a warning if a file does not have a doc-module string right after the `import`s.
-/
register_option linter.docModuleString : Bool := {
  defValue := true
  descr := "enable the docModuleString linter"
}

namespace Style.DocModuleString

--/-- Gets the value of the `linter.docModuleString` option. -/
--def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.docModuleString o

#check Lean.Parser.Command.exit

@[inherit_doc Mathlib.Linter.linter.docModuleString]
def docModuleStringLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterHash (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  if stx.isOfKind ``Lean.Parser.Command.moduleDoc then return
  let upToStx ← parseUpToHere stx "\nassert_not_exists XXX" <|> return Syntax.missing
  if ! onlyImportsOneModDoc upToStx then
    logInfoAt stx "no docs!!"
  --if ! onlyImportsModDocsAsserts upToStx then
    Linter.logLint linter.docModuleString stx
      m!"`{stx}` appears too late: it can only be preceded by `import` statements \
      doc-module strings and other `assert_not_exists` statements."

initialize addLinter docModuleStringLinter

end Style.DocModuleString

end Mathlib.Linter
