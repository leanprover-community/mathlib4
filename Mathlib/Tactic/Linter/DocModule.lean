/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Lean.Linter.Util

/-!
The "docModuleString" style linter checks that a file starts with
```
import*
/-! doc-module -/
```
It emits a warning if a file does not have a doc-module string right after the `import`s.
-/

open Lean Elab

namespace Mathlib.Linter

/-- `onlyImportsOneModDoc stx` checks whether `stx` is the syntax for a module that
only consists of
* any number of `import` statements (possibly none) followed by
* at least one doc-module strings.
-/
def onlyImportsOneModDoc : Syntax → Bool
  | .node _ ``Lean.Parser.Module.module #[_header, .node _ `null args] =>
    (args.getD 0 default).isOfKind ``Lean.Parser.Command.moduleDoc
  | _=> false

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

/-- `firstCommand?` keeps track of whether the linter is parsing the first command *after* the
imports or not. -/
structure firstCommand? where
  f : Bool
  deriving Inhabited

initialize myfirstCommand? : Lean.EnvExtension firstCommand? ← Lean.registerEnvExtension (pure ⟨true⟩)

namespace Style.DocModuleString

/-- Gets the value of the `linter.docModuleString` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.docModuleString o

@[inherit_doc Mathlib.Linter.linter.docModuleString]
def docModuleStringLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterHash (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  if (myfirstCommand?.getState (← getEnv)).f then
    setEnv <| myfirstCommand?.setState (← getEnv) ⟨false⟩
    dbg_trace (myfirstCommand?.getState (← getEnv)).f
    if !stx.isOfKind ``Lean.Parser.Command.moduleDoc then
      Linter.logLint linter.docModuleString stx
        m!"Add the doc-module string before this command\n\
          `{stx.getKind}` appears too late: it can only be preceded by `import` statements \
          doc-module strings and other `assert_not_exists` statements."
    --let x := linter.docModuleString.set (← getOptions) 1
    --dbg_trace "Options: {x}"
    --(← getOptions).set ``linter.docModuleString 1
    --return

--  let upToStx ← parseUpToHere stx "\nassert_not_exists XXX" <|> return Syntax.missing
--  if ! onlyImportsOneModDoc upToStx then

initialize addLinter docModuleStringLinter

end Style.DocModuleString

end Mathlib.Linter
