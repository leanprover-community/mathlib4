/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
import Mathlib.Tactic.Lint.Basic

/-!
# Linter frontend and commands

This file defines the linter commands which spot common mistakes in the code.
* `#lint`: check all declarations in the current file
* `#lint mathlib`: check all declarations in mathlib (so excluding core or other projects,
  and also excluding the current file)
* `#lint all`: check all declarations in the environment (the current file and all
  imported files)

For a list of default / non-default linters, see the "Linting Commands" user command doc entry.

The command `#list_linters` prints a list of the names of all available linters.

You can append a `*` to any command (e.g. `#lint mathlib*`) to omit the slow tests (4).

You can append a `-` to any command (e.g. `#lint mathlib-`) to run a silent lint
that suppresses the output if all checks pass.
A silent lint will fail if any test fails.

You can append a `+` to any command (e.g. `#lint mathlib+`) to run a verbose lint
that reports the result of each linter, including  the successes.

You can append a sequence of linter names to any command to run extra tests, in addition to the
default ones. e.g. `#lint doc_blame_thm` will run all default tests and `doc_blame_thm`.

You can append `only name1 name2 ...` to any command to run a subset of linters, e.g.
`#lint only unused_arguments`

You can add custom linters by defining a term of type `Linter` in the `Mathlib.Tactic.Lint` namespace.
A linter defined with the name `Mathlib.Tactic.Lint.myNewCheck` can be run with `#lint myNewCheck`
or `lint only myNewCheck`.
If you add the attribute `@[mathlibLinter]` to `linter.myNewCheck` it will run by default.

Adding the attribute `@[nolint doc_blame unused_arguments]` to a declaration
omits it from only the specified linter checks.

## Tags

sanity check, lint, cleanup, command, tactic
-/

def Lean.TagAttribute.getDecls (attr : TagAttribute) (env : Environment) : Array Name := Id.run do
  let st := attr.ext.toEnvExtension.getState env
  let mut decls := st.state.toArray
  for ds in st.importedEntries do
    decls := decls ++ ds
  decls

namespace Mathlib.Tactic.Lint
open Lean Std

/--
Verbosity for the linter output.
* `low`: only print failing checks, print nothing on success.
* `medium`: only print failing checks, print confirmation on success.
* `high`: print output of every check.
-/
inductive LintVerbosity | low | medium | high
  deriving Inhabited, DecidableEq, Repr

/-- `getChecks slow extra use_only` produces a list of linters.
`extras` is a list of names that should resolve to declarations with type `linter`.
If `useOnly` is true, it only uses the linters in `extra`.
Otherwise, it uses all linters in the environment tagged with `@[linter]`.
If `slow` is false, it only uses the fast default tests. -/
def getChecks (slow : Bool) (extra : List Name) (useOnly : Bool) : CoreM (List NamedLinter) := do
  let default ← if useOnly then [] else
    getLinters (← mathlibLinterAttr.getDecls (← getEnv)).toList
  let default := if slow then default else default.filter (·.isFast)
  default ++ (← getLinters extra)

def lintCore (decls : Array Name) (linters : Array NamedLinter) :
    CoreM (Array (NamedLinter × HashMap Name MessageData)) := do
  let env ← getEnv
  let options ← getOptions -- TODO: sanitize options?

  let tasks : Array (NamedLinter × Array (Name × Task (Option MessageData))) ←
    linters.mapM fun linter => do
      let decls ← decls.filterM (shouldBeLinted linter.name)
      (linter, ·) <|<- decls.mapM fun decl => do (decl, ·) <|<- do
        BaseIO.asTask do
          match ← withCurrHeartbeats (linter.test decl)
              |>.run'.run' {options} {env} |>.toBaseIO with
          | Except.ok msg? => msg?
          | Except.error err => m!"LINTER FAILED:\n{err.toMessageData}"

  tasks.mapM fun (linter, decls) => do
    let mut msgs : HashMap Name MessageData := {}
    for (declName, msg?) in decls do
      if let some msg := msg?.get then
        msgs := msgs.insert declName msg
    (linter, msgs)

/-- Sorts a map with declaration keys as names by line number. -/
def sortResults {α} [Inhabited α] (results : HashMap Name α) : CoreM <| Array (Name × α) := do
  let mut key : HashMap Name Nat := {}
  for (n, _) in results.toArray do
    if let some range ← findDeclarationRanges? n then
      key := key.insert n <| range.range.pos.line
  results.toArray.qsort fun (a, _) (b, _) => key.findD a 0 < key.findD b 0

/-- Formats a linter warning as `#check` command with comment. -/
def printWarning (declName : Name) (warning : MessageData) : CoreM MessageData := do
  m!"#check @{← mkConstWithLevelParams declName} /- {warning} -/"

/-- Formats a map of linter warnings using `print_warning`, sorted by line number. -/
def printWarnings (results : HashMap Name MessageData) : CoreM MessageData := do
  (MessageData.joinSep ·.toList Format.line) <|<-
    (← sortResults results).mapM fun (declName, warning) => printWarning declName warning

/--
Formats a map of linter warnings grouped by filename with `-- filename` comments.
The first `drop_fn_chars` characters are stripped from the filename.
-/
def groupedByFilename (results : HashMap Name MessageData) : CoreM MessageData := do
  let mut grouped : HashMap Name (HashMap Name MessageData) := {}
  for (declName, msg) in results.toArray do
    let mod ← findModuleOf? declName
    let mod := mod.getD (← getEnv).mainModule
    grouped := grouped.insert mod <| grouped.findD mod {} |>.insert declName msg
  let grouped' := grouped.toArray.qsort fun (a, _) (b, _) => toString a < toString b
  (MessageData.joinSep · (Format.line ++ Format.line)) <|<-
    grouped'.toList.mapM fun (mod, msgs) => do
      m!"-- {mod}\n{← printWarnings msgs}"

/--
Formats the linter results as Lean code with comments and `#print` commands.
-/
def formatLinterResults
    (results : Array (NamedLinter × HashMap Name MessageData))
    (decls : Array Name)
    (groupByFilename : Bool)
    (whereDesc : String) (runSlowLinters : Bool)
    (verbose : LintVerbosity) (numLinters : Nat) :
    CoreM MessageData := do
  let formattedResults ← results.filterMapM fun (linter, results) => do
    if !results.isEmpty then
      let warnings ←
        if groupByFilename then
          groupedByFilename results
        else
          printWarnings results
      some m!"/- The `{linter.name}` linter reports:\n{linter.errorsFound} -/\n{warnings}\n"
    else if verbose = LintVerbosity.high then
      some m!"/- OK: {linter.noErrorsFound} -/"
    else
      none
  let mut s := MessageData.joinSep formattedResults.toList Format.line
  let numAutoDecls := (← decls.filterM isAutoDecl).size
  let failed := results.map (·.2.size) |>.foldl (·+·) 0
  unless verbose matches LintVerbosity.low do
    s := m!"-- Found {failed} error{if failed == 1 then "" else "s"
      } in {decls.size - numAutoDecls} declarations (plus {
      numAutoDecls} automatically generated ones) {whereDesc
      } with {numLinters} linters\n\n{s}"
  unless runSlowLinters do s := m!"{s}-- (slow linters skipped)\n"
  s

def getDeclsInCurrModule : CoreM (Array Name) := do
  (← getEnv).constants.map₂.toList.toArray.map (·.1)

def getAllDecls : CoreM (Array Name) := do
  (← getDeclsInCurrModule) ++
    (← getEnv).constants.map₁.toArray.map (·.1)

def getDeclsInMathlib : CoreM (Array Name) := do
  let mut decls ← getDeclsInCurrModule
  let mathlibModules := (← getEnv).header.moduleNames.map ((`Mathlib).isPrefixOf ·)
  for (declName, moduleIdx) in (← getEnv).const2ModIdx.toArray do
    if mathlibModules[moduleIdx] then
      decls := decls.push declName
  decls

open Elab Command in
elab "#lint"
    project:(&"mathlib" <|> &"all")?
    verbosity:("+" <|> "-")?
    fast:"*"?
    only:(&"only")? linters:(ident)*
    : command => do
  let (decls, whereDesc, groupByFilename) ← match project.getOptional? with
    | none => do (← liftCoreM getDeclsInCurrModule, "in the current file", false)
    | some (Syntax.atom _ "mathlib") => do (← liftCoreM getDeclsInMathlib, "in mathlib", true)
    | some (Syntax.atom _ "all") => do (← liftCoreM getAllDecls, "in all files", true)
    | _ => throwUnsupportedSyntax
  let verbosity : LintVerbosity ← match verbosity.getOptional? with
    | none => LintVerbosity.medium
    | some (Syntax.atom _ "+") => LintVerbosity.high
    | some (Syntax.atom _ "-") => LintVerbosity.low
    | _ => throwUnsupportedSyntax
  let fast := fast.getOptional?.isSome
  let only := only.getOptional?.isSome
  let extraLinters ← linters.getArgs.mapM fun id =>
    withScope ({ · with currNamespace := `Mathlib.Tactic.Lint }) <|
      resolveGlobalConstNoOverload id
  let linters ← liftCoreM <| getChecks (slow := !fast) extraLinters.toList only
  let results ← liftCoreM <| lintCore decls linters.toArray
  let failed := results.any (!·.2.isEmpty)
  let mut fmtResults ← liftCoreM <|
    formatLinterResults results decls (groupByFilename := groupByFilename)
      whereDesc (runSlowLinters := !fast) verbosity linters.length
  if failed then
    logError fmtResults
  else if verbosity != LintVerbosity.low then
    logInfo m!"{fmtResults}\n-- All linting checks passed!"

open Elab Command in
/-- The command `#list_linters` prints a list of all available linters. -/
elab "#list_linters" : command => do
  let env ← getEnv
  let ns : Array Name := env.constants.fold (init := #[]) fun ns n ci =>
    if n.getPrefix == `Mathlib.Tactic.Lint && ci.type == mkConst ``Mathlib.Tactic.Lint.Linter
      then ns.push n else ns
  let linters ← ns.mapM fun n => do
    let b := mathlibLinterAttr.hasTag (← getEnv) n
    toString (n.updatePrefix Name.anonymous) ++ if b then " (*)" else ""
  logInfo m!"Available linters (linters marked with (*) are in the default lint set):\n{Format.joinSep linters.toList Format.line}"
