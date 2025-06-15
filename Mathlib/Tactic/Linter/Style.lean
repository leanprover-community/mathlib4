/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header
import Mathlib.Tactic.DeclarationNames

/-!
## Style linters

This file contain linters about stylistic aspects: these are only about coding style,
but do not affect correctness nor global coherence of mathlib.
Historically, some of these were ported from the `lint-style.py` Python script.

This file defines the following linters:
- the `setOption` linter checks for the presence of `set_option` commands activating
  options disallowed in mathlib: these are meant to be temporary, and not for polished code.
  It also checks for `maxHeartbeats` options being present which are not scoped to single commands.
- the `missingEnd` linter checks for sections or namespaces which are not closed by the end
  of the file: enforcing this invariant makes minimising files or moving code between files easier
- the `cdotLinter` linter checks for focusing dots `·` which are typed using a `.` instead:
  this is allowed Lean syntax, but it is nicer to be uniform
- the `dollarSyntax` linter checks for use of the dollar sign `$` instead of the `<|` pipe operator:
  similarly, both symbols have the same meaning, but mathlib prefers `<|` for the symmetry with
  the `|>` symbol
- the `lambdaSyntax` linter checks for uses of the `λ` symbol for anonymous functions,
  instead of the `fun` keyword: mathlib prefers the latter for reasons of readability
- the `longFile` linter checks for files which have more than 1500 lines
- the `longLine` linter checks for lines which have more than 100 characters
- the `openClassical` linter checks for `open (scoped) Classical` statements which are not
  scoped to a single declaration

All of these linters are enabled in mathlib by default, but disabled globally
since they enforce conventions which are inherently subjective.
-/

open Lean Parser Elab Command Meta Linter

namespace Mathlib.Linter

/-- The `setOption` linter emits a warning on a `set_option` command, term or tactic
which sets a `pp`, `profiler` or `trace` option.
It also warns on an option containing `maxHeartbeats`
(as these should be scoped as `set_option ... in` instead). -/
register_option linter.style.setOption : Bool := {
  defValue := false
  descr := "enable the `setOption` linter"
}

namespace Style.setOption

/-- Whether a syntax element is a `set_option` command, tactic or term:
Return the name of the option being set, if any. -/
def parseSetOption : Syntax → Option Name
  -- This handles all four possibilities of `_val`: a string, number, `true` and `false`.
  | `(command|set_option $name:ident $_val) => some name.getId
  | `(set_option $name:ident $_val in $_x) => some name.getId
  | `(tactic|set_option $name:ident $_val in $_x) => some name.getId
  | _ => none

/-- Deprecated alias for `Mathlib.Linter.Style.setOption.parseSetOption`. -/
@[deprecated parseSetOption (since := "2024-12-07")]
def parse_set_option := @parseSetOption

/-- Whether a given piece of syntax is a `set_option` command, tactic or term. -/
def isSetOption : Syntax → Bool :=
  fun stx ↦ parseSetOption stx matches some _name

/-- Deprecated alias for `Mathlib.Linter.Style.setOption.isSetOption`. -/
@[deprecated isSetOption (since := "2024-12-07")]
def is_set_option := @isSetOption

/-- The `setOption` linter: this lints any `set_option` command, term or tactic
which sets a `debug`, `pp`, `profiler` or `trace` option.
This also warns if an option containing `maxHeartbeats` (typically, the `maxHeartbeats` or
`synthInstance.maxHeartbeats` option) is set.

**Why is this bad?** The `debug`, `pp`, `profiler` and `trace` options are good for debugging,
but should not be used in production code.

`maxHeartbeats` options should be scoped as `set_option opt in ...` (and be followed by a comment
explaining the need for them; another linter enforces this).

**How to fix this?** The `maxHeartbeats` options can be scoped to individual commands, if they
are truly necessary.

The `debug`, `pp`, `profiler` and `trace` are usually not necessary for production code,
so you can simply remove them. (Some tests will intentionally use one of these options;
in this case, simply allow the linter.)
-/
def setOptionLinter : Linter where run := withSetOptionIn fun stx => do
    unless getLinterValue linter.style.setOption (← getLinterOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    if let some head := stx.find? isSetOption then
      if let some name := parseSetOption head then
        let forbidden := [`debug, `pp, `profiler, `trace]
        if forbidden.contains name.getRoot then
          Linter.logLint linter.style.setOption head
            m!"Setting options starting with '{"', '".intercalate (forbidden.map (·.toString))}' \
               is only intended for development and not for final code. \
               If you intend to submit this contribution to the Mathlib project, \
               please remove 'set_option {name}'."
        else if name.components.contains `maxHeartbeats then
          Linter.logLint linter.style.setOption head m!"Unscoped option {name} is not allowed:\n\
          Please scope this to individual declarations, as in\n```\nset_option {name} in\n\
          -- comment explaining why this is necessary\n\
          example : ... := ...\n```"

initialize addLinter setOptionLinter

end Style.setOption

/-!
# The "missing end" linter

The "missing end" linter emits a warning on non-closed `section`s and `namespace`s.
It allows the "outermost" `noncomputable section` to be left open (whether or not it is named).
-/

open Lean Elab Command

/-- The "missing end" linter emits a warning on non-closed `section`s and `namespace`s.
It allows the "outermost" `noncomputable section` to be left open (whether or not it is named).
-/
register_option linter.style.missingEnd : Bool := {
  defValue := false
  descr := "enable the missing end linter"
}

namespace Style.missingEnd

@[inherit_doc Mathlib.Linter.linter.style.missingEnd]
def missingEndLinter : Linter where run := withSetOptionIn fun stx ↦ do
    -- Only run this linter at the end of a module.
    unless stx.isOfKind ``Lean.Parser.Command.eoi do return
    if getLinterValue linter.style.missingEnd (← getLinterOptions) &&
        !(← MonadState.get).messages.hasErrors then
      let sc ← getScopes
      -- The last scope is always the "base scope", corresponding to no active `section`s or
      -- `namespace`s. We are interested in any *other* unclosed scopes.
      if sc.length == 1 then return
      let ends := sc.dropLast.map fun s ↦ (s.header, s.isNoncomputable)
      -- If the outermost scope corresponds to a `noncomputable section`, we ignore it.
      let ends := if ends.getLast!.2 then ends.dropLast else ends
      -- If there are any further un-closed scopes, we emit a warning.
      if !ends.isEmpty then
        let ending := (ends.map Prod.fst).foldl (init := "") fun a b ↦
          a ++ s!"\n\nend{if b == "" then "" else " "}{b}"
        Linter.logLint linter.style.missingEnd stx
         m!"unclosed sections or namespaces; expected: '{ending}'"

initialize addLinter missingEndLinter

end Style.missingEnd

/-!
# The `cdot` linter

The `cdot` linter is a syntax-linter that flags uses of the "cdot" `·` that are achieved
by typing a character different from `·`.
For instance, a "plain" dot `.` is allowed syntax, but is flagged by the linter.
It also flags "isolated cdots", i.e. when the `·` is on its own line.
-/

/--
The `cdot` linter flags uses of the "cdot" `·` that are achieved by typing a character
different from `·`.
For instance, a "plain" dot `.` is allowed syntax, but is flagged by the linter.
It also flags "isolated cdots", i.e. when the `·` is on its own line. -/
register_option linter.style.cdot : Bool := {
  defValue := false
  descr := "enable the `cdot` linter"
}

/-- `isCDot? stx` checks whether `stx` is a `Syntax` node corresponding to a `cdot` typed with
the character `·`. -/
def isCDot? : Syntax → Bool
  | .node _ ``cdotTk #[.node _ `patternIgnore #[.node _ _ #[.atom _ v]]] => v == "·"
  | .node _ ``Lean.Parser.Term.cdot #[.atom _ v] => v == "·"
  | _ => false

/--
`findCDot stx` extracts from `stx` the syntax nodes of `kind` `Lean.Parser.Term.cdot` or `cdotTk`.
-/
partial
def findCDot : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let dargs := (args.map findCDot).flatten
    match kind with
      | ``Lean.Parser.Term.cdot | ``cdotTk => dargs.push stx
      | _ =>  dargs
  |_ => #[]

/-- `unwanted_cdot stx` returns an array of syntax atoms within `stx`
corresponding to `cdot`s that are not written with the character `·`.
This is precisely what the `cdot` linter flags.
-/
def unwanted_cdot (stx : Syntax) : Array Syntax :=
  (findCDot stx).filter (!isCDot? ·)

namespace Style

@[inherit_doc linter.style.cdot]
def cdotLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless getLinterValue linter.style.cdot (← getLinterOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    for s in unwanted_cdot stx do
      Linter.logLint linter.style.cdot s
        m!"Please, use '·' (typed as `\\.`) instead of '{s}' as 'cdot'."
    -- We also check for isolated cdot's, i.e. when the cdot is on its own line.
    for cdot in Mathlib.Linter.findCDot stx do
      match cdot.find? (·.isOfKind `token.«· ») with
      | some (.node _ _ #[.atom (.original _ _ afterCDot _) _]) =>
        if (afterCDot.takeWhile (·.isWhitespace)).contains '\n' then
          Linter.logLint linter.style.cdot cdot
            m!"This central dot `·` is isolated; please merge it with the next line."
      | _ => return

initialize addLinter cdotLinter

end Style

/-!
# The `dollarSyntax` linter

The `dollarSyntax` linter flags uses of `<|` that are achieved by typing `$`.
These are disallowed by the mathlib style guide, as using `<|` pairs better with `|>`.
-/

/-- The `dollarSyntax` linter flags uses of `<|` that are achieved by typing `$`.
These are disallowed by the mathlib style guide, as using `<|` pairs better with `|>`. -/
register_option linter.style.dollarSyntax : Bool := {
  defValue := false
  descr := "enable the `dollarSyntax` linter"
}

namespace Style.dollarSyntax

/-- `findDollarSyntax stx` extracts from `stx` the syntax nodes of `kind` `$`. -/
partial
def findDollarSyntax : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let dargs := (args.map findDollarSyntax).flatten
    match kind with
      | ``«term_$__» => dargs.push stx
      | _ => dargs
  |_ => #[]

@[inherit_doc linter.style.dollarSyntax]
def dollarSyntaxLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless getLinterValue linter.style.dollarSyntax (← getLinterOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    for s in findDollarSyntax stx do
      Linter.logLint linter.style.dollarSyntax s
        m!"Please use '<|' instead of '$' for the pipe operator."

initialize addLinter dollarSyntaxLinter

end Style.dollarSyntax

/-!
# The `lambdaSyntax` linter

The `lambdaSyntax` linter is a syntax linter that flags uses of the symbol `λ` to define anonymous
functions, as opposed to the `fun` keyword. These are syntactically equivalent; mathlib style
prefers the latter as it is considered more readable.
-/

/--
The `lambdaSyntax` linter flags uses of the symbol `λ` to define anonymous functions.
This is syntactically equivalent to the `fun` keyword; mathlib style prefers using the latter.
-/
register_option linter.style.lambdaSyntax : Bool := {
  defValue := false
  descr := "enable the `lambdaSyntax` linter"
}

namespace Style.lambdaSyntax

/--
`findLambdaSyntax stx` extracts from `stx` all syntax nodes of `kind` `Term.fun`. -/
partial
def findLambdaSyntax : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let dargs := (args.map findLambdaSyntax).flatten
    match kind with
      | ``Parser.Term.fun => dargs.push stx
      | _ =>  dargs
  |_ => #[]

@[inherit_doc linter.style.lambdaSyntax]
def lambdaSyntaxLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless getLinterValue linter.style.lambdaSyntax (← getLinterOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    for s in findLambdaSyntax stx do
      if let .atom _ "λ" := s[0] then
        Linter.logLint linter.style.lambdaSyntax s[0] m!"\
        Please use 'fun' and not 'λ' to define anonymous functions.\n\
        The 'λ' syntax is deprecated in mathlib4."

initialize addLinter lambdaSyntaxLinter

end Style.lambdaSyntax

/-!
#  The "longFile" linter

The "longFile" linter emits a warning on files which are longer than a certain number of lines
(1500 by default).
-/

/--
The "longFile" linter emits a warning on files which are longer than a certain number of lines
(`linter.style.longFileDefValue` by default on mathlib, no limit for downstream projects).
If this option is set to `N` lines, the linter warns once a file has more than `N` lines.
A value of `0` silences the linter entirely.
-/
register_option linter.style.longFile : Nat := {
  defValue := 0
  descr := "enable the longFile linter"
}

/-- The number of lines that the `longFile` linter considers the default. -/
register_option linter.style.longFileDefValue : Nat := {
  defValue := 1500
  descr := "a soft upper bound on the number of lines of each file"
}

namespace Style.longFile

@[inherit_doc Mathlib.Linter.linter.style.longFile]
def longFileLinter : Linter where run := withSetOptionIn fun stx ↦ do
  let linterBound := linter.style.longFile.get (← getOptions)
  if linterBound == 0 then
    return
  let defValue := linter.style.longFileDefValue.get (← getOptions)
  let smallOption := match stx with
      | `(set_option linter.style.longFile $x) => TSyntax.getNat ⟨x.raw⟩ ≤ defValue
      | _ => false
  if smallOption then
    logLint0Disable linter.style.longFile stx
      m!"The default value of the `longFile` linter is {defValue}.\n\
        The current value of {linterBound} does not exceed the allowed bound.\n\
        Please, remove the `set_option linter.style.longFile {linterBound}`."
  else
  -- Thanks to the above check, the linter option is either not set (and hence equal
  -- to the default) or set to some value *larger* than the default.
  -- `Parser.isTerminalCommand` allows `stx` to be `#exit`: this is useful for tests.
  unless Parser.isTerminalCommand stx do return
  -- We exclude `Mathlib.lean` from the linter: it exceeds linter's default number of allowed
  -- lines, and it is an auto-generated import-only file.
  -- TODO: if there are more such files, revise the implementation.
  if (← getMainModule) == `Mathlib then return
  if let some init := stx.getTailPos? then
    -- the last line: we subtract 1, since the last line is expected to be empty
    let lastLine := ((← getFileMap).toPosition init).line
    -- In this case, the file has an allowed length, and the linter option is unnecessarily set.
    if lastLine ≤ defValue && defValue < linterBound then
      logLint0Disable linter.style.longFile stx
        m!"The default value of the `longFile` linter is {defValue}.\n\
          This file is {lastLine} lines long which does not exceed the allowed bound.\n\
          Please, remove the `set_option linter.style.longFile {linterBound}`."
    else
    -- `candidate` is divisible by `100` and satisfies `lastLine + 100 < candidate ≤ lastLine + 200`
    -- note that either `lastLine ≤ defValue` and `defValue = linterBound` hold or
    -- `candidate` is necessarily bigger than `lastLine` and hence bigger than `defValue`
    let candidate := (lastLine / 100) * 100 + 200
    let candidate := max candidate defValue
    -- In this case, the file is longer than the default and also than what the option says.
    if defValue ≤ linterBound && linterBound < lastLine then
      logLint0Disable linter.style.longFile stx
        m!"This file is {lastLine} lines long, but the limit is {linterBound}.\n\n\
          You can extend the allowed length of the file using \
          `set_option linter.style.longFile {candidate}`.\n\
          You can completely disable this linter by setting the length limit to `0`."
    else
    -- Finally, the file exceeds the default value, but not the option: we only allow the value
    -- of the option to be `candidate` or `candidate + 100`.
    -- In particular, this flags any option that is set to an unnecessarily high value.
    if linterBound == candidate || linterBound + 100 == candidate then return
    else
      logLint0Disable linter.style.longFile stx
        m!"This file is {lastLine} lines long. \
          The current limit is {linterBound}, but it is expected to be {candidate}:\n\
          `set_option linter.style.longFile {candidate}`."

initialize addLinter longFileLinter

end Style.longFile

/-! # The "longLine linter" -/

/-- The "longLine" linter emits a warning on lines longer than 100 characters.
We allow lines containing URLs to be longer, though. -/
register_option linter.style.longLine : Bool := {
  defValue := false
  descr := "enable the longLine linter"
}

namespace Style.longLine

@[inherit_doc Mathlib.Linter.linter.style.longLine]
def longLineLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless getLinterValue linter.style.longLine (← getLinterOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    -- The linter ignores the `#guard_msgs` command, in particular its doc-string.
    -- The linter still lints the message guarded by `#guard_msgs`.
    if stx.isOfKind ``Lean.guardMsgsCmd then
      return
    -- if the linter reached the end of the file, then we scan the `import` syntax instead
    let stx := ← do
      if stx.isOfKind ``Lean.Parser.Command.eoi then
        let fileMap ← getFileMap
        -- `impMods` is the syntax for the modules imported in the current file
        let (impMods, _) ← Parser.parseHeader
          { input := fileMap.source, fileName := ← getFileName, fileMap := fileMap }
        return impMods.raw
      else return stx
    let sstr := stx.getSubstring?
    let fm ← getFileMap
    let longLines := ((sstr.getD default).splitOn "\n").filter fun line ↦
      (100 < (fm.toPosition line.stopPos).column)
    for line in longLines do
      if (line.splitOn "http").length ≤ 1 then
        let stringMsg := if line.contains '"' then
          "\nYou can use \"string gaps\" to format long strings: within a string quotation, \
          using a '\\' at the end of a line allows you to continue the string on the following \
          line, removing all intervening whitespace."
        else ""
        Linter.logLint linter.style.longLine (.ofRange ⟨line.startPos, line.stopPos⟩)
          m!"This line exceeds the 100 character limit, please shorten it!{stringMsg}"
initialize addLinter longLineLinter

end Style.longLine

/-- The `nameCheck` linter emits a warning on declarations whose name is non-standard style.
(Currently, this only includes declarations whose name includes a double underscore.)

**Why is this bad?** Double underscores in theorem names can be considered non-standard style and
probably have been introduced by accident.
**How to fix this?** Use single underscores to separate parts of a name, following standard naming
conventions.
-/
register_option linter.style.nameCheck : Bool := {
  defValue := true
  descr := "enable the `nameCheck` linter"
}

namespace Style.nameCheck

@[inherit_doc linter.style.nameCheck]
def doubleUnderscore: Linter where run := withSetOptionIn fun stx => do
    unless getLinterValue linter.style.nameCheck (← getLinterOptions) do
      return
    if (← get).messages.hasErrors then
      return
    let mut aliases := #[]
    if let some exp := stx.find? (·.isOfKind `Lean.Parser.Command.export) then
      aliases ← getAliasSyntax exp
    for id in aliases.push ((stx.find? (·.isOfKind ``declId)).getD default)[0] do
      let declName := id.getId
      if id.getPos? == some default then continue
      if declName.hasMacroScopes then continue
      if id.getKind == `ident then
        -- Check whether the declaration name contains "__".
        if 1 < (declName.toString.splitOn "__").length then
          Linter.logLint linter.style.nameCheck id
            m!"The declaration '{id}' contains '__', which does not follow the mathlib naming \
              conventions. Consider using single underscores instead."

initialize addLinter doubleUnderscore

end Style.nameCheck

/-! # The "openClassical" linter -/

/-- The "openClassical" linter emits a warning on `open Classical` statements which are not
scoped to a single declaration. A non-scoped `open Classical` can hide that some theorem statements
would be better stated with explicit decidability statements.
-/
register_option linter.style.openClassical : Bool := {
  defValue := false
  descr := "enable the openClassical linter"
}

namespace Style.openClassical

/-- If `stx` is syntax describing an `open` command, `extractOpenNames stx`
returns an array of the syntax corresponding to the opened names,
omitting any renamed or hidden items.

This only checks independent `open` commands: for `open ... in ...` commands,
this linter returns an empty array.
-/
def extractOpenNames : Syntax → Array (TSyntax `ident)
  | `(command|$_ in $_) => #[] -- redundant, for clarity
  | `(command|open $decl:openDecl) => match decl with
    | `(openDecl| $arg hiding $_*)    => #[arg]
    | `(openDecl| $arg renaming $_,*) => #[arg]
    | `(openDecl| $arg ($_*))         => #[arg]
    | `(openDecl| $args*)             => args
    | `(openDecl| scoped $args*)      => args
    | _ => unreachable!
  | _ => #[]

@[inherit_doc Mathlib.Linter.linter.style.openClassical]
def openClassicalLinter : Linter where run stx := do
    unless getLinterValue linter.style.openClassical (← getLinterOptions) do
      return
    if (← get).messages.hasErrors then
      return
    -- If `stx` describes an `open` command, extract the list of opened namespaces.
    for stxN in (extractOpenNames stx).filter (·.getId == `Classical) do
      Linter.logLint linter.style.openClassical stxN "\
      please avoid 'open (scoped) Classical' statements: this can hide theorem statements \
      which would be better stated with explicit decidability statements.\n\
      Instead, use `open Classical in` for definitions or instances, the `classical` tactic \
      for proofs.\nFor theorem statements, \
      either add missing decidability assumptions or use `open Classical in`."

initialize addLinter openClassicalLinter

end Style.openClassical

end Mathlib.Linter
