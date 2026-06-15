/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Damiano Testa, Thomas R. Murrills
-/
module

public meta import Lean.Elab.Command
public meta import Std.Sync.Mutex
public import Lean.Parser.Module
public import Mathlib.Tactic.Linter.DirectoryDependency

/-!
# The "header" linter

The "header" style linter checks that a file starts with
```
/-
Copyright ...
Apache ...
Authors ...
-/

import statements*

module doc-string*

remaining file
```
It emits a warning if
* the copyright statement is malformed;
* `Mathlib.Tactic` is imported;
* any import in `Lake` is present;
* the first non-`import` command is not a module doc-string.

The linter allows `import`-only files and does not require a copyright statement in `Mathlib.Init`.

## Implementation

The linter checks if it is linting the first command or not by (quickly) parsing the imports, and
checking whether the end position of the header is the same as the start position of the current
command. If so, it re-parses the header more slowly and checks that the current (first) command is
a module doc-string (unless the command is exempted for some reason).
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- `toSyntax s pattern` converts the two input strings into a `Syntax`, assuming that `pattern`
is a substring of `s`:
the syntax is an atom with value `pattern` whose the range is the range of `pattern` in `s`. -/
def toSyntax (s pattern : String) (offset : String.Pos.Raw := 0) : Syntax :=
  let beg := ((s.splitOn pattern).getD 0 "").rawEndPos.offsetBy offset
  let fin := (((s.splitOn pattern).getD 0 "") ++ pattern).rawEndPos.offsetBy offset
  mkAtomFrom (.ofRange ⟨beg, fin⟩) pattern

/-- Return if `line` looks like a correct authors line in a copyright header.

The `offset` input is used to shift the position information of the `Syntax` that the command
produces.
`authorsLineChecks` computes a position for its warning *relative to `line`*.
The `offset` input passes on the starting position of `line` in the whole file.
-/
def authorsLineChecks (line : String) (offset : String.Pos.Raw) : Array (Syntax × String) :=
  Id.run do
  -- We cannot reasonably validate the author names, so we look only for a few common mistakes:
  -- the line starting wrongly, double spaces, using ' and ' between names,
  -- and ending the line with a period.
  let mut stxs := #[]
  if !line.startsWith "Authors: " then
    stxs := stxs.push
      (toSyntax line (line.take "Authors: ".length |>.copy) offset,
       s!"The authors line should begin with 'Authors: '")
  if (line.splitOn "  ").length != 1 then
    stxs := stxs.push (toSyntax line "  " offset, s!"Double spaces are not allowed.")
  if (line.splitOn " and ").length != 1 then
    stxs := stxs.push (toSyntax line " and " offset, s!"Please, do not use 'and'; use ',' instead.")
  if line.back == '.' then
    stxs := stxs.push
      (toSyntax line "." offset,
       s!"Please, do not end the authors' line with a period.")
  -- If there are no previous exceptions, then we try to validate the names.
  if !stxs.isEmpty then
    return stxs
  if (line.drop "Authors:".length).trimAscii.isEmpty then
    return #[(toSyntax line "Authors:" offset,
       s!"Please, add at least one author!")]
  else
    return #[]

/-- The main function to validate the copyright string.
The input is the copyright string, the output is an array of `Syntax × String` encoding:
* the `Syntax` factors are atoms whose ranges are "best guesses" for where the changes should
  take place; the embedded string is the current text that the linter flagged;
* the `String` factor is the linter message.

The linter checks that
* the first and last line of the copyright are a `("/-", "-/")` pair, each on its own line;
* the first line is begins with `Copyright (c) 20` and ends with `. All rights reserved.`;
* the second line is `Released under Apache 2.0 license as described in the file LICENSE.`;
* the remainder of the string begins with `Authors: `, does not end with `.` and
  contains no ` and ` nor a double space, except possibly after a line break.
-/
public def copyrightHeaderChecks (copyright : String) : Array (Syntax × String) := Id.run do
  -- First, we merge lines ending in `,`: two spaces after the line-break are ok,
  -- but so is only one or none.  We take care of *not* adding more consecutive spaces, though.
  -- This is to allow the copyright or authors' lines to span several lines.
  -- We also allow the "All rights reserved" line to be on a separate line.
  let preprocessCopyright := (copyright.replace ",\n  " ", ").replace ",\n" ","
    |>.replace ".\nAll rights reserved." ". All rights reserved."
  -- Filter out everything after the first isolated `-/`.
  let pieces := preprocessCopyright.splitOn "\n-/"
  let copyright := (pieces.getD 0 "") ++ "\n-/"
  let stdText (s : String) :=
    s!"Malformed or missing copyright header: `{s}` should be alone on its own line."
  let mut output := #[]
  if (pieces.getD 1 "\n").take 1 != "\n".toSlice then
    output := output.push (toSyntax copyright "-/", s!"{stdText "-/"}")
  let lines := copyright.splitOn "\n"
  let closeComment := lines.getLastD ""
  match lines with
  | openComment :: copyrightAuthor :: license :: authorsLines =>
    -- The header should start and end with blank comments.
    match openComment, closeComment with
    | "/-", "-/" => output := output
    | "/-", _    =>
      output := output.push (toSyntax copyright closeComment, s!"{stdText "-/"}")
    | _, _       =>
      output := output.push (toSyntax copyright openComment, s!"{stdText ("/".push '-')}")
    -- Validate the first copyright line.
    let copStart := "Copyright (c) 20"
    let copStop := ". All rights reserved."
    if !copyrightAuthor.startsWith copStart then
      output := output.push
        (toSyntax copyright (copyrightAuthor.take copStart.length).copy,
         s!"Copyright line should start with 'Copyright (c) YYYY'")
    let author := (copyrightAuthor.drop (copStart.length + 2))
    if output.isEmpty && author.take 1 != " ".toSlice then
      output := output.push
        (toSyntax copyright (copyrightAuthor.drop (copStart.length + 2)).copy,
         s!"'Copyright (c) YYYY' should be followed by a space")
    if output.isEmpty && #["", ".", ","].contains ((author.drop 1).take 1).trimAscii.copy then
      output := output.push
        (toSyntax copyright (copyrightAuthor.drop (copStart.length + 3)).copy,
         s!"There should be at least one copyright author, separated from the year by exactly one space.")
    if !copyrightAuthor.endsWith copStop then
      output := output.push
        (toSyntax copyright (copyrightAuthor.takeEnd copStop.length).copy,
         s!"Copyright line should end with '. All rights reserved.'")
    -- Validate the authors line(s). The last line is the closing comment: trim that off right away.
    let authorsLines := authorsLines.dropLast
    -- Complain about a missing authors line.
    if authorsLines.length == 0 then
      output := output.push (toSyntax copyright "-/", s!"Copyright too short!")
    else
    -- If the list of authors spans multiple lines, all but the last line should end with a trailing
    -- comma. This excludes e.g. other comments in the copyright header.
    let authorsLine := "\n".intercalate authorsLines
    let authorsStart := (("\n".intercalate [openComment, copyrightAuthor, license, ""])).rawEndPos
    if authorsLines.length > 1 && !authorsLines.dropLast.all (·.endsWith ",") then
      output := output.push ((toSyntax copyright authorsLine),
        "If an authors line spans multiple lines, \
        each line but the last must end with a trailing comma")
    output := output.append (authorsLineChecks authorsLine authorsStart)
    let expectedLicense := "Released under Apache 2.0 license as described in the file LICENSE."
    if license != expectedLicense then
      output := output.push (toSyntax copyright license,
        s!"Second copyright line should be \"{expectedLicense}\"")
  | _ =>
    output := output.push (toSyntax copyright "-/", s!"Copyright too short!")
  return output

/--
`isInLibraryRoot modName` returns `true` if `<root>.lean` imports the file `modName`, where
`<root>` is the top-level component of `modName`. For example, for `Mathlib.Foo.Bar` this checks
`Mathlib.lean`; for `Cslib.Foo.Bar` this checks `Cslib.lean`.
This is used by the `Header` linter as a heuristic of whether it should inspect the file or not,
so that the linter works in any project whose library root follows the standard Lean convention
of being named after the top-level module.
-/
def isInLibraryRoot (modName : Name) : IO Bool := do
  let rootPath := (modName.getRoot.toString : System.FilePath).addExtension "lean"
  if ← rootPath.pathExists then
    let res ← parseImports' (← IO.FS.readFile rootPath) ""
    return res.imports.any (·.module == modName)
  else return false

/-- `inLibraryRootMutex` caches whether the current file is imported in the library root file
(e.g. `Mathlib.lean`), as computed by `isInLibraryRoot`. It is
* `none` at initialization time;
* `some true` if the `header` linter has already discovered that the current file
  is imported in the library root file;
* `some false` if the `header` linter has already discovered that the current file
  is *not* imported in the library root file.
-/
initialize inLibraryRootMutex : Std.Mutex (Option Bool) ← Std.Mutex.new none

/--
The "header" style linter checks that a file starts with
```
/-
Copyright ...
Apache ...
Authors ...
-/

import statements*
module doc-string*
remaining file
```
It emits a warning if
* the copyright statement is malformed;
* `Mathlib.Tactic` is imported;
* any import in `Lake` is present;
* the first non-`import` command is not a module doc-string.

The linter allows `import`-only files and does not require a copyright statement in `Mathlib.Init`.
-/
public register_option linter.style.header : Bool := {
  defValue := false
  descr := "enable the header style linter"
}

/-- Extends `Import` with ``stx : TSyntax `Lean.Parser.Module.import`` to allow reporting at the
given import. -/
structure ImportRef extends Import where
  stx : TSyntax ``Parser.Module.import

/-- Returns the module `Ident` (following `(public)? (meta)? import (all)?` of a given
`ImportRef`. -/
def ImportRef.getIdent (i : ImportRef) : Ident :=
  match i.stx with
  | `(Parser.Module.import|
      $[public]? $[meta]? import $[all]? $n:ident) => n
  | _ => ⟨.missing⟩

/-- Destructures header syntax (`(module)? (prelude)? $imports*`) into an array of `Import`s
together with the import syntax that gave rise to them. See also `headerToImports`. -/
def headerToImportRefs (header : TSyntax ``Parser.Module.header) : Array ImportRef :=
  match header with
  | `(Parser.Module.header| $[module%$moduleTk]? $[prelude]? $imports*) =>
    imports.filterMap fun
      | stx@`(Parser.Module.import|
          $[public%$publicTk]? $[meta%$metaTk]? import $[all%$allTk]? $n:ident) =>
        some {
          module := n.getId
          importAll := allTk.isSome
          isExported := publicTk.isSome || moduleTk.isNone
          isMeta := metaTk.isSome
          stx := ⟨stx⟩ }
      | _ => none
  | _ => #[]

namespace Style.header

/-- Check the `Syntax` `imports` for broad imports:
`Mathlib.Tactic`, any import starting with `Lake`, or `Mathlib.Tactic.{Have,Replace}`. -/
def broadImportsCheck (imports : Array ImportRef) (mainModule : Name) : CommandElabM Unit := do
  for i in imports do
    match i.module with
    | `Mathlib.Tactic | `Lean | `Lean.Elab | `Std =>
      Linter.logLint linter.style.header i.getIdent
        s!"Files in mathlib cannot import the whole `{i.module}` folder. \
        Doing so would cause imports to be unnecessarily slow."
    | `Mathlib.Tactic.Replace =>
      if mainModule != `Mathlib.Tactic then
        Linter.logLint linter.style.header i.getIdent
          "`Mathlib.Tactic.Replace` defines a deprecated form of the `replace` tactic; \
          please do not use it in mathlib."
    | `Mathlib.Tactic.Have =>
      if ![`Mathlib.Tactic, `Mathlib.Tactic.Replace].contains mainModule then
        Linter.logLint linter.style.header i.getIdent
          "`Mathlib.Tactic.Have` defines a deprecated form of the `have` tactic; \
          please do not use it in mathlib."
    | modName =>
      if modName.getRoot == `Lake then
      Linter.logLint linter.style.header i.getIdent
        "In the past, importing `Lake` in mathlib has led to dramatic slow-downs of the linter \
        (see e.g. https://github.com/leanprover-community/mathlib4/pull/13779). \
        Please consider carefully if this import is useful and \
        make sure to benchmark it. If this is fine, feel free to silence this linter."

/-- Check the syntax `imports` for syntactically duplicate imports.
Two imports are considered duplicates only if they import the same module with the same modifiers.
For example, `public import Foo` and `import all Foo` are NOT duplicates.
-/
def duplicateImportsCheck (imports : Array ImportRef) : CommandElabM Unit := do
  let mut importsSoFar : Std.HashSet Import := {}
  for imp in imports do
    if importsSoFar.contains imp.toImport then
      Linter.logLint linter.style.header imp.getIdent
        m!"Duplicate imports: `{imp.module}` already imported"
    else
      importsSoFar := importsSoFar.insert imp.toImport

/--
The set of files outside the `Mathlib` package to run the header style linter on,
because they are files that test the linter.
-/
def headerTestFiles : NameSet := .ofList [
  `MathlibTest.Header,
  `MathlibTest.HeaderFail,
  `MathlibTest.VersoHeader,
  `MathlibTest.DirectoryDependencyLinter.Test]

@[inherit_doc Mathlib.Linter.linter.style.header]
def headerLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.style.header (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let map ← getFileMap
  let s := ParseImports.main map.source (ParseImports.whitespace map.source {})
  unless (← read).cmdPos == s.pos do
    return
  let mainModule ← getMainModule
  if Parser.isTerminalCommand stx ||
    -- Deprecated module files are exempt from all header style checks (copyright, doc-string,
    -- directory dependency, etc.) since they are just import-redirect stubs.
    stx.isOfKind ``Parser.Command.deprecated_module ||
    -- Skip linting the library root file itself.
    -- In practice, the `inLibraryRoot?` check above already covers this (a well-formed
    -- `<root>.lean` does not import itself), but a root module could appear in `headerTestFiles`.
    mainModule == mainModule.getRoot
  then return
  unless stx.isOfKind ``Parser.Command.moduleDoc do
    Linter.logLint linter.style.header stx
      m!"The module doc-string for a file should be the first command after the imports.\n\
       Please, add a module doc-string (`/-! ... -/`) before `{stx}`."
  let inLibraryRoot? ← inLibraryRootMutex.atomically do
    match ← get with
    | some d => return d
    | none =>
      let val ← isInLibraryRoot mainModule
      -- We cache the answer to avoid recomputing it on every command. The fill runs under the mutex
      -- so that concurrent (async) linter runs don't all miss the cache and each redundantly parse
      -- the library root file; `mainModule` is fixed for the duration of the elaboration.
      set (some val)
      return val
  -- The linter skips files not imported in their library root (e.g. `Mathlib.lean`), to avoid
  -- linting "scratch files". It is however active in the test files for the linter itself.
  unless inLibraryRoot? || headerTestFiles.contains mainModule do return
  -- Re-parse the header slowly, to get the leading whitespace and nice source locations for imports
  let (headerStx, s, log) ← Parser.parseHeader (Parser.mkInputContext map.source (← getFileName))
  if log.hasErrors then return
  let importRefs := headerToImportRefs headerStx
  -- Report on broad or duplicate imports.
  broadImportsCheck importRefs mainModule
  duplicateImportsCheck importRefs
  let errors ← directoryDependencyCheck mainModule
  if errors.size > 0 then
    Linter.logLint linter.directoryDependency (importRefs.back?.elim stx (·.stx)) <|
      m!"\n\n".joinSep errors.toList
  -- Report any errors about the copyright line.
  if mainModule != `Mathlib.Init && mainModule != `Mathlib.Tactic then
    let copyright := match headerStx.raw.getHeadInfo with
      | .original lead .. => lead.toString
      | _ => ""
    for (stx, m) in copyrightHeaderChecks copyright do
      Linter.logLint linter.style.header stx m!"* `{stx.getAtomVal}`:\n{m}\n"

initialize addLinter headerLinter

end Style.header

end Mathlib.Linter
