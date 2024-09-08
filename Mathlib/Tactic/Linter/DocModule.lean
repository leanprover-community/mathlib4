/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command

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

/-- `onlyImportsModDocs stx` checks whether `stx` is the syntax for a module that
only consists of any number of `import` statements (possibly none) followed by
either a module doc-string (and then anything else) or nothing else.
-/
def onlyImportsModDocs : Syntax → Option Bool
  | .node _ ``Lean.Parser.Module.module #[_header, .node _ `null args] =>
    let args := args
    let first := args.get? 0
    first.map (·.isOfKind ``Lean.Parser.Command.moduleDoc)
  | _=> some false

/-- Returns the array of all `import` identifiers in `s`. -/
partial
def getImportIds (s : Syntax) : Array Syntax :=
  let rest : Array Syntax := (s.getArgs.map getImportIds).flatten
  if s.isOfKind ``Lean.Parser.Module.import then
    rest.push (s.getArgs.getD 2 default)
  else
    rest

/--
`parseUpToHere stx post` takes as input a `Syntax` `stx` and a `String` `post`.
It parses the file containing `stx` up to and excluding `stx`, appending `post` at the end.

The option of appending a final string to the text gives more control to avoid syntax errors,
for instance in the presence of `#guard_msgs in` or `set_option ... in`.

Note that this parsing will *not* be successful on every file.  However, if the linter is
parsing the file linearly, it will only need to parse
* the imports (that are always parseable) and
* the first non-import command that is supposed to be a module doc-string (so again always
  parseable).

In conclusion, either the parsing is successful, and the linter can continue with its analysis,
or the parsing is not successful and the linter will flag a missing module doc-string!
-/
def parseUpToHere (stx : Syntax) (post : String := "") (included : Bool := true) :
    CommandElabM Syntax := do
  let fm ← getFileMap
  let startPos := if included then stx.getTailPos?.getD default else stx.getPos?.getD default
  let upToHere : Substring:= { str := fm.source, startPos := ⟨0⟩, stopPos := startPos}
  -- append a further string after the `upToHere` content
  Parser.testParseModule (← getEnv) "linter.style.header" (upToHere.toString ++ post)

/-- `toSyntax s pattern` converts the two input strings into a `Syntax`, assuming that `pattern`
is a substring of `s`:
the syntax is an atom with value `pattern` whose the range is the range of `pattern` in `s`. -/
def toSyntax (s pattern : String) (offset : String.Pos := 0) : Syntax :=
  --let firstSubstring := ((s.splitOn pattern).getD (1 + offset) "").toSubstring
  let beg := ((s.splitOn pattern).getD 0 "").endPos + offset
  let fin := (((s.splitOn pattern).getD 0 "") ++ pattern).endPos + offset
  mkAtomFrom (.ofRange ⟨beg, fin⟩) pattern

-- adapted from the textbased
/-- Return if `line` looks like a correct authors line in a copyright header. -/
def authorsLineCorrections (line : String) (offset : String.Pos) : Array (Syntax × String) :=
  Id.run do
  -- We cannot reasonably validate the author names, so we look only for a few common mistakes:
  -- the file starting wrong, double spaces, using ' and ' between names,
  -- and ending the line with a period.
  let mut stxs := #[]
  if !line.startsWith "Authors: " then
    stxs := stxs.push
      (toSyntax line (line.take "Authors: ".length) offset,
       s!"The authors line should begin with 'Authors: '")
  if ((line.replace "\n  " " ").splitOn "  ").length != 1 then
    stxs := stxs.push (toSyntax line "  " offset, s!"Double spaces are not allowed.")
  if (line.splitOn " and ").length != 1 then
    stxs := stxs.push (toSyntax line " and " offset, s!"Please, do not use 'and', use ',' instead.")
  if line.endsWith "." then
    stxs := stxs.push
      (toSyntax line "." offset,
       s!"Please, do not end the authors' line with a period.")
  return stxs

/-- The main function to validate the copyright string.
The input is the copyright string, the output is an array of `Syntax × String` encoding:
* the `Syntax` factors are atoms whose ranges are "best guesses" for where the changes should
  take place and the embedded string is the current text that the linter flagged;
* the `String` factor is the linter message.

The linter checks that
* the first and last line of the copyright are a `("/-", "-/")` pair, each on its own line;
* the first line is `begins with `Copyright (c) 20` and ends with `. All rights reserved.`;
* the second line is `Released under Apache 2.0 license as described in the file LICENSE.`;
* the remainder of the string begins with `Authors: `, does not end with `.` and
  contains no ` and ` nor a double space, except possibly after a line break.
-/
def copyrightHeaderLinter (copyright : String) : Array (Syntax × String) := Id.run do
  -- filter out everything after the first isolated `-/`
  let pieces := copyright.splitOn "\n-/"
  let copyright := (pieces.getD 0 "") ++ "\n-/"
  let stdTxt (s : String) :=
    s!"Malformed or missing copyright header: `{s}` should be alone on its own line."
  let mut msgs := #[]
  if (pieces.getD 1 "\n").take 1 != "\n" then
    msgs := msgs.push (toSyntax copyright "-/", s!"{stdTxt "-/"}")
  let lines := copyright.splitOn "\n"
  let closeComment := lines.getLastD ""
  match lines with
  | openComment :: copyrightAuthor :: license :: authorsLines =>
    -- The header should start and end with blank comments.
    match openComment, closeComment with
    | "/-", "-/" => msgs := msgs
    | "/-", _    =>
      msgs := msgs.push (toSyntax copyright closeComment, s!"{stdTxt "-/"}")
    | _, _       =>
      msgs := msgs.push (toSyntax copyright openComment, s!"{stdTxt ("/".push '-')}")
    -- validate copyright author
    let copStart := "Copyright (c) 20"
    let copStop := ". All rights reserved."
    if !copyrightAuthor.startsWith copStart then
      msgs := msgs.push
        (toSyntax copyright (copyrightAuthor.take copStart.length),
         s!"Copyright line should start with 'Copyright (c) YYYY'")
    if !copyrightAuthor.endsWith copStop then
      msgs := msgs.push
        (toSyntax copyright (copyrightAuthor.takeRight copStop.length),
         s!"Copyright line should end with '. All rights reserved.'")
    -- validate authors
    let authorsLine := "\n".intercalate authorsLines.dropLast
    let authorsStart := (("\n".intercalate [openComment, copyrightAuthor, license, ""])).endPos
    for corr in authorsLineCorrections authorsLine authorsStart do
      msgs := msgs.push corr
    let expectedLicense := "Released under Apache 2.0 license as described in the file LICENSE."
    if license != expectedLicense then
      msgs := msgs.push (toSyntax copyright license,
        s!"Second copyright line should be \"{expectedLicense}\"")
  | _ =>
    msgs := msgs.push (toSyntax copyright "-/", s!"Copyright too short!")
  return msgs

/-- checks the `Syntax` `imps` for broad imports. -/
def broadImportsCheck (imports : Array Syntax)  : Array (Syntax × String) := Id.run do
  let mut msgs := #[]
  for i in imports do
    match i.getId with
    | `Mathlib.Tactic | `Mathlib.Tactic.Linter.DocModule =>
      msgs := msgs.push (i, s!"Files in mathlib cannot import the whole tactic folder.")
    | modName =>
      if modName.getRoot == `Lake then
      msgs := msgs.push (i,
        s!"In the past, importing 'Lake' in mathlib has led to dramatic slow-downs of the linter \
          (see e.g. mathlib4#13779). Please consider carefully if this import is useful and \
          make sure to benchmark it. If this is fine, feel free to allow this linter.")
  return msgs

/--
The "header" style linter checks that a file starts with
```
import*
/-! doc-module -/*
```
It emits a warning if the first command after the last import is not a module doc-string.
-/
register_option linter.style.header : Bool := {
  defValue := false
  descr := "enable the header style linter"
}

/-- An `IO.Ref` used to keep track of the initial segment of the file, from the end of the last
`import` command, until the first non-`import` command. -/
initialize fileToFirstCommand : IO.Ref Substring ← IO.mkRef default

namespace Style.header

@[inherit_doc Mathlib.Linter.linter.style.header]
def headerLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.header (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- instead of silencing this linter on Sensitivity, we should probably silence the text-based one
  if #[`Archive.Sensitivity, `Mathlib.Init].contains (← getMainModule) then
    return
  let mut fileStart ← fileToFirstCommand.get
  let mut upToStx : Syntax := .missing
  let mut importIds : Array Syntax := #[]
  let offset : String.Pos := ⟨3⟩
  let fm ← getFileMap
  if Parser.isTerminalCommand stx then
    let currStart : Substring :=
      {str := fm.source, startPos := fileStart.startPos, stopPos := fileStart.stopPos}
    if fileStart != currStart then
      logWarningAt (.ofRange ⟨fileStart.startPos + ⟨1⟩, fileStart.stopPos⟩)
        m!"Header information is outdated, please restart the file to get up to date information."
  let stxRg := stx.getRange?.getD default
  if fileStart.isEmpty ||
    stx.getPos?.getD 0 ≤ fileStart.stopPos - (stxRg.stop - stxRg.start) + offset then
    upToStx ← parseUpToHere stx <|> pure Syntax.missing
    importIds := getImportIds upToStx
    fileStart := { str      := fm.source
                   startPos := importIds.back.getTailPos?.getD 0
                   stopPos  := stx.getTailPos?.getD 0 }
    fileToFirstCommand.set fileStart
  if upToStx != .missing then
    if (onlyImportsModDocs upToStx).isNone then return
    unless stx.getPos?.getD 0 ≤ fileStart.stopPos - (stxRg.stop - stxRg.start) + offset do
      return
    let copyright := match upToStx.getHeadInfo with
      | .original lead .. => lead.toString
      | _ => ""
    -- copyright report
    for (stx, m) in copyrightHeaderLinter copyright do
      Linter.logLint linter.style.header stx m!"* '{stx.getAtomVal}':\n{m}\n"
    -- imports report
    for (imp, msg) in broadImportsCheck importIds do
      Linter.logLint linter.style.header imp msg
    -- doc-module report
    if let some false := onlyImportsModDocs upToStx then
      Linter.logLint linter.style.header stx
        m!"The module doc-string for a file should be the first command after the imports.\n\
         Please, add a module doc-string before `{stx}`."
    else return

initialize addLinter headerLinter

end Style.header

end Mathlib.Linter
