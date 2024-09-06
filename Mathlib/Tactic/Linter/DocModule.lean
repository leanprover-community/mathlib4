/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Linter.Util
import Batteries.Data.String.Matcher
import Mathlib.Util.AssertExists

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
def onlyImportsModDocs : Syntax → Bool
  | .node _ ``Lean.Parser.Module.module #[_header, .node _ `null args] =>
    let args := args.toList.dropWhile (·.isOfKind ``Lean.Parser.Command.section)
    let first := args.getD 0 (Lean.mkNode ``Lean.Parser.Command.moduleDoc #[])
    first.isOfKind ``Lean.Parser.Command.moduleDoc
  | _=> false

/-- `afterImports stx` checks whether `stx` is the syntax for a module, discards the
`import` statements and returns the first command after the `import`s, or `.missing` if
no such command exists.
-/
def afterImports : Syntax → Syntax
  | .node _ ``Lean.Parser.Module.module #[_header, .node _ `null args] =>
    args.getD 0 default
  | _=> .missing

/-- returns the array of `import` identifiers. -/
partial
def getImportIds (s : Syntax) : Array Syntax :=
  let rest : Array Syntax := (s.getArgs.map getImportIds).flatten
  if s.isOfKind ``Lean.Parser.Module.import then
    rest.push (s.getArgs.getD 2 default)
  else
    rest

/-- `parseUpToHere stx post` takes as input a `Syntax` `stx` and a `String` `post`.
It parses the file containing `stx` up to and excluding `stx`, appending `post` at the end.

The option of appending a final string to the text gives more control to avoid syntax errors,
for instance in the presence of `#guard_msgs in` or `set_option ... in`.
-/
def parseUpToHere (stx : Syntax) (post : String := "") (included : Bool := true) :
    CommandElabM Syntax := do
  let fm ← getFileMap
  let startPos := if included then stx.getTailPos?.getD default else stx.getPos?.getD default
  let upToHere : Substring:= { str := fm.source, startPos := ⟨0⟩, stopPos := startPos}
  -- append a further string after the `upToHere` content
  Parser.testParseModule (← getEnv) "linter.style.header" (upToHere.toString ++ post)

-- from the textbased
/-- Return if `line` looks like a correct authors line in a copyright header. -/
def isCorrectAuthorsLine (line : String) : Bool :=
  -- We cannot reasonably validate the author names, so we look only for a few common mistakes:
  -- the file starting wrong, double spaces, using ' and ' between names,
  -- and ending the line with a period.
  line.startsWith "Authors: " && (!line.containsSubstr "  ")
    && (!line.containsSubstr " and ") && (!line.endsWith ".")

/-- `toSyntax s pattern` converts the two input strings into a `Syntax`, assuming that `pattern`
is a substring of `s`:
the syntax is an atom with value `pattern` whose the range is the range of `pattern` in `s`. -/
def toSyntax (s pattern : String) : Syntax :=
  let substr := (s.findSubstr? pattern.toSubstring).getD default
  mkAtomFrom (.ofRange ⟨substr.startPos, substr.stopPos⟩) pattern

/-- The main function to validate the copyright string. -/
def copyrightHeaderLinter (copyright : String) : Array (Syntax × MessageData) := Id.run do
  -- filter out everything after the first isolated `-/`
  let pieces := copyright.splitOn "\n-/"
  let copyright := (pieces.getD 0 "") ++ "\n-/"
  let stdTxt (s : String) :=
    s!"Malformed or missing copyright header: `{s}` should be alone on its own line."
  let mut msgs := #[]
  if (pieces.getD 1 "\n").take 1 != "\n" then
    msgs := msgs.push (toSyntax copyright "-/", m!"{stdTxt "-/"}")
  let lines := copyright.splitOn "\n" --.trimRight
  --dbg_trace lines
  let closeComment := lines.getLastD ""
  match lines with
  | openComment :: copyrightAuthor :: license :: authorsLines =>
    -- The header should start and end with blank comments.
    match openComment, closeComment with
    | "/-", "-/" => msgs := msgs
    | "/-", _    =>
      msgs := msgs.push (toSyntax copyright closeComment, m!"{stdTxt "-/"}")
    | _, _       =>
      msgs := msgs.push (toSyntax copyright openComment, m!"{stdTxt ("/".push '-')}")
    -- validate copyright author
    if !copyrightAuthor.startsWith "Copyright (c) 20" then
      msgs := msgs.push
        (toSyntax copyright (copyrightAuthor.take 14), m!"First copyright line is malformed")
    if !copyrightAuthor.endsWith ". All rights reserved." then
      msgs := msgs.push
        (toSyntax copyright (copyrightAuthor.takeRight 20), m!"First copyright line is malformed")
    -- validate authors
    let authorsLine := "\n".intercalate authorsLines.dropLast
    dbg_trace authorsLine
    if !isCorrectAuthorsLine authorsLine then
      msgs := msgs.push (toSyntax copyright authorsLine,
          "Authors line should look like: 'Authors: Jean Dupont, Иван Иванович Иванов'")
    -- validate license
    let expectedLicense := "Released under Apache 2.0 license as described in the file LICENSE."
    if license != expectedLicense then
      msgs := msgs.push (toSyntax copyright license,
        m!"Second copyright line should be \"{expectedLicense}\"")
  | _ =>
    msgs := msgs.push (toSyntax copyright "-/", m!"Copyright too short!")
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
  defValue := true
  descr := "enable the header style linter"
}

/-- An `IO.Ref` used to keep track of the starting position of the first non-`import`
command in a file -/
initialize firstCommand : IO.Ref (Option String.Pos) ← IO.mkRef none

namespace Style.AssertNotExists

@[inherit_doc Mathlib.Linter.linter.style.header]
def headerLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.header (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let mut firstPos ← firstCommand.get
  let mut upToStx : Syntax := .missing
  let offset : String.Pos := ⟨3⟩
  if firstPos.isNone then
    upToStx ← parseUpToHere stx <|> pure Syntax.missing
    let endOfImports := upToStx.getTailPos?
    firstCommand.set endOfImports
  if upToStx != .missing then
    firstPos := upToStx.getTailPos?
    unless stx.getPos?.getD 0 ≤ firstPos.getD 0 + offset do
      return
    let copyright := match upToStx.getHeadInfo with
      | .original lead .. => lead.toString
      | _ => default
    for (stx, m) in copyrightHeaderLinter copyright do
      Linter.logLint linter.style.header stx m!"* '{stx.getAtomVal}':\n{m}\n"
    let imports := getImportIds upToStx
    for i in imports do
      match i.getId with
      | `Mathlib.Data.Nat.Notation =>
        Linter.logLint linter.style.header i
          m!"Files in mathlib cannot import the whole tactic folder."
      | `Mathlib.Tactic =>
        Linter.logLint linter.style.header i
          m!"Files in mathlib cannot import the whole tactic folder."
      | modName =>
        if modName.getRoot == `Lake then
        Linter.logLint linter.style.header i
          m!"In the past, importing 'Lake' in mathlib has led to dramatic slow-downs of the linter \
            (see e.g. mathlib4#13779). Please consider carefully if this import is useful and \
            make sure to benchmark it. If this is fine, feel free to allow this linter."
    if ! onlyImportsModDocs upToStx then
      Linter.logLint linter.style.header stx
        m!"`{stx}` appears too late: it can only be preceded by `import` statements \
        doc-module strings and other `assert_not_exists` statements."
    else return


initialize addLinter headerLinter

end Style.AssertNotExists

end Mathlib.Linter
