/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Damiano Testa
-/
import Lean.Elab.Command
import Lean.Elab.ParseImportsFast
import Mathlib.Tactic.Linter.DirectoryDependency

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
The strategy used by the linter is as follows.
The linter computes the end position of the first module doc-string of the file,
resorting to the end of the file, if there is no module doc-string.
Next, the linter tries to parse the file up to the position determined above.

If the parsing is successful, the linter checks the resulting `Syntax` and behaves accordingly.

If the parsing is not successful, this already means there is some "problematic" command
after the imports. In particular, there is a command that is not a module doc-string
immediately following the last import: the file should be flagged by the linter.
Hence, the linter then falls back to parsing the header of the file, adding a spurious `section`
after it.
This makes it possible for the linter to check the entire header of the file, emit warnings that
could arise from this part and also flag that the file should contain a module doc-string after
the `import` statements.
-/

open Lean Elab Command Linter

namespace Mathlib.Linter

/--
`firstNonImport? stx` assumes that the input `Syntax` is of kind `Lean.Parser.Module.module`.
It returns
* `none`, if `stx` consists only of `import` statements,
* the first non-`import` command in `stx`, otherwise.

The intended use-case is to use the output of `testParseModule` as the input of
`firstNonImport?`.
-/
def firstNonImport? : Syntax → Option Syntax
  | .node _ ``Lean.Parser.Module.module #[_header, .node _ `null args] => args[0]?
  | _=> some .missing  -- this is unreachable, if the input comes from `testParseModule`

/-- `getImportIds s` takes as input `s : Syntax`.
It returns the array of all `import` identifiers in `s`. -/
-- We cannot use `importsOf` instead, as
-- - that function is defined in the `ImportGraph` project; we would like to minimise imports
--   to Mathlib.Init (where this linter is imported)
-- - that function does not return the Syntax corresponding to each import,
--   which we use to log more precise warnings.
partial
def getImportIds (s : Syntax) : Array Syntax :=
  let rest : Array Syntax := (s.getArgs.map getImportIds).flatten
  if let `(Lean.Parser.Module.import| import $n) := s then
    rest.push n
  else
    rest

/--
`parseUpToHere pos post` takes as input `pos : String.Pos` and the optional `post : String`.
It parses the current file from the beginning until `pos`, appending `post` at the end.
It returns a syntax node of kind `Lean.Parser.Module.module`.
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
def parseUpToHere (pos : String.Pos.Raw) (post : String := "") : CommandElabM Syntax := do
  let upToHere : Substring := { str := (← getFileMap).source, startPos := ⟨0⟩, stopPos := pos }
  -- Append a further string after the content of `upToHere`.
  Parser.testParseModule (← getEnv) "linter.style.header" (upToHere.toString ++ post)

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
      (toSyntax line (line.take "Authors: ".length) offset,
       s!"The authors line should begin with 'Authors: '")
  if (line.splitOn "  ").length != 1 then
    stxs := stxs.push (toSyntax line "  " offset, s!"Double spaces are not allowed.")
  if (line.splitOn " and ").length != 1 then
    stxs := stxs.push (toSyntax line " and " offset, s!"Please, do not use 'and'; use ',' instead.")
  if line.back == '.' then
    stxs := stxs.push
      (toSyntax line "." offset,
       s!"Please, do not end the authors' line with a period.")
  return stxs

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
def copyrightHeaderChecks (copyright : String) : Array (Syntax × String) := Id.run do
  -- First, we merge lines ending in `,`: two spaces after the line-break are ok,
  -- but so is only one or none.  We take care of *not* adding more consecutive spaces, though.
  -- This is to allow the copyright or authors' lines to span several lines.
  let preprocessCopyright := (copyright.replace ",\n  " ", ").replace ",\n" ","
  -- Filter out everything after the first isolated `-/`.
  let pieces := preprocessCopyright.splitOn "\n-/"
  let copyright := (pieces.getD 0 "") ++ "\n-/"
  let stdText (s : String) :=
    s!"Malformed or missing copyright header: `{s}` should be alone on its own line."
  let mut output := #[]
  if (pieces.getD 1 "\n").take 1 != "\n" then
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
        (toSyntax copyright (copyrightAuthor.take copStart.length),
         s!"Copyright line should start with 'Copyright (c) YYYY'")
    if !copyrightAuthor.endsWith copStop then
      output := output.push
        (toSyntax copyright (copyrightAuthor.takeRight copStop.length),
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
`isInMathlib modName` returns `true` if `Mathlib.lean` imports the file `modName` and `false`
otherwise.
This is used by the `Header` linter as a heuristic of whether it should inspect the file or not.
-/
def isInMathlib (modName : Name) : IO Bool := do
  let mlPath := ("Mathlib" : System.FilePath).addExtension "lean"
  if ← mlPath.pathExists then
    let res ← parseImports' (← IO.FS.readFile mlPath) ""
    return (res.imports.map (·.module == modName)).any (·)
  else return false

/-- `inMathlibRef` is
* `none` at initialization time;
* `some true` if the `header` linter has already discovered that the current file
  is imported in `Mathlib.lean`;
* `some false` if the `header` linter has already discovered that the current file
  is *not* imported in `Mathlib.lean`.
-/
initialize inMathlibRef : IO.Ref (Option Bool) ← IO.mkRef none

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
register_option linter.style.header : Bool := {
  defValue := false
  descr := "enable the header style linter"
}

namespace Style.header

/-- Check the `Syntax` `imports` for broad imports:
`Mathlib.Tactic`, any import starting with `Lake`, or `Mathlib.Tactic.{Have,Replace}`. -/
def broadImportsCheck (imports : Array Syntax) (mainModule : Name) : CommandElabM Unit := do
  for i in imports do
    match i.getId with
    | `Mathlib.Tactic =>
      Linter.logLint linter.style.header i "Files in mathlib cannot import the whole tactic folder."
    | `Mathlib.Tactic.Replace =>
      if mainModule != `Mathlib.Tactic then
        Linter.logLint linter.style.header i
          "'Mathlib.Tactic.Replace' defines a deprecated form of the 'replace' tactic; \
          please do not use it in mathlib."
    | `Mathlib.Tactic.Have =>
      if ![`Mathlib.Tactic, `Mathlib.Tactic.Replace].contains mainModule then
        Linter.logLint linter.style.header i
          "'Mathlib.Tactic.Have' defines a deprecated form of the 'have' tactic; \
          please do not use it in mathlib."
    | modName =>
      if modName.getRoot == `Lake then
      Linter.logLint linter.style.header i
        "In the past, importing 'Lake' in mathlib has led to dramatic slow-downs of the linter \
        (see e.g. https://github.com/leanprover-community/mathlib4/pull/13779). Please consider carefully if this import is useful and \
        make sure to benchmark it. If this is fine, feel free to silence this linter."

/-- Check the syntax `imports` for syntactically duplicate imports.
The output is an array of `Syntax` atoms whose ranges are the import statements,
and the embedded strings are the error message of the linter.
-/
def duplicateImportsCheck (imports : Array Syntax)  : CommandElabM Unit := do
  let mut importsSoFar := #[]
  for i in imports do
    if importsSoFar.contains i then
      Linter.logLint linter.style.header i m!"Duplicate imports: '{i}' already imported"
    else importsSoFar := importsSoFar.push i

@[inherit_doc Mathlib.Linter.linter.style.header]
def headerLinter : Linter where run := withSetOptionIn fun stx ↦ do
  let mainModule ← getMainModule
  let inMathlib? := ← match ← inMathlibRef.get with
    | some d => return d
    | none => do
      let val ← isInMathlib mainModule
      -- We store the answer to the question "is this file in `Mathlib.lean`?" in `inMathlibRef`
      -- to avoid recomputing its value on every command. This is a performance optimisation.
      inMathlibRef.set (some val)
      return val
  -- The linter skips files not imported in `Mathlib.lean`, to avoid linting "scratch files".
  -- It is however active in the test files for the linter itself.
  unless inMathlib? ||
    mainModule == `MathlibTest.Header || mainModule == `MathlibTest.DirectoryDependencyLinter.Test do return
  unless getLinterValue linter.style.header (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- `Mathlib.lean` imports `Mathlib.Tactic`, which the broad imports check below would flag.
  -- Since that file is imports-only, we can simply skip linting it.
  if mainModule == `Mathlib then return
  let fm ← getFileMap
  let md := (getMainModuleDoc (← getEnv)).toArray
  -- The end of the first module doc-string, or the end of the file if there is none.
  let firstDocModPos := match md[0]? with
                          | none     => fm.positions.back!
                          | some doc => fm.ofPosition doc.declarationRange.endPos
  unless stx.getTailPos?.getD default ≤ firstDocModPos do
    return
  -- We try to parse the file up to `firstDocModPos`.
  let upToStx ← parseUpToHere firstDocModPos <|> (do
    -- If parsing failed, there is some command which is not a module docstring.
    -- In that case, we parse until the end of the imports and add an extra `section` afterwards,
    -- so we trigger a "no module doc-string" warning.
    let fil ← getFileName
    let (stx, _) ← Parser.parseHeader { inputString := fm.source, fileName := fil, fileMap := fm }
    parseUpToHere (stx.raw.getTailPos?.getD default) "\nsection")
  let importIds := getImportIds upToStx
  -- Report on broad or duplicate imports.
  broadImportsCheck importIds mainModule
  duplicateImportsCheck importIds
  let errors ← directoryDependencyCheck mainModule
  if errors.size > 0 then
    let mut msgs := ""
    for msg in errors do
      msgs := msgs ++ "\n\n" ++ (← msg.toString)
    Linter.logLint linter.directoryDependency stx msgs.trimLeft
  let afterImports := firstNonImport? upToStx
  if afterImports.isNone then return
  let copyright := match upToStx.getHeadInfo with
    | .original lead .. => lead.toString
    | _ => ""
  -- Report any errors about the copyright line.
  if mainModule != `Mathlib.Init then
    for (stx, m) in copyrightHeaderChecks copyright do
      Linter.logLint linter.style.header stx m!"* '{stx.getAtomVal}':\n{m}\n"
  -- Report a missing module doc-string.
  match afterImports with
    | none => return
    | some (.node _ ``Lean.Parser.Command.moduleDoc _) => return
    | some rest =>
    Linter.logLint linter.style.header rest
      m!"The module doc-string for a file should be the first command after the imports.\n\
       Please, add a module doc-string before `{stx}`."

initialize addLinter headerLinter

end Style.header

end Mathlib.Linter
