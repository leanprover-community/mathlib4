/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

--import Mathlib.Init
import Mathlib.Tactic.Linter.DeprecatedModule
import Std.Time.Zoned
import Lean.Meta.Tactic.TryThis
-- a comment here to test `keepTrailing

/-!
#  Create a deprecated module

This file defines the lean script for creating a deprecated module.
-/

open Lean Elab Command

namespace DeprecatedModule

/--
`getHeader fname fileContent keepTrailing` takes as input two strings and a `Bool`ean.
It uses
* `fname`, as the path of a file (which need not exist);
* `fileContent`, as the content of `fname` (regardless of whether the file exists and what its
  content is);
* `keepTrailing` a boolean to control whether to keep trailing comments.

It returns the content of `fileContent` up to the final import,
including trailing comments if `keepTrailing = true`
(the command always trims trailing whitespace after the last comment).
-/
def getHeader (fname fileContent : String) (keepTrailing : Bool) : IO String := do
  let (stx, _) ← Parser.parseHeader (Parser.mkInputContext fileContent fname)
  let stx := if keepTrailing then stx.raw else stx.raw.unsetTrailing
  let some substring := stx.getSubstring? | throw <| .userError "No substring: we have a problem!"
  let upToAllImports : Substring := {substring with startPos := 0}
  return upToAllImports.toString

/--
`getHeaderFromFileName fname keepTrailing` is similar to `getHeader`, except that it assumes that
`fname` is the actual path of a file, and uses `fname`'s content as input to `getHeader`.
-/
def getHeaderFromFileName (fname : String) (keepTrailing : Bool) : IO String := do
  getHeader fname (← IO.FS.readFile fname) keepTrailing


/--
`mkDeprecationWithDate customMessage date` returns the formatted syntax
`deprecated_module "customMessage" (since := "date")`,
where the date is of the form "YYYY-MM-DD".
-/
def mkDeprecationWithDate (customMessage : String := "Auto-generated deprecation") (date : String) :
    CommandElabM Format := do
  let msgStx := if customMessage.isEmpty then none else some <| Syntax.mkStrLit customMessage
  let dateStx := Syntax.mkStrLit date
  let stx ← `(command|deprecated_module $[$msgStx]? (since := $dateStx))
  liftCoreM <| PrettyPrinter.ppCategory `command stx

/--
`mkDeprecation customMessage` returns the formatted syntax
`deprecated_module "customMessage" (since := "YYYY-MM-DD")`, where the date is today's date.
-/
def mkDeprecation (customMessage : String := "Auto-generated deprecation") :
    CommandElabM Format := do
  -- Get the current date in UTC: we don't want this to depend on the user computer's time zone.
  let date := s!"{(← Std.Time.DateTime.now (tz := .UTC)).toPlainDate}"
  mkDeprecationWithDate customMessage date

/--
The command `#create_deprecated_module filePath (comment)? (write)?` generates a module deprecation.

Writing
```lean
#create_deprecated_module path/To/DeletedFile.lean "This file is no longer relevant"
```
checks that `path/To/DeletedFile.lean` is not currently present, but was present in `Mathlib/`
at some point.

If the check is successful, then it reports on its findings, shows how the corresponding
deprecated module should look like, using `"This file is no longer relevant"` as the (optional)
comment.

If the message is not explicitly used, `#create_deprecated_module` defaults to
`"Auto-generated deprecation"`.
If you wish there to be no comment, use `#create_deprecated_module path/To/DeletedFile.lean ""`.

Finally, if everything looks correct, adding a final `write` actually generates the file:
```lean
#create_deprecated_module path/To/DeletedFile.lean "This file is no longer relevant" write
```
-/
syntax "#create_deprecated_module " str (ppSpace str)? (&" write")? ppLine :
  command

/-- `processPrettyOneLine log msg` takes as input two strings `log` and `msg`.
It expects `log` to be a line in the output of `git log --pretty=oneline`:
it should look like `<hash> <PRdescr>`.

It also expects `msg` to be either `last modified` or `deleted` and
it returns the pair `(<hash>, <msg> in <PRdescr> <hash>)`, formatted as a collapsible message.
-/
def processPrettyOneLine (log msg : String) : String × MessageData :=
  let hash := log.takeWhile (!·.isWhitespace)
  let PRdescr := (log.drop hash.length).trim
  (hash, m!"{msg} in " ++
        .trace {cls := .str .anonymous ("_" ++ hash.take 7)} m!"{PRdescr}" #[m!"{hash}"])

/--
`deprecateFilePath fname comment` takes as input
* the path `fname` of a file that was deleted;
* an optional comment to add in the `deprecated module` syntax.

It returns a pair consisting of
* an array of `MessageData` giving details about the last time that `fname` was modified
  and when it was deleted;
* the content of the deprecated file, matching the original `fname` up to the last import command
  followed by the `deprecated_module` command with the optional `comment` input, defaulting to
  `Auto-generated deprecation` if `comment = none`.
-/
def deprecateFilePath (fname : String) (comment : Option String) :
    CommandElabM (Array MessageData × String) := do
  let mut msgs : Array MessageData := #[]
  -- Check that the input `fname` is a file that currently does not exist.
  if ← System.FilePath.pathExists fname then
    throwError m!"The file {fname} exists: I cannot deprecate it!"
  -- Retrieve the last two commits that modified `fname`:
  -- the last one is the deletion, the previous one is the last file modification.
  let log ← IO.Process.run {
      cmd := "git"
      args := #["log", "--pretty=oneline", "--all", "-2", "--", fname]
    }
  let [deleted, lastModified] := log.trim.splitOn "\n" |
    throwError "Found {(log.trim.splitOn "\n").length} commits, but expected 2! \
      Please make sure the file {fname} actually exists"
  let (_deleteHash, deletedMsg) := processPrettyOneLine deleted "deleted"
  let (modifiedHash, modifiedMsg) := processPrettyOneLine lastModified "last modified"
  msgs := msgs.push <| m!"The file {fname} was\n"
  msgs := msgs.push modifiedMsg
  msgs := msgs.push deletedMsg

  -- Get the commit date (in YYYY-MM-DD) of the commit deleting the file.
  let log' ← IO.Process.run {cmd := "git", args := #[
    "log", "--format=%cs", "--all", "-2", "--", fname]
  }
  let deletionDate := (log'.trim.splitOn "\n")[0]!
  let deprecation ← if let some cmt := comment then mkDeprecationWithDate cmt deletionDate else mkDeprecation deletionDate
  msgs := msgs.push ""
  -- Retrieves the final version of the file, before it was deleted.
  let file ← IO.Process.run {cmd := "git", args := #["show", s!"{modifiedHash}:{fname}"]}
  -- Generate a module deprecation for the file `fname`.
  let fileHeader ← getHeader fname file false
  let deprecatedFile := s!"{fileHeader.trimRight}\n\n{deprecation.pretty.trimRight}\n"
  msgs := msgs.push <| .trace {cls := `Deprecation} m!"{fname}" #[m!"\n{deprecatedFile}"]
  return (msgs, deprecatedFile)

elab_rules : command
| `(#create_deprecated_module%$tk $fnameStx:str $[$comment:str]? $[write%$write?]?) => do
  let fname := fnameStx.getString
  if ← System.FilePath.pathExists fname then
    logWarningAt fnameStx m!"The file {fname} exists: I cannot deprecate it!"
    return
  let (msgs, deprecatedFile) ← deprecateFilePath fname (comment.map (·.getString))
  let mut msgs : Array MessageData := msgs
  if write?.isSome then
    IO.FS.writeFile fname deprecatedFile
  if write?.isNone then
    -- We strip trailing comments from `fnameStx` and `comment` to avoid them showing up in the
    -- regenerated syntax.
    let fnameStx := ⟨fnameStx.raw.unsetTrailing⟩
    let comment := comment.map (⟨·.raw.unsetTrailing⟩)
    let stx ← `(command|#create_deprecated_module $fnameStx:str $[$comment:str]? write)
    liftTermElabM do Meta.liftMetaM do
      Meta.Tactic.TryThis.addSuggestion tk
        { preInfo? := "Confirm that you are happy with the information below before continuing!\n\n"
          suggestion := stx
          postInfo? :=
            if comment.isNone
            then "\nYou can add a reason for the removal after the file name, as a string."
            else ""}
  logInfoAt tk <| .joinSep msgs.toList "\n"

/--
`#find_deleted_files (nc)?` takes an optional natural number input `nc`.

Using `#find_deleted_files 5`
It looks at the `lean` files in `Mathlib` that existed `4` commits ago
(i.e. the commit that you see with `git log -5`) and that are no longer present.
It then proposes `Try these:` suggestions calling the `#create_deprecated_module`
to finalize the deprecation.

Unlike what usually happens with `Try these:`, the original `#find_deleted_files` does not get
replaced by the suggestion, which means that you can click on multiple suggestions and proceed with
the deprecations later on.

If the number of commits is not explicitly used, `#find_deleted_files` defaults to `2`,
namely, the commit just prior to the current one.
-/
elab tk:"#find_deleted_files" nc:(ppSpace num)? : command => do
  let n := nc.getD (Syntax.mkNumLit "2") |>.getNat
  let mut msgs : Array MessageData := #[]
  -- Get the hash and the commit message of the commit at `git log -n`
  -- (and throw an error if that doesn't exist).
  let getHashAndMessage (n : Nat) : CommandElabM (String × MessageData) := do
    let log ← IO.Process.run {cmd := "git", args := #["log", "--pretty=oneline", s!"-{n}"]}
    let some last := log.trim.splitOn "\n" |>.getLast? | throwError "Found no commits!"
    let commitHash := last.takeWhile (!·.isWhitespace)
    let PRdescr := (last.drop commitHash.length).trim
    return (commitHash, .trace {cls := `Commit} m!"{PRdescr}" #[m!"{commitHash}"])
  let getFilesAtHash (hash : String) := do
    let files ← IO.Process.run
      {cmd := "git", args := #["ls-tree", "-r", "--name-only", hash, "Mathlib/"]}
    let h : Std.HashSet String := .ofList <| files.splitOn "\n"
    return h
  let (currentHash, currentPRdescr) ← getHashAndMessage 1
  let currentFiles ← getFilesAtHash currentHash
  msgs := msgs.push m!"{currentFiles.size} files at the current commit {currentPRdescr}"
  let (pastHash, pastPRdescr) ← getHashAndMessage n
  let pastFiles ← getFilesAtHash pastHash
  msgs := msgs.push m!"{pastFiles.size} files at the past commit {pastPRdescr}"
  let onlyPastFiles := pastFiles.filter fun fil ↦ fil.endsWith ".lean" && !currentFiles.contains fil
  let noFiles := onlyPastFiles.size
  msgs := msgs.push
    m!"{noFiles} Lean file{if noFiles == 1 then "" else "s"} in 'Mathlib' that no longer exist:"
  msgs := msgs.push "" ++ onlyPastFiles.toArray.map (m!"  {·}") |>.push ""
  if onlyPastFiles.isEmpty then
    logWarningAt (nc.getD ⟨tk⟩)
      m!"All Lean files in Mathlib that existed {n} commits ago are still present.  \
      Increase {n} to search further back!"
    return
  let mut suggestions : Array Meta.Tactic.TryThis.Suggestion := #[]
  let ref := .ofRange {tk.getRange?.get! with stop := tk.getPos?.get!}
  for fname in onlyPastFiles do
    let fnameStx := Syntax.mkStrLit fname
    let stx ← `(command|#create_deprecated_module $fnameStx)
    suggestions := suggestions.push {
            suggestion := (⟨stx.raw.updateTrailing "hello".toSubstring⟩ : TSyntax `command)
            }
  liftTermElabM do Meta.liftMetaM do
    Meta.Tactic.TryThis.addSuggestions (origSpan? := some ref) (header := "Try these:\n\n\
          Clicking on the suggestions below will *not* remove the \
          `#find_delete_files` command, so you can click several of them.\n") tk suggestions
  logInfoAt tk <| .joinSep msgs.toList "\n"

/-!
If you already know the name of the file that you want to deprecate, then uncomment the
`#create_deprecated_module` line below to get started, writing the file path as a string.
* omitting `"a comment here"` is equivalent to using `"Auto-generated deprecation"`
  while using the empty string `""` eliminates the comment entirely;
* uncomment `write` only when you are satisfied that the deprecations look correct!
  The command will also suggested this as a `Try this`.
-/
--#create_deprecated_module "Mathlib/LinearAlgebra/RootSystem/Finite/g2.lean"  "a comment here" --write

/-!
If, instead, you are looking for a file to be deprecated, uncomment the
`#find_deleted_files 10` line below to start scanning.

You can play around with `10`: it represents the number of past commits that the command considers
to find files that existed then and do not exist now.
The exact value is not important: we are just looking for a file name.
Once you found what you were looking for, click on all the relevant `Try these:` suggestions
and continue following the instructions on these commands.

Unlike what usually happens with `Try these:`, the original `#find_deleted_files` does not get
replaced by the suggestion, which means that you can click on multiple suggestions and proceed with
the deprecations later on.
-/
--#find_deleted_files 10

/--
info: /-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

--import Mathlib.Init
import Mathlib.Tactic.Linter.DeprecatedModule
import Std.Time.Zoned
import Lean.Meta.Tactic.TryThis
-/
#guard_msgs in
run_cmd
  let fname ← getFileName
  let head ← getHeader fname (← getFileMap).source false
  logInfo head

/--
info: /-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

--import Mathlib.Init
import Mathlib.Tactic.Linter.DeprecatedModule
import Std.Time.Zoned
import Lean.Meta.Tactic.TryThis
-- a comment here to test `keepTrailing
-/
#guard_msgs in
run_cmd
  let fname ← getFileName
  let head ← getHeader fname (← getFileMap).source true
  logInfo head
