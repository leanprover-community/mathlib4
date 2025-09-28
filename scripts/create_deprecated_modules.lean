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
This file interacts with `git ...` quite a bit. `runCmd` takes as input the command-line
function `git ...` and returns its stdout string as its output.
(Technically, the command need not be `git`: it can be any command we need.
We only use this for `git`, though.)

This is convenient to get both the output of the function, but also for reproducing the exact
command-line text that produced the output for better reproducibility and error reporting.

*Warning*. Splitting of the input string happens at *every* space. This means that if you
pass `"git commit -m 'message with spaces'`, the command will be split into
`["git", "commit", "-m", "'message", "with", "spaces'"]`, which is not what you want.
-/
def runCmd (s : String) : IO String := do
  let cmd::args := s.splitOn | EStateM.throw "Please provide at least one word in your command!"
  IO.Process.run {cmd := cmd, args := args.toArray}

/--
`getHeader fname fileContent keepTrailing` takes as input two strings and a `Bool`ean.
It uses
* `fname`, as the path of a file (which need not exist);
* `fileContent`, as the content of `fname` (regardless of whether the file exists and what its
  content is);
* `keepTrailing` a boolean to control whether to keep trailing comments.

It returns just the imports of `fileContent`, including trailing comments if `keepTrailing = true`
(the command always trims trailing whitespace after the last comment).
-/
def getHeader (fname fileContent : String) (keepTrailing : Bool) : IO String := do
  let (stx, _) ← Parser.parseHeader (Parser.mkInputContext fileContent fname)
  let stx := if keepTrailing then stx.raw else stx.raw.unsetTrailing
  let some substring := stx.getSubstring? | throw <| .userError "No substring: we have a problem!"
  return substring.toString

/--
`getHeaderFromFileName fname keepTrailing` is similar to `getHeader`, except that it assumes that
`fname` is the actual path of a file, and uses `fname`'s content as input to `getHeader`.
-/
def getHeaderFromFileName (fname : String) (keepTrailing : Bool) : IO String := do
  getHeader fname (← IO.FS.readFile fname) keepTrailing

/--
`mkDeprecationWithDate date customMessage` returns the formatted syntax
`deprecated_module "customMessage" (since := "date")`,
where the date is of the form `YYYY-MM-DD`.
-/
def mkDeprecationWithDate (date : String)
    (customMessage : Option String := some "Auto-generated deprecation") :
    CommandElabM Format := do
  let msgStx := customMessage.map Syntax.mkStrLit
  let dateStx := Syntax.mkStrLit date
  let stx ← `(command|deprecated_module $[$msgStx]? (since := $dateStx))
  liftCoreM <| PrettyPrinter.ppCategory `command stx

/--
`mkDeprecation customMessage` returns the formatted syntax
`deprecated_module "customMessage" (since := "YYYY-MM-DD")`, where the date is today's date.
-/
def mkDeprecation (customMessage : Option String := some "Auto-generated deprecation") :
    CommandElabM Format := do
  -- Get the current date in UTC: we don't want this to depend on the user computer's time zone.
  let date := s!"{(← Std.Time.DateTime.now (tz := .UTC)).toPlainDate}"
  mkDeprecationWithDate date customMessage

/--
The command `#create_deprecated_module filePath (<comment>)? (rename_to <fname>) (write)?`
generates a module deprecation.

Writing
```lean
#create_deprecated_module path/To/DeletedFile.lean "This file is no longer relevant" rename_to "Mathlib/Path/To/Rename.lean"
```
checks that `path/To/DeletedFile.lean` is not currently present, but was present in `Mathlib/`
at some point.

If the check is successful, then it reports on its findings, shows how the corresponding
deprecated module should look like, using `"This file is no longer relevant"` as the (optional)
<comment>.

If the message is not explicitly used, `#create_deprecated_module` defaults to
`"Auto-generated deprecation"`.
If you wish there to be no comment, use `#create_deprecated_module path/To/DeletedFile.lean ""`.

If `rename_to "Mathlib/Path/To/Rename.lean"` is present, then instead of copying over the imports
from a deleted file, it uses `import Mathlib.Path.To.Rename`.

Finally, if everything looks correct, adding a final `write` actually generates the file:
```lean
#create_deprecated_module path/To/DeletedFile.lean "This file is no longer relevant" write
```
-/
syntax "#create_deprecated_module " str (ppSpace str)? (&" rename_to " str)? (&" write")? ppLine :
  command

/-- `processPrettyOneLine log msg` takes as input two strings `log` and `msg`.
It expects `log` to be a line in the output of `git log --pretty=oneline`:
it should look like `<hash> <PRdescr>`.

It returns the pair `(<hash>, <msg> in <PRdescr> <hash> <diff of file wrt previous commit>)`,
formatted as a collapsible message. In practice, `msg` is either `last modified` or `deleted`.
it returns the pair `(<hash>, <msg> in <PRdescr> <hash> <diff of file wrt previous commit>)`,
formatted as a collapsible message.
-/
def processPrettyOneLine (log msg fname : String) : IO (String × MessageData) := do
  let hash := log.takeWhile (!·.isWhitespace)
  let PRdescr := (log.drop hash.length).trim
  let gitDiffCLI := s!"git diff {hash}^...{hash} -- {fname}"
  let diff ← runCmd gitDiffCLI <|> pure s!"{hash}: error in computing '{gitDiffCLI}'"
  let diffCollapsed := .trace {cls := .str .anonymous s!"{hash}"} m!"{gitDiffCLI}" #[m!"{diff}"]
  return (hash, m!"{msg} in " ++
    .trace {cls := .str .anonymous ("_" ++ hash.take 7)} m!"{PRdescr}" #[diffCollapsed])

/--
`mkRenamesDict pct` takes as optional input a natural number.

It computes the `git` status of the files at the current `HEAD` commit,
comparing them with `master`.

It returns a `HashMap` with keys the old names and values the new names of all the files that
git considers renames with likelihood at least the input `percent`.

If no input is provided, the default percentage is `100`.
-/
def mkRenamesDict (percent : Nat := 100) : IO (Std.HashMap String String) := do
  let mut dict := ∅
  let gitDiff ← runCmd s!"git diff --name-status origin/master...HEAD"
  let lines := gitDiff.trim.splitOn "\n"
  for git in lines do
    -- If `git` corresponds to a rename, it contains `3` segments, separated by a
    -- tab character (`\t`): `R%%`, `oldName`, `newName`.
    let [pct, oldName, newName] := git.split (· == '\t') | continue
    if pct.take 1 != "R" then
      IO.println
        s!"mkRenamesDict: '{pct}' should have been of the form Rxxx, denoting a `R`ename \
          and a similarity percentage.\nFull git line: '{git}'"
      continue
    let some pctNat := (pct.drop 1).toNat? | continue
    -- This looks like a rename with a similarity index at least as big as our threshold:
    -- we add the rename to our dictionary.
    if percent ≤ pctNat then
      dict := dict.insert oldName newName
    -- This looks like a rename, but the similarity index is smaller than our threshold:
    -- we report a message and do not add the rename to our dictionary.
    else
      IO.println
        s!"'{oldName}' was renamed to '{newName}' ({pct}), but the similarity {pctNat}% \
          is less than the expected threshold of {percent}%.\n\n
          We treat this file as a removal."
  return dict

/--
`mkModName fname` takes as input a file path and returns the guessed module name:
the dir-separators get converted to `.` and a trailing `.lean` gets removed, if it exists.

*Note*. The input path is relative to the root of the project.  E.g., within `mathlib`, every path
effectively starts as `Mathlib/...`.
-/
def mkModName (fname : System.FilePath) : String :=
  let cpts := fname.components
  let cpts :=
    match cpts.getLast? with
    | none => cpts
    | some last =>
      cpts.dropLast ++ [if last.endsWith ".lean" then last.dropRight ".lean".length else last]
  ".".intercalate cpts

#guard mkModName ("Mathlib" / "Data" / "Nat" / "Basic.lean") == "Mathlib.Data.Nat.Basic"
#guard mkModName "" == ""
#guard mkModName ("" / "") == "."

/--
`deprecateFilePath fname rename comment` takes as input
* the path `fname` of a file that was deleted;
* an optional module name `rename`, in case the file was renamed, rather than removed;
* an optional comment to add in the `deprecated module` syntax.

It returns a pair consisting of
* an array of `MessageData` giving details about the last time that `fname` was modified
  and when it was deleted;
* if `rename = some preRenamedModule`, then a suggestion to create a file with `import newName`
  in the regenerated module `preRenamedModule`; otherwise
  the content of the deprecated file, matching the original `fname` up to the last import command.
  In both cases, after the imports, there will be the `deprecated_module` command with the optional
  `comment` input, defaulting to `Auto-generated deprecation` if `comment = none`.
-/
def deprecateFilePath (fname : String) (rename comment : Option String) :
    CommandElabM (Array MessageData × String) := do
  let mut msgs : Array MessageData := #[]
  -- Check that the input `fname` is a file that currently does not exist.
  if ← System.FilePath.pathExists fname then
    throwError m!"The file {fname} exists: I cannot deprecate it!"
  -- Retrieve the last two commits that modified `fname`:
  -- the last one is the deletion, the previous one is the last file modification.
  let log ← runCmd s!"git log --pretty=oneline -2 -- {fname}"
  let [deleted, lastModified] := log.trim.splitOn "\n" |
    throwError "Found {(log.trim.splitOn "\n").length} commits, but expected 2! \
      Please make sure the file {fname} existed at some point!"
  let (_deleteHash, deletedMsg) ← processPrettyOneLine deleted "deleted" fname
  let (modifiedHash, modifiedMsg) ← processPrettyOneLine lastModified "last modified" fname
  msgs := msgs.append #[m!"The file {fname} was\n", modifiedMsg, deletedMsg]
  -- Get the commit date, in `YYYY-MM-DD` format, of the commit deleting the file.
  let log' ← runCmd s!"git log --format=%cs -2 -- {fname}"
  let deletionDate := (log'.trim.splitOn "\n")[0]!
  let deprecation ← mkDeprecationWithDate deletionDate comment
  msgs := msgs.push ""
  -- Retrieve the final version of the file, before it was deleted.
  let file ← runCmd s!"git show {modifiedHash}:{fname}"
  -- Generate a module deprecation for the file `fname`.
  let fileHeader := ← match rename with
    | some rename => do
      let modName := mkModName rename
      pure s!"import {modName}"
    | none => getHeader fname file false
  let deprecatedFile := s!"{fileHeader.trimRight}\n\n{deprecation.pretty.trimRight}\n"
  msgs := msgs.push <| .trace {cls := `Deprecation} m!"{fname}" #[m!"\n{deprecatedFile}"]
  return (msgs, deprecatedFile)

elab_rules : command
| `(#create_deprecated_module%$tk $fnameStx:str $[$comment:str]? $[rename_to $rename?:str]? $[write%$write?]?) => do
  let fname := fnameStx.getString
  if ← System.FilePath.pathExists fname then
    logWarningAt fnameStx m!"The file {fname} exists: I cannot deprecate it!"
    return
  let (msgs, deprecatedFile) ← deprecateFilePath fname (rename?.map (·.getString)) (comment.map (·.getString))
  if write?.isSome then
    if let some dir := System.FilePath.parent fname then
      if !(← System.FilePath.pathExists dir) then
        logInfoAt fnameStx m!"Creating directory {dir}"
        IO.FS.createDirAll dir
    IO.FS.writeFile fname deprecatedFile
  if write?.isNone then
    -- We strip trailing comments from `fnameStx` and `comment` to avoid them showing up in the
    -- regenerated syntax.
    let fnameStx := ⟨fnameStx.raw.unsetTrailing⟩
    let comment := comment.map (⟨·.raw.unsetTrailing⟩)
    let stx ← `(command|#create_deprecated_module $fnameStx:str $[$comment:str]? $[rename_to $rename?:str]? write)
    liftTermElabM do Meta.liftMetaM do
      Meta.Tactic.TryThis.addSuggestion (← getRef).unsetTrailing
        { preInfo? := "Confirm that you are happy with the information below before continuing!\n\n"
          suggestion := stx
          postInfo? :=
            if comment.isNone
            then "\nYou can add a reason for the removal after the file name, as a string."
            else ""}
  logInfoAt tk <| .joinSep msgs.toList "\n"

/--
`#find_deleted_files (nc)? (pct%)?` takes an optional natural number input `nc` and an optional
percentage `pct%`.

Using `#find_deleted_files 5 80%`
It looks at the `lean` files in `Mathlib` that existed `4` commits ago
(i.e. the commit that you see with `git log -5`) and that are no longer present.
It then proposes `Try these:` suggestions calling the `#create_deprecated_module`
to finalize the deprecation.

The percentage `pct` is used to detect renames: if a file was renamed with similarity
at least `pct`, then the `#create_deprecated_module` suggestion will use the new name
in the `import` command, rather than copying over the imports from the deleted file.

Unlike what usually happens with `Try these:`, the original `#find_deleted_files` does not get
replaced by the suggestion, which means that you can click on multiple suggestions and proceed with
the deprecations later on.

If the number of commits is not explicitly given, `#find_deleted_files` defaults to `2`,
namely, the commit just prior to the current one.
-/
elab tk:"#find_deleted_files" nc:(ppSpace num)? pct:(ppSpace num)? bang:&"%"? : command => do
  if pct.isSome && bang.isNone then
    throwError m!"Please add a '%' after the percentage {pct.getD default}"
  let n := nc.getD (Syntax.mkNumLit "2") |>.getNat
  if n == 0 then
    logWarningAt (nc.getD default) "The number of commits to look back must be at least 1!"
    return
  let mut msgs : Array MessageData := #[]
  -- Get the hash and the commit message of the commit at `git log -n`
  -- and format the message (with its hash) as a collapsible message.
  -- (throwing an error if that doesn't exist).
  let getHashAndMessage (n : Nat) : CommandElabM (String × MessageData) := do
    let log ← runCmd s!"git log --pretty=oneline -{n}"
    let some last := log.trim.splitOn "\n" |>.getLast? | throwError "Found no commits!"
    let commitHash := last.takeWhile (!·.isWhitespace)
    let PRdescr := (last.drop commitHash.length).trim
    return (commitHash, .trace {cls := `Commit} m!"{PRdescr}" #[m!"{commitHash}"])
  let getFilesAtHash (hash : String) : CommandElabM (Std.HashSet String) := do
    let files ← runCmd s!"git ls-tree -r --name-only {hash} Mathlib/"
    return .ofList <| files.splitOn "\n"
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
  let dict ← mkRenamesDict (pct.getD (Syntax.mkNumLit "100")).getNat
  for fname in onlyPastFiles do
    let fnameStx := Syntax.mkStrLit fname
    let stx ← if let some newName := dict[fname]? then
                let newNameStx := Syntax.mkStrLit newName
                `(command|#create_deprecated_module $fnameStx rename_to $newNameStx)
              else
                `(command|#create_deprecated_module $fnameStx)
    suggestions := suggestions.push {
      suggestion := (⟨stx.raw.updateTrailing "hello".toSubstring⟩ : TSyntax `command)
    }
  let suggestionsText :=
    if suggestions.size == 1 then ("the suggestion", "")
    else (s!"any of the {suggestions.size} suggestions", ", so you can click several of them")
  liftTermElabM do Meta.liftMetaM do
    Meta.Tactic.TryThis.addSuggestions (origSpan? := some ref) (header := s!"Try these:\n\n\
          Clicking on {suggestionsText.1} below will *not* remove the \
          `#find_delete_files` command{suggestionsText.2}.\n") tk suggestions
  logInfoAt tk <| .joinSep msgs.toList "\n"

/-!
If you already know the name of the file that you want to deprecate, then uncomment the
`#create_deprecated_module` line below to get started, writing the file path as a string.
* omitting `"a comment here"` is equivalent to using `"Auto-generated deprecation"`
  while using the empty string `""` eliminates the comment entirely;
* uncomment `write` only when you are satisfied that the deprecations look correct!
  The command will also by proposed this as a `Try this` suggestion by the
  `#create_deprecated_module` command.
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

#find_deleted_files 0
/--
info: import Mathlib.Tactic.Linter.DeprecatedModule
import Std.Time.Zoned
import Lean.Meta.Tactic.TryThis
-/
#guard_msgs in
run_cmd
  let fname ← getFileName
  let head ← getHeader fname (← getFileMap).source false
  logInfo head

/--
info: import Mathlib.Tactic.Linter.DeprecatedModule
import Std.Time.Zoned
import Lean.Meta.Tactic.TryThis
-- a comment here to test `keepTrailing
-/
#guard_msgs in
run_cmd
  let fname ← getFileName
  let head ← getHeader fname (← getFileMap).source true
  logInfo head
