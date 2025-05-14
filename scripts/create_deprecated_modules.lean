/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

--import Mathlib.Init
import Mathlib.Tactic.Linter.DeprecatedModule
import Std.Time.Zoned
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
`mkDeprecation customMessage` returns the formatted syntax
`deprecated_module "customMessage" (since := "YYYY-MM-DD")`,
where the date is today's date.
-/
def mkDeprecation (customMessage : String := "Auto-generated deprecation") :
    CommandElabM Format := do
  let msgStx := if customMessage.isEmpty then none else some <| Syntax.mkStrLit customMessage
  -- Get the current date in UTC: we don't want this to depend on the user computer's time zone.
  let dateStx := Syntax.mkStrLit s!"{(← Std.Time.DateTime.now (tz := .UTC)).toPlainDate}"
  let stx ← `(command|deprecated_module $[$msgStx]? (since := $dateStx))
  liftCoreM <| PrettyPrinter.ppCategory `command stx

/--
The command `#create_deprecated_modules (n)? (comment)? (write)?` generates module deprecations.

Writing
```lean
#create_deprecated_modules 5 "These files are no longer relevant"
```
looks at the `lean` files in `Mathlib` that existed `4` commits ago
(i.e. the commit that you see with `git log -5`) and that are no longer present.
It shows how the corresponding deprecated modules should look like, using
`"These files are no longer relevant"` as the (optional) comment.

If the number of commits is not explicitly used, `#create_deprecated_modules` defaults to `2`,
namely, the commit just prior to the current one.

If the message is not explicitly used, `#create_deprecated_modules` defaults to
`"Auto-generated deprecation"`.
If you wish there to be no comment, use `#create_deprecated_modules 5 ""`.

Note that the command applies the *same* comment to all the files that it generates.

Finally, if everything looks correct, adding a final `write` actually generates the files:
```lean
#create_deprecated_modules 5 "These files are no longer relevant" write
```
-/
syntax "#create_deprecated_modules" (ppSpace num)? (ppSpace str)? (&" write")? : command

elab_rules : command
| `(#create_deprecated_modules%$tk $[$nc:num]? $[$comment:str]? $[write%$write?]?) => do
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
    m!"{noFiles} Lean file{if noFiles == 1 then "" else "s"} in 'Mathlib' that no longer exist."
  let deprecation ← if let some cmt := comment then mkDeprecation cmt.getString else mkDeprecation
  msgs := msgs.push ""
  -- Generate a module deprecation for each file that only existed in the past commit.
  for fname in onlyPastFiles do
    let file ← IO.Process.run {cmd := "git", args := #["show", s!"{pastHash}:{fname}"]}
    let fileHeader ← getHeader fname file false
    let deprecatedFile := s!"{fileHeader.trimRight}\n\n{deprecation.pretty.trimRight}\n"
    msgs := msgs.push <| .trace {cls := `Deprecation} m!"{fname}" #[m!"\n{deprecatedFile}"]
    if write?.isSome then
      IO.FS.writeFile fname deprecatedFile
  if write?.isNone && noFiles != 0 then
    -- We strip trailing comments from `nc` and `comment` to avoid them showing up in the
    -- regenerated syntax.
    let nc := nc.map (⟨·.raw.unsetTrailing⟩)
    let comment := comment.map (⟨·.raw.unsetTrailing⟩)
    let stx ← `(command|#create_deprecated_modules $[$nc:num]? $[$comment:str]? write)
    msgs := msgs.push
      m!"The files were not deprecated. Use '{stx}' if you wish to deprecate them."
  logInfoAt tk <| .joinSep msgs.toList "\n"

/-
Uncomment the `#create_deprecated_modules` line below to get started.
* `10` should likely be some small number, though its exact value may not be too important;
* omitting `"a comment here"` is equivalent to using `"Auto-generated deprecation"`
  while using the empty string `""` eliminates the comment entirely;
* uncomment `write` only when you are satisfied that the deprecations look correct!
-/
--#create_deprecated_modules 10 "a comment here" --write

/--
info: /-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

--import Mathlib.Init
import Mathlib.Tactic.Linter.DeprecatedModule
import Std.Time.Zoned
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
-- a comment here to test `keepTrailing
-/
#guard_msgs in
run_cmd
  let fname ← getFileName
  let head ← getHeader fname (← getFileMap).source true
  logInfo head
